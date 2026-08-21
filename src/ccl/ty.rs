//! The CCL [`Type`] lattice, its [`Refinement`] subset-type carrier, and the
//! type-blind structural equality / hashing on refinement predicate terms.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use smol_str::SmolStr;

use crate::ccl::{BaseType, InferVar, Lit, ProjKey, TypedExpr, TypedExprNode, ccl_utils, symbolic};

/// The introduction level riding a [`Type::ChanDom`] — deliberately
/// **identity-transparent**: two channel domains denote the same channel iff
/// their *names* match. The level is bookkeeping for `freshen_above`'s
/// quantification decision only, and one name is legitimately observed at
/// different levels (a pass-1 `At(use)` instantiation and a pass-2 `Preserve`
/// clone rename of the same logical instantiation). Comparing or hashing it
/// would split one channel into two atoms — every `PartialEq`/`Ord`/`Hash`
/// here says "equal".
#[derive(Debug, Clone, Copy)]
pub struct ChanLevel(pub crate::ccl::Level);

impl PartialEq for ChanLevel {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ChanLevel {}
impl PartialOrd for ChanLevel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ChanLevel {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl std::hash::Hash for ChanLevel {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

/// Identifies a field inside a structural record/tuple, or a variant tag.
///
/// `Index` is used for tuple-shaped records (positional projection);
/// `Name` for named-field records. The `constrain_subtype` solver treats them
/// uniformly under width-subtyping; the closed-tuple-vs-record
/// distinction is materialized only at coalesce time.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldKey {
    /// Positional field (tuple index).
    Index(usize),
    /// Named field.
    Name(SmolStr),
}

impl fmt::Display for FieldKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Positional keys render as a bare index, matching tuple/record
            // projection (`.0`, `.1`); the dot prefix in tag/field contexts
            // is supplied by the caller, so a positional sum reads `.0`, `.1`.
            FieldKey::Index(n) => write!(f, "{n}"),
            FieldKey::Name(s) => write!(f, "{s}"),
        }
    }
}

/// A set of [`FieldKey`]-keyed arms in canonical (key) order.
///
/// The carrier for the arms of a tagged sum wherever one is represented: the
/// per-variant extents of a union, its per-variant predicates, and the payload
/// columns of a union value. Those three have to agree about *which* arm is
/// which, and keying them all on the tag is what makes that agreement structural
/// rather than an ordering convention each site restates.
///
/// **Why keyed rather than positional.** A tag's position within a sum is
/// relative to that sum's own key set, so it is *not* stable under width
/// subtyping: `[b] <: [a, b]` is a legal instance of the variant width rule, but
/// `b` sits at position 0 in the subtype and position 1 in the supertype. A
/// positional encoding therefore has to renumber on subsumption — and since a
/// sum's arm set is part of its runtime layout, "renumber" means rebuilding the
/// value. Keying on the tag removes the renumbering entirely: an arm is found by
/// name, and a key the map does not carry is simply absent, which is exactly what
/// width subtyping means (that arm cannot occur).
///
/// **Canonical order is still maintained**, because the arms of a sum are also
/// consumed positionally in places where that positional identity is load-bearing
/// (per-variant release pairs a predicate arm with its source sub-extent). Sorted
/// order makes structural equality agree with key-set equality and keeps the
/// pairing well-defined; it just no longer decides *identity*.
///
/// [`FieldKey::Index`] keys make an anonymous positional sum (`a ++ b`, and the
/// domain of the union-of-restricts fan-out) the degenerate case of the same
/// structure, so named and positional sums share one representation — mirroring
/// [`Type::Variant`], which already keys on [`FieldKey`] for both.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TagMap<T>(Vec<(FieldKey, T)>);

impl<T> TagMap<T> {
    /// An empty map — a sum with no arms.
    pub fn new() -> Self {
        TagMap(Vec::new())
    }

    /// Build an **anonymous positional sum**: arm `i` keyed [`FieldKey::Index`]`(i)`.
    ///
    /// The `a ++ b` / union-of-restricts case, where a tag *is* its position, so
    /// this is the one place a positional vector legitimately becomes a `TagMap`.
    /// `Index` keys sort numerically, so the canonical order matches the input.
    pub fn from_positional(arms: Vec<T>) -> Self {
        TagMap(
            arms.into_iter()
                .enumerate()
                .map(|(i, v)| (FieldKey::Index(i), v))
                .collect(),
        )
    }

    /// The arms in canonical order, dropping their tags.
    pub fn into_values(self) -> Vec<T> {
        self.0.into_iter().map(|(_, v)| v).collect()
    }

    /// Build from arms in any order, sorting into canonical order.
    ///
    /// # Panics
    /// In debug builds, if a key repeats — an arm set with a duplicate tag has no
    /// meaning (which of the two would a value with that tag belong to?).
    pub fn from_arms(mut arms: Vec<(FieldKey, T)>) -> Self {
        arms.sort_by(|(a, _), (b, _)| a.cmp(b));
        debug_assert!(
            arms.windows(2).all(|w| w[0].0 != w[1].0),
            "TagMap: duplicate tag in arm set"
        );
        TagMap(arms)
    }

    /// The arm for `key`, or `None` when this sum carries no such arm.
    ///
    /// `None` is the width-subtyping case and is not an error: a producer of
    /// fewer tags is a subtype, so a consumer asking for a tag it handles but the
    /// producer never emits gets nothing, which is correct.
    pub fn get(&self, key: &FieldKey) -> Option<&T> {
        self.position(key).map(|i| &self.0[i].1)
    }

    /// Mutable access to the arm for `key`.
    pub fn get_mut(&mut self, key: &FieldKey) -> Option<&mut T> {
        self.position(key).map(|i| &mut self.0[i].1)
    }

    /// The arm for `key`, inserting `default()` first if this sum lacks it.
    ///
    /// The "widen by one tag" operation: merging two sums keyed on different tag
    /// sets grows the result to their union, so a missing arm is created rather
    /// than being an error.
    pub fn get_or_insert_with(&mut self, key: FieldKey, default: impl FnOnce() -> T) -> &mut T {
        let i = match self.0.binary_search_by(|(k, _)| k.cmp(&key)) {
            Ok(i) => i,
            Err(i) => {
                self.0.insert(i, (key, default()));
                i
            }
        };
        &mut self.0[i].1
    }

    /// The canonical position of `key`'s arm.
    ///
    /// Positions are only meaningful *within this map*; never compare one against
    /// a position taken from a different sum (that is the renumbering hazard the
    /// keying exists to remove).
    pub fn position(&self, key: &FieldKey) -> Option<usize> {
        self.0.binary_search_by(|(k, _)| k.cmp(key)).ok()
    }

    /// Number of arms.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether this sum has no arms.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Arms in canonical order.
    pub fn iter(&self) -> impl Iterator<Item = (&FieldKey, &T)> {
        self.0.iter().map(|(k, v)| (k, v))
    }

    /// Mutable arms in canonical order.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&FieldKey, &mut T)> {
        self.0.iter_mut().map(|(k, v)| (&*k, v))
    }

    /// The tags, in canonical order.
    pub fn keys(&self) -> impl Iterator<Item = &FieldKey> {
        self.0.iter().map(|(k, _)| k)
    }

    /// The arms, in canonical order.
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.0.iter().map(|(_, v)| v)
    }

    /// Whether both sums carry exactly the same tags.
    pub fn same_tags<U>(&self, other: &TagMap<U>) -> bool {
        self.len() == other.len() && self.keys().eq(other.keys())
    }

    /// Rebuild with each arm mapped, preserving tags (and so canonical order).
    pub fn map<U>(&self, mut f: impl FnMut(&FieldKey, &T) -> U) -> TagMap<U> {
        TagMap(self.0.iter().map(|(k, v)| (k.clone(), f(k, v))).collect())
    }

    /// Pair arms by tag with `other`, visiting only tags both carry.
    ///
    /// The tag-keyed replacement for zipping two arm vectors positionally: it
    /// cannot silently mispair when the two sums carry different tag sets.
    pub fn zip_matching<'a, U>(
        &'a self,
        other: &'a TagMap<U>,
    ) -> impl Iterator<Item = (&'a FieldKey, &'a T, &'a U)> {
        self.iter()
            .filter_map(move |(k, v)| other.get(k).map(|u| (k, v, u)))
    }

    /// Combine arm-wise with `other`, which must carry the **same** tags.
    ///
    /// The *total* counterpart of [`zip_matching`](Self::zip_matching): where that
    /// one visits the intersection and is happy to skip, this lifts a binary
    /// operation pointwise over a fixed arm set, so every tag must be present on
    /// both sides for the result to be defined at every tag. Differing tag sets are
    /// a caller bug rather than a case to absorb — the two sums would be describing
    /// different value spaces, and there is no arm to combine with.
    ///
    /// This is why a *query* over two sums ([`same_tags`](Self::same_tags) plus a
    /// conservative answer, as `Predicate::subsumes` does) and a *combination* of
    /// two sums are guarded differently: a query can answer "no" when the arm sets
    /// disagree, and a combination has no such fallback to give.
    ///
    /// # Panics
    /// If the two sums do not carry the same tags. `op` names the caller for the
    /// message.
    pub fn zip_same_tags<U, V>(
        &self,
        other: &TagMap<U>,
        op: &str,
        mut f: impl FnMut(&T, &U) -> V,
    ) -> TagMap<V> {
        assert!(
            self.same_tags(other),
            "{op}: arm sets differ ({:?} vs {:?}); a pointwise combination of two \
             sums is defined only over one arm set",
            self.keys().collect::<Vec<_>>(),
            other.keys().collect::<Vec<_>>()
        );
        TagMap(
            self.zip_matching(other)
                .map(|(k, v, u)| (k.clone(), f(v, u)))
                .collect(),
        )
    }
}

impl<T> Default for TagMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> FromIterator<(FieldKey, T)> for TagMap<T> {
    fn from_iter<I: IntoIterator<Item = (FieldKey, T)>>(iter: I) -> Self {
        Self::from_arms(iter.into_iter().collect())
    }
}

impl<T> IntoIterator for TagMap<T> {
    type Item = (FieldKey, T);
    type IntoIter = std::vec::IntoIter<(FieldKey, T)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Whether a [`Type::Variant`]'s listed arms are the **whole** arm set, or only the
/// part the type commits to.
///
/// A record needs no such distinction, because record width subtyping already gives
/// it: a producer with *extra* fields is a *subtype*, so demanding
/// `producer <: Record({core})` pins the core and lets the extras through
/// (`design/lowering.md` calls this the open-record pattern). For a sum the
/// subtyping runs the other way — fewer tags is the subtype — so a producer with
/// extra tags is a **supertype**, and no closed judgment can both allow those extras
/// and still say anything about the arms it *does* share.
///
/// That is exactly what a `match` with a `case _:` needs. Its arms describe a
/// consumer, so each arm's payload binder has to receive the scrutinee's payload at
/// that tag (an edge *into* the binder), while the scrutinee stays free to carry tags
/// no arm names (no constraint on the tag *set*). On the tag axis the scrutinee is
/// the supertype; on the payload axis its payload sits *below* the binder. One
/// closed subtyping judgment cannot point both ways, so the arm set is marked
/// [`Open`](Self::Open) and the width rule skips the missing-tag rejection while
/// keeping the per-tag recursion.
///
/// **Openness is a property of a demand, never of a value.** Every *producer* of a
/// sum — a constructor, an annotation, anything a value flows out of — is
/// [`Closed`](Self::Closed): it knows its own tags. Only a consumer's expectation is
/// open, so `Open` appears on the right of a subtyping edge and nowhere else.
///
/// It survives compaction and coalescing (`CompactVariant` carries it) rather than
/// being flattened there, because a **diagnostic** naming a demand goes through that
/// same round-trip: a report closing the arm set would say the scrutinee failed to
/// *be* that sum, where what it failed was to be a subtype of a partial one. The
/// rendering keeps the two apart with a trailing `| …`.
///
/// Nothing else reads it. [`Extent`](crate::interpreter::Extent) has no counterpart,
/// and no AST node's coalesced type comes out open — a demand is what a consumer
/// requires, not what any expression *is*. That is an invariant rather than a
/// theorem, so it is watched instead of assumed: `types_agree_modulo_unread`
/// compares openness, and an `Open` that escaped onto a node surfaces there as a
/// disagreement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Openness {
    /// These arms and no others. The default, and what every sum *value* has.
    #[default]
    Closed,
    /// These arms, and possibly more this type says nothing about.
    ///
    /// Only ever demanded, never produced. A subtype may carry tags absent from an
    /// open arm set; the shared arms still constrain pointwise.
    Open,
}

impl Openness {
    /// Whether a subtype may carry tags this arm set does not list.
    pub fn permits_extra_tags(self) -> bool {
        matches!(self, Openness::Open)
    }
}

/// Whether a [`Type::Fun`]'s domain is a **capability** or a **collection** — the
/// compute-function vs data-function distinction.
///
/// - [`FunKind::Compute`] — `α ⇒ β`: the domain is a *capability*, the inputs
///   the function accepts. No data sits behind it, so shrinking the domain only
///   under-promises; the contravariant meet at a control-flow join is a sound,
///   lossy simplification.
/// - [`FunKind::Data`] — `α ⤇ β`: the domain is a *collection*'s index set. The
///   domain *is* the data map, so a lossy domain is lost data. A join of two data
///   functions therefore may not take the contravariant meet: where their domains
///   differ it is rejected (`CoalesceError::DomainJoinConflict`) rather than
///   silently dropping rows. The lossless join — a dependent sum over the candidate
///   domains — is the collections work; the kind distinction is what makes its
///   absence an error instead of a wrong answer.
///
/// Set at introduction (list literals, comprehensions, `++`, registered
/// sources, and every `History` erasure are `Data`; `lambda`/`def` are
/// `Compute`). The audit rule for a rebuilt or erased function type: it is `Data` iff
/// `extent_of` will drive iteration off its domain. See
/// `design/type-inference.md`, "4.6 Data vs compute functions".
///
/// FunKind is **inferred** (see `design/type-inference.md`, "4.6 Data vs compute
/// functions"):
/// where the structure fixes it (a list literal is `Data`, a scalar op is
/// `Compute`) a concrete kind is stamped; where it depends on use or on an
/// unresolved source (a map/comprehension) a [`FunKind::Var`] is minted and the
/// solver resolves it, like a type variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunKind {
    /// A compute function / capability (`⇒`): lossy meet at a join is fine.
    Compute,
    /// A data function / collection (`⤇`): the domain *is* the data; joins must
    /// be lossless.
    Data,
    /// An unresolved kind, pinned down by the solver at coalesce. Identity is by
    /// the variable's `uid`, so `FunKind` (and `Type`) keep deriving
    /// `PartialEq`/`Eq`/`Hash` — the [`FunKindVar`] impls compare by `uid` only.
    Var(Rc<FunKindVar>),
}

impl FunKind {
    /// The display arrow for this kind: `⇒` for compute, `⤇` for data. An
    /// unresolved variable renders `⇒` (its resolved kind is written back before
    /// display matters downstream).
    pub fn arrow(&self) -> &'static str {
        match self {
            FunKind::Compute | FunKind::Var(_) => "⇒",
            FunKind::Data => "⤇",
        }
    }

    /// A fresh inferred kind (a new [`FunKindVar`] with empty bounds).
    pub fn fresh_var() -> FunKind {
        FunKind::Var(FunKindVar::fresh())
    }
}

/// Stable identity of a [`FunKindVar`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunKindVarId(pub(crate) u32);

static FUN_KIND_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

/// What a [`FunKindVar`] has been pinned to.
///
/// `Data` and `Compute` are **incomparable**, so a kind edge fixes a variable
/// rather than bounding it, and there is nothing to accumulate but which of the
/// two points something pinned it to. An [`crate::ccl::InferVar`] carries polar
/// bound *lists*; this carries one of four states, and since no [`Type`] sits
/// inside, a `FunKindVar` never forms a cycle.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum KindPin {
    /// Nothing pinned this kind. Resolves to the reader's default.
    #[default]
    Unpinned,
    /// Pinned to `Compute`.
    Compute,
    /// Pinned to `Data`.
    Data,
    /// Pinned to both points — one function required to be a collection at one
    /// site and a capability at another. Read at coalesce
    /// ([`crate::ccl::infer::solver::compact::KindMerge::of`]).
    Conflict,
}

/// A kind-inference variable — an unknown [`FunKind`] an elimination mints
/// and the value flowing in pins.
///
/// The two eliminations cannot know a function's kind: applying a value and
/// destructuring a function are one node for a collection and for a capability
/// alike ([`Type::pi_eliminated`], [`Type::fun_eliminated`]). Each mints one of
/// these, and the kind edge pins it to whatever concrete kind the value carries
/// (`constrain_kind`). Nothing else mints one — no scheme is kind-polymorphic and
/// lowering stamps every function type it builds — so a variable is **written by the one
/// value that reaches it**, never solved against other variables: two variables
/// meeting record nothing, because what they resolve to is not known at that edge
/// and no program needs it to be.
///
/// Identity (`uid`) is immutable and lives outside the `RefCell`, so
/// equality/hashing is borrow-free and never inspects the pin (mirroring
/// [`crate::ccl::InferVar`]). [`Rc`] because the same cell has to be visible
/// wherever the type was cloned to.
pub struct FunKindVar {
    /// Stable, globally-unique identity.
    pub uid: FunKindVarId,
    /// Which point this var has been pinned to. Private so that every write goes
    /// through a pin, which is what makes reaching [`KindPin::Conflict`] the only
    /// way to hold two points at once.
    pin: RefCell<KindPin>,
}

impl FunKindVar {
    /// Allocate a fresh kind variable, pinned to nothing.
    pub fn fresh() -> Rc<FunKindVar> {
        Rc::new(FunKindVar {
            uid: FunKindVarId(FUN_KIND_VAR_COUNTER.fetch_add(1, Ordering::Relaxed)),
            pin: RefCell::new(KindPin::Unpinned),
        })
    }

    /// What this variable has been pinned to.
    pub fn pin(&self) -> KindPin {
        *self.pin.borrow()
    }

    /// Pin this kind to `Compute`. Pinning to the point already recorded is
    /// idempotent; pinning to the other one is the conflict, which absorbs.
    pub fn pin_compute(&self) {
        let pin = &mut *self.pin.borrow_mut();
        *pin = match *pin {
            KindPin::Unpinned | KindPin::Compute => KindPin::Compute,
            KindPin::Data | KindPin::Conflict => KindPin::Conflict,
        };
    }

    /// Pin this kind to `Data`. The dual of [`FunKindVar::pin_compute`].
    pub fn pin_data(&self) {
        let pin = &mut *self.pin.borrow_mut();
        *pin = match *pin {
            KindPin::Unpinned | KindPin::Data => KindPin::Data,
            KindPin::Compute | KindPin::Conflict => KindPin::Conflict,
        };
    }

    /// Copy `other`'s pin onto this variable, for a scheme instantiation carrying
    /// the definition site's answer onto the freshened copy.
    pub fn adopt_pin(&self, other: &FunKindVar) {
        *self.pin.borrow_mut() = other.pin();
    }
}

// Identity-based (by `uid`), mirroring `InferVar`: borrow-free, never touches
// `bounds`, so it is safe even while a variable's bounds are borrowed.
impl PartialEq for FunKindVar {
    fn eq(&self, other: &Self) -> bool {
        self.uid == other.uid
    }
}
impl Eq for FunKindVar {}
impl std::hash::Hash for FunKindVar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.uid.hash(state);
    }
}
impl fmt::Debug for FunKindVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "κ{}", self.uid.0)
    }
}

/// Reset the kind-variable counter to zero (test-only, for predictable output).
#[cfg(any(test, feature = "test-helpers"))]
pub fn reset_kind_var_counter() {
    FUN_KIND_VAR_COUNTER.store(0, Ordering::Relaxed);
}

/// A CCL type annotation.
///
/// Appears on [`TypedExpr`] nodes and as the output of type inference.
///
/// The transient variants divide ownership cleanly:
///
/// | Variant | Owner | Meaning | Must be eliminated by |
/// |---|---|---|---|
/// | `Hole` | Lowering | "This slot needs a type; not yet known" | End of inference (compiler bug if survives — flagged as `UnresolvedHole`) |
/// | `BoundedHole(𝑇)` | Lowering | "A bounded annotation `𝑥 <: 𝑇`: infer this, subject to `<: 𝑇`" — an obligation, not a shape | Pass 1's `normalize_annotation` (flagged as `UnresolvedBoundedHole` if it survives) |
/// | `Infer(id)` | Type checker only | "Inference variable N from the coalesce pass" | End of inference for any type reachable from the program's root output (flagged as `UnresolvedInfer` by `collect_type_errors`); an induction accumulator's *domain* is necessarily `Infer` until the unified phase resolves it (see `Strictness::PreDesugar`) |
/// | `History` (`kind: Overwrite`) | Type checker only | "Mutable variable: a `value` cell tracked over a `domain` (loop index or transaction time)" | the unified phase (`transact_phase` / `mut_elim`, which runs *before* `channelize`; a survivor downstream is a compiler bug) |
/// | `History` (`kind: Feed`) | Type checker only | "Feed channel `domain ⇒ value`: the defer binding's post-desugar stream type" | `channelize` (which runs after inference; a survivor downstream is a compiler bug) |
/// | `ChanDom(d, _)` | Type checker only | "Rigid nominal domain of feed channel `d` — its domain resolves at channel assembly" | `channelize` (substituted to the concrete channel domain; a survivor downstream is a compiler bug) |
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// A primitive base type.
    Base(BaseType),
    /// A finite index range `[0, n)`, used as the domain of list types.
    ///
    /// Emitted by `lower_list_comp` to annotate the outer lambda's parameter
    /// with the exact length of the source list. `compile_ccl::extent_of` maps
    /// it directly to `Extent::UIntRange { start: 0, end: n }`.
    UIntRange(usize),
    /// A function type. When `name` is `None` it is the ordinary
    /// non-dependent function type `domain ⇒ codomain`. When `name` is `Some(x)` it
    /// is a **Pi type** `(x: domain) ⇒ codomain`: the binder `x` is in scope
    /// in `codomain` and may be referenced by refinement predicates nested
    /// anywhere within it.
    ///
    /// Inference always populates `name` when it introduces a function type
    /// from a lambda's parameter (see `emit_lambda`); whether the codomain
    /// actually references the binder is a *property* of the resulting type,
    /// not a structural decision made up front. A `Some`-named function whose
    /// codomain does not mention the binder is observationally identical to
    /// the same function with `name: None` — the binder is only load-bearing
    /// once a nested refinement closes over it (dependent application).
    Fun {
        /// The Pi binder, if this function type is dependent. Bound in
        /// `codomain`. The derived [`PartialEq`] *does* compare it, but the
        /// α-aware comparisons that matter for dependent refinements strip it
        /// first (`without_pi_names`), so two function types equal up to
        /// renaming their Pi binder reconcile there (see the substitution
        /// machinery).
        name: Option<crate::ccl::Name>,
        /// Whether this function is a capability (`Compute`) or a data
        /// collection (`Data`). See [`FunKind`]. The derived [`PartialEq`] compares it: a
        /// data function and a compute function over the same domain/codomain
        /// are genuinely different types (one carries data, one a capability).
        ///
        /// Nothing structural distinguishes the two — only the construction
        /// site knows — so downstream the kind is *carried, never re-derived*:
        /// a typing rule reads it off the node's own type and a rewrite copies
        /// it from the type it replaces ([`Type::fun_like`]).
        kind: FunKind,
        /// The parameter (argument) type. Contravariant position.
        domain: Box<Type>,
        /// The result type. Covariant position; may reference `name`.
        codomain: Box<Type>,
    },
    /// An ordered product type with unnamed fields (tuple).
    Tuple(Vec<Type>),
    /// A named product type (record).
    Record(Vec<(String, Type)>),
    /// A tagged sum type — each tag has its own payload type.
    ///
    /// Tags are [`FieldKey`]s, the dual of `Record`/`Tuple` keys: `Name`
    /// for source-level `.Tag(...)` variants, `Index` for anonymous
    /// positional sums. This is the single sum representation — the
    /// formerly-separate untagged `Union` is just the all-`Index` case
    /// (`a ++ b` is `Variant([(Index(0), A), (Index(1), B)])`), so
    /// positional and named sums share one constructor, one coalesce
    /// path, and one width-subtyping rule. `Vec` order is preserved for
    /// display.
    ///
    /// The [`Openness`] says whether those arms are the *whole* arm set or only
    /// the part this type commits to — see that type for why a sum needs the
    /// distinction where a record does not.
    Variant(Vec<(FieldKey, Type)>, Openness),
    /// A refinement of another type
    Refinement(Box<Type>, Refinement),
    /// Pre-inference placeholder stamped by lowering on every new node.
    ///
    /// Invariant: every `Hole` must be eliminated by the end of inference.
    /// `Hole` carries no identity — it's a structural "fill this in later"
    /// marker. The inference pass replaces it either with a concrete type
    /// or with a `Type::Infer` variable. A surviving `Hole` means inference
    /// never visited the node, and is reported by `collect_type_errors` as
    /// `UnresolvedHole` (treat as a compiler bug, not a user-facing error).
    /// Created exclusively by [`TypedExpr::new`] and [`crate::ccl::TypedBinding::new_unannotated`].
    Hole,
    /// A [`Hole`](Type::Hole) with an **identity**: every occurrence carrying the
    /// same id normalizes to the *same* inference variable.
    ///
    /// This is how lowering states a relation between two type positions it cannot
    /// name. A plain `Hole` says "infer this", and each occurrence gets its own
    /// fresh variable; `SharedHole(id)` says "infer this, and it is the same one as
    /// that" — the weakest thing that lets a desugaring connect two positions whose
    /// common type only inference will learn.
    ///
    /// **Transient, like `Hole`**: `normalize_annotation` resolves it, and a
    /// survivor is a compiler bug (`UnresolvedHole`). Ids are minted per
    /// [`LoweringContext`](crate::ccl::lower::LoweringContext) and are meaningless
    /// outside the tree they were minted for.
    SharedHole(u32),
    /// Pre-inference placeholder for a **bounded** annotation `𝑥 <: 𝑇`: "some
    /// type that is a subtype of `𝑇`", to be inferred.
    ///
    /// [`Hole`](Self::Hole) with a ceiling — `Hole` is the unbounded case, and
    /// the two compose wherever a compound annotation is only partly specified
    /// (the per-position modes of a multi-parameter `def`'s single tuple
    /// annotation are exactly this). `normalize_annotation` erases it into a
    /// fresh [`Infer`](Self::Infer) carrying `𝑇` as an upper bound.
    ///
    /// **This is not a type.** Like [`Hole`](Self::Hole) and [`Infer`](Self::Infer)
    /// it denotes no set of values — it is a *slot* inhabiting the `Type` enum
    /// because annotations are typed positions, and it states an obligation for
    /// inference rather than a shape. `BoundedHole(𝑇)` is not "the type of values below
    /// `𝑇`": there is no such type, which is why nothing may subtype against one,
    /// narrow against one, or compact one. The solver has no rule for it and asserts
    /// so (`constrain::extrude`, `compact`); only the
    /// *structural* walks that rewrite every slot uniformly — substitution,
    /// free-variable collection, refinement stripping — pass through it.
    ///
    /// **Annotation position only, and transient**: lowering writes it, inference
    /// erases it, and no pass downstream may observe one. The annotation slots it
    /// occupies do not survive inference at all
    /// (`infer::api::debug_assert_annotations_cleared`), so a binder `ty` is the
    /// only place a survivor could hide — flagged there by `collect_type_errors`
    /// as [`InferError::UnresolvedBoundedHole`](crate::ccl::infer::InferError::UnresolvedBoundedHole).
    ///
    /// See `src/ccl/design/type-inference.md`, "Annotation kinds: exact and bounded".
    BoundedHole(Box<Type>),
    /// Unresolved type variable, identified by a unique [`crate::ccl::InferVarId`].
    ///
    /// Created during inference by the inference pass
    /// ([`crate::ccl::infer`]) when coalescing a constraint
    /// variable whose bounds left it genuinely unconstrained (e.g. an
    /// identity lambda's parameter with no call-site usage).
    ///
    /// Invariant: any `Infer` reachable from the program's root output
    /// type is an *ambiguous-type* error, reported by `collect_type_errors`
    /// as `UnresolvedInfer`. `Infer` survivals are permitted only inside
    /// sub-expressions whose output type is not exercised (e.g. a top-level
    /// `f = \x -> x` that is never applied).
    ///
    /// Carries the mutable [`InferVar`] (id + level + bounds) that the
    /// solver constrains in place. A *coalesced* `Infer` (one
    /// surviving inference) has empty bounds and matters only for its
    /// `uid`; the solver guarantees no still-mutating variable escapes
    /// into a downstream pass.
    Infer(Rc<InferVar>),
    /// The opaque domain type of an externally-registered data source.
    ///
    /// Used as the domain in `Fun(DataSource(name), output_type)` types emitted
    /// by the source registry.  [`crate::interpreter::operator_conversion::OpConversionContext`]
    /// resolves this to a concrete `Extent::DataSourceDomain(rc)` at compilation time
    /// by looking the name up in its source-domain-extent registry.
    DataSource(String),
    /// the nominal, rigid domain of a feed channel, named by
    /// its defer binder. Minted by inference when it types a `let d = Defer`
    /// binding (instead of a fresh `Infer` domain), so every consumer of a
    /// read of `d` types *concretely* against `ChanDom(d)` and no `Infer`
    /// channel-domain residue forms. `channelize` erases it with a whole-tree
    /// substitution `ChanDom(d) ↦ <concrete channel domain>` once the channel
    /// is assembled. Like [`Type::DataSource`], it is a nominal leaf whose
    /// domain resolves later; unlike it, it is *transient* — no pass after
    /// `channelize` may observe one.
    ///
    /// The second field is the domain's **introduction level** (the inference
    /// level of the `let d = Defer` RHS that minted it). It makes channel
    /// identity *per-instantiation*: `freshen_above` renames a `ChanDom`
    /// above its cutoff exactly as it freshens a quantified variable, so a
    /// defer inside a generalized definition names a distinct channel per
    /// specialization, while a captured outer channel (level ≤ cutoff) stays
    /// shared. Identity-transparent (see [`ChanLevel`]) and inference-only —
    /// dead weight after `channelize` erases the type.
    ChanDom(crate::ccl::Name, ChanLevel),
    /// The transaction-commit domain: an anonymous total order of commit times
    /// issued by the runtime (the prototype's `CommitTime`). It is the domain of
    /// transactional histories (`Txn ⇒ V`), the codomain of the per-site
    /// `begin_<site>` oracles, and the type of a transaction handle. Like
    /// `DataSource`, it has no enumerable static domain — its positions exist only
    /// in the tile. See src/ccl/design/mutability.md.
    Txn,
    /// The type of a **history** handle: a function `domain ⇒ value` that a
    /// `:=` mutable variable or a `defer`/`<<` channel writes incrementally. One variant
    /// for both — a mutable variable and a feed channel are the same object (an
    /// invariant, deref-transparent `domain ⇒ value`); they differ only in the
    /// [`HistoryKind`]:
    ///
    /// - [`HistoryKind::Overwrite`] — a **mutable variable** (`:=` / `+=`). A reference
    ///   reads through to its `value` (the scalar behind `Mut(Int, D)`; `cnt + 1`
    ///   reads the `Int`), its writes may read the previous position
    ///   (`get_prev_seq` recurrence), and its trailing read is `final_or_default`
    ///   (a scalar). The unified phase materializes it with a carry-forward arm.
    /// - [`HistoryKind::Append`] — a **feed channel** (`defer` / `<<` / `<<=`). A
    ///   reference reads the whole stream (`domain ⇒ value`), off-path positions
    ///   are absent (no carry-forward), and `channelize` resolves it to the
    ///   collected channel.
    ///
    /// Either way it is **invariant** in both children, and the reason is
    /// narrower than "a reference is both read and written". A mutable variable's writes
    /// contribute *lower* bounds to its value type — the value type is the join
    /// over the seed and every write, and the lattice already is that join (see
    /// the `MutWrite` arm of `infer::emit::emit_node`) — so where that type is
    /// *inferred*, nothing uses it contravariantly and covariance would be sound.
    /// Invariance is what protects a **declared** value type, where the same
    /// write edge reads as a demand *on* the writes rather than a contribution
    /// *to* them: without it, passing a `Mut({a: Int, b: Int})` mutable variable to a
    /// parameter declared `Mut({a: Int})` would let the callee's `r := (a=5)`
    /// drop a field the caller's declaration requires. That cannot be narrowed to
    /// "invariant only where the value type is declared", because *declaredness is
    /// provenance, not a property of a type*: a variance rule sees two types and
    /// cannot ask where either came from.
    ///
    /// **The rule is what enforces that across a function boundary**, and it can be
    /// because the handle reaches the parameter: `emit_apply` decides pass-by-reference
    /// from the parameter read off the head of the application spine and leaves the
    /// argument's `Mut` intact, so the `(History, History)` arm relates the two value
    /// types directly. Both directions come from the one rule rather than being
    /// assembled from an application edge plus a compensating write contribution — the
    /// shape this needed while a deref coercion erased the handle before invariance
    /// could see it. The property is still pinned by test
    /// (`a_mut_vars_value_type_is_invariant_across_a_mut_parameter`), which is what
    /// would catch a future consolidation quietly dropping one direction.
    ///
    /// It is also a **transient** variant like `Hole` / `Infer`: it exists only between type
    /// inference (which stamps it on `:=` / `defer` introductions and every
    /// reference) and the passes that erase it — the unified phase
    /// (`transact_phase` / `mut_elim`) for `Overwrite` histories, `channelize`
    /// for `Feed` ones. Both erase it to a bare `Type::Fun`; no pass downstream
    /// may observe a `History` (a survivor at the strict wall is a compiler bug —
    /// see `collect_type_errors`). See src/ccl/design/mutability.md.
    History {
        /// The type of the history's value (a position's cell / element). Read
        /// through by the deref coercion for a [`HistoryKind::Overwrite`] reference.
        value: Box<Type>,
        /// The index the history's positions are tracked over (loop index,
        /// transaction time, or a feed channel's collection domain).
        domain: Box<Type>,
        /// Whether this is a mutable variable or a feed channel — selects the read
        /// mode (scalar-final vs whole-stream) and, in the unified phase, whether
        /// off-path positions carry forward.
        kind: HistoryKind,
    },
    // Planned:
    // Pi { param: String, param_ty: Box<Type>, body_ty: Box<Type> }
}

/// Which flavour of [`Type::History`] a handle is — a mutable variable (`:=`) or a
/// feed channel (`defer` / `<<`). The two are the same object (a `domain ⇒
/// value` history) but read and materialize differently; see [`Type::History`].
///
/// `Ord` carries no semantics — the two kinds are unordered alternatives. It
/// exists so a kind can key a `BTreeMap`, which is how the monomorphization
/// specialization key holds a position's history contributions without having to
/// pick a winner between two kinds (see `src/ccl/infer/solver/spec_key.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HistoryKind {
    /// A mutable variable introduced by `:=` — deref-on-read to the scalar `value`,
    /// a `get_prev_seq` / `get_prev_txn` recurrence, a `final_or_default` trailing
    /// read, and a carry-forward arm for off-path positions.
    Overwrite,
    /// A feed channel introduced by `defer` and written with `<<` / `<<=` — read
    /// as the whole `domain ⇒ value` stream, with off-path positions absent.
    Append,
}

/// If every tag in `tags` is an anonymous positional [`FieldKey::Index`]
/// tag (as produced by `++`/`Copair` and other unnamed sums),
/// return the payloads in order — recursively flattening nested
/// all-positional variants so chained `a ++ b ++ c` renders flat as
/// `A | B | C` rather than as nested `[._0: … | ._1: …]`. Returns `None`
/// for any variant containing a `Name` tag (a source-level `.Tag(...)`),
/// which is rendered with its tags shown.
///
/// Because positional (`Index`) and named (`Name`) tags are distinct
/// `FieldKey` cases, there is no ambiguity here: a user-written named tag
/// can never be mistaken for a synthetic positional one.
fn synthetic_payloads(tags: &[(FieldKey, Type)]) -> Option<Vec<Type>> {
    if tags.iter().any(|(k, _)| !matches!(k, FieldKey::Index(_))) {
        return None;
    }
    let mut out = Vec::with_capacity(tags.len());
    for (_, t) in tags {
        match t {
            Type::Variant(inner, _) => match synthetic_payloads(inner) {
                Some(mut flat) => out.append(&mut flat),
                None => out.push(t.clone()),
            },
            _ => out.push(t.clone()),
        }
    }
    Some(out)
}

// Wire shape (inspector, feature `serde`): a `Type` serializes as its rendered
// `Display` string (`"Int"`, `"Int -> Int"`), not structurally — the inspector
// schema wants the human type rendering, and structural serialization of the
// type AST would leak internals (`Infer` ids, holes) the client never wants.
#[cfg(feature = "serde")]
impl serde::Serialize for Type {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

/// Renders through [`fmt_type`] with no enclosing arrow: a self-contained type
/// carries every arrow its references name, so the spelling is complete. A type
/// shown detached from an arrow that binds one of its references renders that
/// reference as its bare index — see [`symbolic::PiBinderEnv`].
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_type(f, self, None)
    }
}

/// `ty` rendered inside `binders` — the [`Display`](fmt::Display) form of
/// [`fmt_type`], for a caller that holds an environment and needs a type
/// string. The symbolic printer takes this for the type slots it renders
/// inside a refinement predicate, so a reference to an enclosing arrow prints
/// as that arrow's binder name there too.
pub(crate) struct TypeUnder<'a, 'b>(
    pub(crate) &'a Type,
    pub(crate) Option<&'a symbolic::PiBinderEnv<'b>>,
);

impl fmt::Display for TypeUnder<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_type(f, self.0, self.1)
    }
}

/// Render `ty` inside `binders`, the arrows the rendering has descended
/// through. Threading them is what lets a refinement predicate print a
/// reference to one of those arrows by the arrow's own binder name rather than
/// as a de Bruijn index (`src/ccl/design/type-inference.md`, "Rendering opens
/// what it descended through").
fn fmt_type(
    f: &mut fmt::Formatter<'_>,
    ty: &Type,
    binders: Option<&symbolic::PiBinderEnv<'_>>,
) -> fmt::Result {
    /// `ty` as a string in the same environment, for the arms that join parts.
    fn render(ty: &Type, binders: Option<&symbolic::PiBinderEnv<'_>>) -> String {
        TypeUnder(ty, binders).to_string()
    }
    {
        match ty {
            Type::Base(b) => write!(f, "{}", b.keyword()),
            // `n == 0` means an empty range (e.g. the domain of `[]`); render
            // it as `∅` instead of computing `n - 1` and underflowing.
            Type::BoundedHole(t) => write!(f, "<:{}", render(t, binders)),
            Type::UIntRange(0) => write!(f, "∅"),
            Type::UIntRange(n) => write!(f, "[0, {}]", n - 1),
            // The rendered symbol reflects the resolved `kind`: `⇒` for a compute
            // capability (and an unresolved kind var), `⤇` for a data collection
            // (see `FunKind::arrow`), making the collection/capability distinction
            // legible in every type string.
            //
            // The codomain renders one arrow deeper, named or not: the index
            // counts crossings, so an unnamed arrow occupies an entry too.
            Type::Fun {
                name,
                kind,
                domain,
                codomain,
            } => {
                let inner = symbolic::PiBinderEnv::crossing(binders, name.as_ref());
                let cod = render(codomain, Some(&inner));
                let dom = render(domain, binders);
                match name {
                    Some(x) => write!(f, "(({x}: {dom}) {} {cod})", kind.arrow()),
                    None => write!(f, "({dom} {} {cod})", kind.arrow()),
                }
            }
            Type::Tuple(ts) => {
                let parts: Vec<_> = ts.iter().map(|t| render(t, binders)).collect();
                write!(f, "({})", parts.join(", "))
            }
            Type::Record(fields) => {
                let parts: Vec<_> = fields
                    .iter()
                    .map(|(n, t)| format!("{n}: {}", render(t, binders)))
                    .collect();
                write!(f, "{{{}}}", parts.join(", "))
            }
            Type::Variant(tags, openness) => {
                // An **open** arm set renders with a trailing `| …`, so a demand that
                // admits further tags never reads as an exact sum in a diagnostic or a
                // symbolic dump. (Only a demand is ever open — see `Openness`.)
                let ellipsis = if openness.permits_extra_tags() {
                    " | …"
                } else {
                    ""
                };
                // Anonymous positional variants (all tags are
                // `FieldKey::Index`, as `++`/`Copair` produces) are
                // rendered as a flat `A | B` join — the positional tags
                // carry no user-meaningful information. Nested
                // all-positional variants flatten recursively so
                // `a ++ b ++ c` prints as `A | B | C` rather than
                // `[._0: [._0: A | ._1: B] | ._1: C]`.
                if let Some(payloads) = synthetic_payloads(tags) {
                    let parts: Vec<_> = payloads.iter().map(|t| render(t, binders)).collect();
                    write!(f, "{}{ellipsis}", parts.join(" | "))
                } else {
                    // CHL's surface spelling — see `fmt_variant_arms`. A `Unit`
                    // payload is the nullary constructor and renders bare.
                    crate::util::fmt_variant_arms(
                        f,
                        tags.iter().map(|(n, t)| {
                            let payload = match t {
                                Type::Base(BaseType::Unit) => None,
                                _ => Some(render(t, binders)),
                            };
                            (n.to_string(), payload)
                        }),
                        openness.permits_extra_tags(),
                    )
                }
            }
            // A **singleton** prints as its base pinned to the literal: `{Int |
            // __elem == 5}` is `Int@5`. The predicate is the type's whole content,
            // and spelling it out puts one in front of the reader at every literal.
            // Every other refinement prints in the general form.
            //
            // The predicate renders inside `binders`, so a reference to an
            // enclosing arrow prints as that arrow's binder name.
            Type::Refinement(t, r) => match singleton_value(ty) {
                Some(lit) => write!(f, "{}@{}", render(t, binders), symbolic::symbolic(lit)),
                None => write!(
                    f,
                    "{{{} | {}}}",
                    render(t, binders),
                    symbolic::symbolic_under(&r.predicate, binders)
                ),
            },
            Type::Hole => write!(f, "_"),
            // A hole with an identity renders as one: `_#0` and `_#1` are distinct
            // requests, two `_#0`s are the same one.
            Type::SharedHole(id) => write!(f, "_#{id}"),
            Type::Infer(var) => write!(f, "?{}", var.uid),
            Type::DataSource(name) => write!(f, "source({name})"),
            Type::ChanDom(name, _) => write!(f, "chan({name})"),
            Type::Txn => write!(f, "Txn"),
            Type::History {
                value,
                domain,
                kind,
            } => {
                let (value, domain) = (render(value, binders), render(domain, binders));
                if *kind == HistoryKind::Overwrite {
                    write!(f, "Mut({value}, {domain})")
                } else {
                    write!(f, "feed({domain} ⇒ {value})")
                }
            }
        }
    }
}

/// The literal a **singleton** refinement pins, if `ty` is one: a base refined by
/// exactly `__elem == <lit>` and nothing else.
///
/// Presentation only. The type keeps its general [`Type::Refinement`] shape — every
/// rule that handles refinements handles this one unchanged — and this recognizes
/// the shape just well enough to print it as what it means.
fn singleton_value(ty: &Type) -> Option<&TypedExpr> {
    let Type::Refinement(base, r) = ty else {
        return None;
    };
    // Exactly one layer: a further-refined singleton is not one.
    if matches!(base.as_ref(), Type::Refinement(..)) {
        return None;
    }
    let TypedExprNode::BinOp {
        left,
        op: crate::ccl::BinOpKind::Compare(crate::ccl::CompareKind::Equals),
        right,
    } = &r.predicate.node
    else {
        return None;
    };
    let elem_lhs = matches!(&left.node, TypedExprNode::Var(n) if n.is_elem());
    (elem_lhs && matches!(right.node, TypedExprNode::Lit(_))).then_some(right.as_ref())
}

impl Type {
    /// The product of `elems` — a [`Type::Tuple`], or [`BaseType::Unit`] when
    /// there are none.
    ///
    /// **There is exactly one empty product and it is `Unit`.** `Tuple([])` and
    /// `Record([])` are not valid types (`docs/chl-spec.md`, "6.6 The empty
    /// product is unit"), so any site building a tuple type from a
    /// *variable-length* collection must come through here rather than naming
    /// the variant. Sites with a literal two-or-more-element `vec![…]` can
    /// construct `Type::Tuple` directly — the invariant is not in question
    /// there.
    ///
    /// Two spellings for one type would not merely be untidy, they would fail
    /// to *reconcile*: a product with no fields has no keys to distinguish
    /// positional from named keying, so independent sites would each pick an
    /// empty spelling arbitrarily, and the post-inference consistency wall
    /// (which compares a node's recorded type against one rebuilt from its
    /// children) would reject the node — reporting the self-contradictory
    /// `expected (), found ()`, since both spellings render the same.
    pub fn tuple(elems: Vec<Self>) -> Self {
        if elems.is_empty() {
            return Type::Base(BaseType::Unit);
        }
        Type::Tuple(elems)
    }

    /// The named product of `fields` — a [`Type::Record`], or
    /// [`BaseType::Unit`] when there are none. See [`Type::tuple`] for why the
    /// empty case collapses.
    pub fn record(fields: Vec<(String, Self)>) -> Self {
        if fields.is_empty() {
            return Type::Base(BaseType::Unit);
        }
        Type::Record(fields)
    }

    /// Helper for creating a non-dependent **compute** function type
    /// (`name: None`, `kind: Compute`).
    pub fn fun(domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: None,
            kind: FunKind::Compute,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// `Option(𝑇)` — the two-tag variant `{some: 𝑇, none: Unit}`.
    ///
    /// A built-in type *abbreviation*, in the same category as `List(T)` — see
    /// `docs/chl-spec.md`, "3.15 Variant constructors".
    /// It is **not** a distinguished kind of type: the result is an ordinary
    /// structural [`Type::Variant`], and the constructors `` `some(𝑒) `` / `` `none ``
    /// are ordinary variant constructors that no pass gives special treatment.
    /// This function is the only place in the compiler that mentions either tag
    /// spelling; when type aliases land it is replaced by a prelude
    /// `` Option(T) = {`some{T} | `none} `` and deleted.
    ///
    /// Tags are listed in **name order** (`none` before `some`) on purpose: the
    /// solver materializes a coalesced variant from a `BTreeMap`, so an inferred
    /// variant's tags always come out name-ordered. Writing the abbreviation in
    /// that same order is what lets an `Option(T)` *annotation* compare equal to
    /// the inferred type structurally instead of differing only by tag order.
    pub fn option_of(payload: Self) -> Self {
        Type::variant(vec![
            (FieldKey::Name("none".into()), Type::Base(BaseType::Unit)),
            (FieldKey::Name("some".into()), payload),
        ])
    }

    /// A **closed** tagged sum: these arms and no others.
    ///
    /// The constructor for every *producer* of a sum. See [`Openness`].
    pub fn variant(arms: Vec<(FieldKey, Type)>) -> Self {
        Type::Variant(arms, Openness::Closed)
    }

    /// An **open** tagged sum: these arms, and possibly more.
    ///
    /// Only for a *demand* — the arm set a consumer commits to handling, where a
    /// subtype carrying further tags is admissible. See [`Openness`].
    pub fn open_variant(arms: Vec<(FieldKey, Type)>) -> Self {
        Type::Variant(arms, Openness::Open)
    }

    /// Helper for creating a dependent (Pi) **compute** function type
    /// `(name: domain) ⇒ codomain`.
    ///
    /// Construction closes: free references to `name` in `codomain` become
    /// de Bruijn indices ([`crate::ccl::subst::close_pi_binder`]), so the
    /// constructed arrow never carries a free name for its own binder and two
    /// α-variant arrows are structurally identical. See
    /// `src/ccl/design/type-inference.md`, "Where the conversions run".
    pub fn pi(name: impl Into<crate::ccl::Name>, domain: Self, codomain: Self) -> Self {
        Type::pi_kinded(name, domain, codomain, FunKind::Compute)
    }

    /// [`Type::pi`] at an explicit kind, for a rebuild that carries the arrow kind
    /// it is replacing: a group-by partition function is a dependent *collection*,
    /// so its Pi stays `⤇` instead of flattening to the capability arrow.
    ///
    /// Closes its codomain exactly as [`Type::pi`] does — the kind is the only
    /// difference, and reaching for a bare [`Type::Fun`] literal to get it is what
    /// leaves a free binder name in a stored type.
    pub fn pi_kinded(
        name: impl Into<crate::ccl::Name>,
        domain: Self,
        codomain: Self,
        kind: FunKind,
    ) -> Self {
        let name = name.into();
        let codomain = crate::ccl::subst::close_pi_binder(&name, &codomain);
        Type::Fun {
            name: Some(name),
            kind,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// This type's [`FunKind`] if it is a function, looking through refinements.
    ///
    /// A refined function (`{Fun | p}`) still carries a kind, and a match on the
    /// bare type drops it, so every reader that wants the kind wants this.
    pub fn fun_kind(&self) -> Option<&FunKind> {
        match self.peel_refinements() {
            Type::Fun { kind, .. } => Some(kind),
            _ => None,
        }
    }

    /// `self` re-stamped with `provenance`'s [`FunKind`], through any
    /// refinements on either side. A non-`Fun` on either side is a no-op.
    ///
    /// A pass that **re-kinds one node** and has to carry that onto a second type
    /// stating the same function type needs this: `wrap_with_iterate` re-kinding an
    /// iteration site, whose consuming combinator head declares the site as its
    /// domain, or a `Let` whose kind follows its body, or a `Cast`'s `target`
    /// (`ccl_utils::sync_cast_target_kind`). The kinds are incomparable, so a
    /// stale copy is not a harmless widening — it is a different claim about what
    /// the value *is*. Everything else (refinements, the Pi binder, the domain and
    /// codomain) stays, because only the kind moved.
    pub fn with_kind_of(&self, provenance: &Type) -> Type {
        let Some(kind) = provenance.fun_kind() else {
            return self.clone();
        };
        fn restamp(t: &Type, kind: &FunKind) -> Type {
            match t {
                Type::Fun {
                    name,
                    domain,
                    codomain,
                    ..
                } => Type::Fun {
                    name: name.clone(),
                    kind: kind.clone(),
                    domain: domain.clone(),
                    codomain: codomain.clone(),
                },
                Type::Refinement(base, r) => {
                    Type::Refinement(Box::new(restamp(base, kind)), r.clone())
                }
                other => other.clone(),
            }
        }
        restamp(self, kind)
    }

    /// The function type an **elimination** demands: a Pi whose kind is a fresh
    /// [`FunKind::Var`].
    ///
    /// `Data` and `Compute` are incomparable, so a demand stamped with either
    /// one rejects the other. Application does not care: indexing a collection
    /// and calling a capability are the same node, and the rule that types them
    /// only needs *some* function with this domain and codomain. Leaving the kind
    /// inferred says exactly that — the applied value's own kind flows in and
    /// pins it, and a demand nothing pins defaults to `Compute` like any other
    /// unconstrained kind.
    ///
    /// Contrast [`Type::pi`] / [`Type::fun`] / [`Type::data_fun`], which *stamp*
    /// a kind and are for a position that genuinely means one of the two.
    pub fn pi_eliminated(name: impl Into<crate::ccl::Name>, domain: Self, codomain: Self) -> Self {
        Type::pi_kinded(name, domain, codomain, FunKind::fresh_var())
    }

    /// The non-dependent [`Type::pi_eliminated`] — an elimination's demand
    /// with no Pi binder.
    pub fn fun_eliminated(domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: None,
            kind: FunKind::fresh_var(),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Helper for creating a non-dependent **data** function type
    /// (`name: None`, `kind: Data`) — a collection `domain ⤇ codomain`.
    pub fn data_fun(domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: None,
            kind: FunKind::Data,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Rebuild a function type copying `name` and `kind` from an `exemplar`
    /// `Fun`, so a downstream rebuild (lambda elimination, inlining, planning)
    /// can never silently flip a data function to compute or drop its Pi binder. A
    /// non-`Fun` exemplar yields a plain `Compute` function type with no binder —
    /// the safe default at a site with no function type to copy from.
    pub fn fun_like(exemplar: &Type, domain: Self, codomain: Self) -> Self {
        match exemplar {
            Type::Fun { name, kind, .. } => {
                // Construction closes (see [`Type::pi`]): a rebuild computes
                // its codomain from node types, which reference the binder by
                // name. Idempotent on a codomain extracted from a closed
                // arrow — its references are already indices.
                let codomain = match name {
                    Some(b) => crate::ccl::subst::close_pi_binder(b, &codomain),
                    None => codomain,
                };
                Type::Fun {
                    name: name.clone(),
                    kind: kind.clone(),
                    domain: Box::new(domain),
                    codomain: Box::new(codomain),
                }
            }
            _ => Type::fun(domain, codomain),
        }
    }

    /// Look through every outer [`Type::Refinement`] layer, returning the bare
    /// structural type underneath. Borrowing and non-allocating; refinements
    /// nested inside the structure are left in place.
    ///
    /// **A shape test looks through a refinement**, and that is not leniency: a
    /// refinement is a claim about a value, not part of the shape carrying it, so
    /// `{(𝐷 ⇒ 𝑉) | 𝑝}` *is* a function and `{Mut(𝑉, 𝐷) | 𝑝}` *is* a mutable variable.
    /// Anything that dispatches on or destructures a shape peels first — including
    /// the handle accessors below.
    ///
    /// The all-depths counterpart, [`crate::ccl::ccl_utils::strip_refinements`],
    /// is a different operation: it *drops* refinements rather than looking past them,
    /// allocates, and is only meaningful on a resolved type.
    pub fn peel_refinements(&self) -> &Type {
        let mut cur = self;
        while let Type::Refinement(inner, _) = cur {
            cur = inner;
        }
        cur
    }

    /// The value type of the mutable variable this denotes, or `None` if it is not
    /// one.
    ///
    /// A mutable variable is a [`HistoryKind::Overwrite`] history `Mut(𝑉, 𝐷)`, and
    /// this is `𝑉` — what one read of it yields. A feed channel is deliberately
    /// *not* one ([`Type::as_feed`]): it reads as its whole stream, so the two are
    /// never interchangeable at a read.
    pub fn mut_value_type(&self) -> Option<&Type> {
        match self.peel_refinements() {
            Type::History {
                value,
                kind: HistoryKind::Overwrite,
                ..
            } => Some(value),
            _ => None,
        }
    }

    /// The `(domain, value)` of the feed channel this denotes, or `None` if it is
    /// not one.
    ///
    /// A channel is a [`HistoryKind::Append`] history, and what a read of it yields
    /// is the whole stream `domain ⇒ value` — hence the pair, where
    /// [`Type::mut_value_type`] returns a single value type.
    pub fn as_feed(&self) -> Option<(&Type, &Type)> {
        match self.peel_refinements() {
            Type::History {
                domain,
                value,
                kind: HistoryKind::Append,
            } => Some((domain, value)),
            _ => None,
        }
    }

    /// Whether this denotes a **handle** to state introduced elsewhere — a mutable
    /// variable or a feed channel, either [`HistoryKind`].
    ///
    /// This is the kind-agnostic question, and the thing that asks it is a
    /// *binding*: naming a handle aliases the state behind it whichever kind it is,
    /// so the choice between binding the handle and binding a copy of its value
    /// turns on handle-ness alone.
    pub fn is_handle(&self) -> bool {
        matches!(self.peel_refinements(), Type::History { .. })
    }

    /// If this is a function type, return the domain type, otherwise None.
    pub fn domain(&self) -> Option<Type> {
        if let Type::Fun { domain, .. } = &self {
            Some(domain.as_ref().clone())
        } else {
            None
        }
    }

    /// If this is a function type, return the codomain type, otherwise None.
    pub fn codomain(&self) -> Option<Type> {
        if let Type::Fun { codomain, .. } = &self {
            Some(codomain.as_ref().clone())
        } else {
            None
        }
    }

    /// A structural copy with every Pi binder name erased (`Fun.name → None`)
    /// and every function **kind** canonicalized to `Compute`.
    ///
    /// The binder is load-bearing only inside the type solver (it carries
    /// dependent-refinement correspondences); downstream passes treat function
    /// types structurally and a `Some`/`None` binder is the same type to them.
    /// Use this when comparing types for structural equality across a pass that
    /// does not preserve the cosmetic binder.
    ///
    /// FunKind is normalized for the same reason the binder is: these comparisons
    /// are about domain and codomain structure, not provenance. Elimination does
    /// carry a lambda's kind across (`elim_lambda_kinded`); normalizing here only
    /// keeps the structural asserts (and the feed-operand agreement check) from
    /// comparing it.
    ///
    /// Binder **presence** is all this canonicalizes. It does not reconcile the
    /// two binder-reference coordinates: a refinement spelled as an index and its
    /// name-coordinate twin stay unequal here, so the comparisons below hold
    /// only between two types on the same side of a construction boundary. That
    /// is the invariant they are checking, not an assumption they make — a pass
    /// that dropped a binder and left the index behind fails them.
    ///
    /// Under the Barendregt convention the blindness needed at the remaining
    /// call sites (lambda elimination's type-preservation asserts) is exactly
    /// `Some` vs `None`: both compared types descend from one derivation, so
    /// when both carry a binder it is the *same* [`crate::ccl::Name`] (uids are preserved
    /// by every copy along the lineage). What elimination does not preserve is
    /// the binder's presence — rebuilt combinator types (`fun_ty_or_hole`,
    /// [`Type::fun`]) are constructed with `name: None`. If those sites ever
    /// preserve binders on rebuilt types, this helper can retire.
    pub fn without_pi_names(&self) -> Type {
        match self {
            Type::Fun {
                domain, codomain, ..
            } => Type::Fun {
                name: None,
                // Canonicalize the kind so the comparison is about *shape*. Nothing
                // here says elimination may lose it — `elim_lambda_kinded` carries a
                // lambda's kind across — only that these asserts are checking
                // domain/codomain structure and the Pi binder, not provenance.
                kind: FunKind::Compute,
                domain: Box::new(domain.without_pi_names()),
                codomain: Box::new(codomain.without_pi_names()),
            },
            Type::BoundedHole(t) => Type::BoundedHole(Box::new(t.without_pi_names())),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| t.without_pi_names()).collect()),
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), t.without_pi_names()))
                    .collect(),
            ),
            Type::Variant(tags, openness) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), t.without_pi_names()))
                    .collect(),
                *openness,
            ),
            Type::Refinement(base, r) => {
                Type::Refinement(Box::new(base.without_pi_names()), r.clone())
            }
            Type::History {
                value,
                domain,
                kind,
            } => Type::History {
                value: Box::new(value.without_pi_names()),
                domain: Box::new(domain.without_pi_names()),
                kind: *kind,
            },
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::SharedHole(_)
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn => self.clone(),
        }
    }

    /// Create a fresh [`Type::Infer`] variable for use in tests.
    ///
    /// Use this only when constructing expressions in tests that will not be
    /// run through inference (e.g. to exercise pretty-printing or symbolic
    /// output), or to provide an unannotated parameter type that inference
    /// will fill in.
    #[cfg(test)]
    pub fn infer() -> Self {
        Type::Infer(InferVar::fresh(0))
    }

    /// Invoke `f` on each direct child [`Type`] of this type.
    ///
    /// "Direct child" means a `Type` reachable through this type's value
    /// fields — the domain and codomain of a `Fun`, the elements of a
    /// `Tuple` / `Record`, the payloads of a `Variant`, and the base of a
    /// `Refinement`.
    ///
    /// Does **not** descend into the refinement *predicate* (which is a
    /// [`TypedExpr`], not a `Type`).  Callers that need to walk a
    /// refinement's predicate must handle [`Type::Refinement`] explicitly
    /// — e.g. by matching on it before calling this helper.
    pub fn walk_children(&self, mut f: impl FnMut(&Type)) {
        match self {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::SharedHole(_)
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn => {}
            // A bounded annotation's bound is an ordinary child type — a pass
            // that rewrites types (uniquify's α-renaming, `subst`) must reach
            // inside it exactly as it reaches inside a `Refinement`.
            Type::BoundedHole(t) => f(t),
            Type::Fun {
                domain, codomain, ..
            } => {
                f(domain);
                f(codomain);
            }
            Type::Tuple(ts) => {
                for t in ts {
                    f(t);
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    f(t);
                }
            }
            Type::Refinement(base, _) => f(base),
            Type::History { value, domain, .. } => {
                f(value);
                f(domain);
            }
            Type::Variant(tags, _) => {
                for (_, t) in tags {
                    f(t);
                }
            }
        }
    }

    /// Mutable analog of [`walk_children`](Self::walk_children).
    ///
    /// Same caveats apply: does not descend into the refinement predicate.
    pub fn walk_children_mut(&mut self, mut f: impl FnMut(&mut Type)) {
        match self {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::SharedHole(_)
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn => {}
            // A bounded annotation's bound is an ordinary child type — a pass
            // that rewrites types (uniquify's α-renaming, `subst`) must reach
            // inside it exactly as it reaches inside a `Refinement`.
            Type::BoundedHole(t) => f(t),
            Type::Fun {
                domain, codomain, ..
            } => {
                f(domain);
                f(codomain);
            }
            Type::Tuple(ts) => {
                for t in ts {
                    f(t);
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    f(t);
                }
            }
            Type::Refinement(base, _) => f(base),
            Type::History { value, domain, .. } => {
                f(value);
                f(domain);
            }
            Type::Variant(tags, _) => {
                for (_, t) in tags {
                    f(t);
                }
            }
        }
    }

    /// Fold `f` left-to-right over the direct child [`Type`]s, starting
    /// from `init`.  Mirrors [`TypedExpr::fold_children`].
    pub fn fold_children<T>(&self, init: T, mut f: impl FnMut(T, &Type) -> T) -> T {
        let mut acc = Some(init);
        self.walk_children(|t| {
            let v = acc
                .take()
                .expect("Type::fold_children: closure invoked re-entrantly");
            acc = Some(f(v, t));
        });
        acc.expect("Type::fold_children: walk_children dropped accumulator")
    }
}

/// Represents a type refinement: a base type narrowed by a boolean predicate.
///
/// The refinement *is a binding form*. Rather than carry a per-refinement
/// binder name, every refinement implicitly binds the single reserved
/// [`REFINEMENT_BINDER`], which ranges over the refined base type and is free
/// in [`predicate`]. A predicate references its own element through that one
/// name; nested refinements simply shadow it, which is the correct lexical
/// scoping (a predicate never refers to an *outer* refinement's element, only
/// to its own plus enclosing `Fun`-binders, which have their own distinct
/// names). A fixed binder means refinement equality is plain structural
/// equality of the bare predicate — no α-renaming needed.
///
/// [`predicate`]: Refinement::predicate
#[derive(Debug, Clone)]
pub struct Refinement {
    /// A **bare**, *immutable* boolean expression (not a lambda) in which
    /// [`REFINEMENT_BINDER`] is free. Compiled as an element-wise loop join
    /// when its type is iterated. A rewrite produces a *new* term (structural
    /// `Rc` sharing keeps that cheap); nothing mutates a predicate in place,
    /// so a predicate that flows around is never resolved out from under a
    /// hash key.
    ///
    /// **Rewriting predicates in a pass? Do not assign a freshly-built `Rc`
    /// here per occurrence.** One predicate term rides many type slots as a
    /// *shared* `Rc` (a comprehension's filtered domain appears on its source,
    /// map, cast, and consumer-contract types); rebuilding each occurrence
    /// independently splits that sharing, and while that's invisible to
    /// correctness it makes planning recompile one predicate once per
    /// occurrence — superlinearly, on nested comprehensions. Route rewrites
    /// through [`crate::ccl::ccl_utils::walk_refined_predicates_mut`] /
    /// [`crate::ccl::ccl_utils::PredMemo`], which preserve the sharing across a
    /// pass. Use [`Refinement::born`] only for a genuinely *new* predicate.
    /// Guarded by `tests/predicate_sharing.rs`.
    pub predicate: Rc<TypedExpr>,
}

/// Pointer identity of a refinement's predicate term.
///
/// Traversals that descend into refinement predicates use this as a
/// visited-set key to avoid re-walking a predicate term shared by `Rc` across
/// several occurrences (the term graph is a DAG — immutable `Rc<TypedExpr>`
/// cannot form a cycle). It identifies *this very `Rc`*, unlike
/// [`Refinement`]'s structural `PartialEq`, and costs nothing to compute.
/// Only meaningful while the `Rc` is alive — hold it no longer than a
/// traversal over a tree that owns the `Rc`s (a freed address can be reused).
pub type PredicateId = *const TypedExpr;

/// The single reserved binder every [`Refinement`] implicitly introduces. It
/// is free in a refinement's predicate and ranges over the refined base type.
/// Disjoint from user identifiers by construction (lowering never produces
/// it); nested refinements share it and shadow positionally.
pub const REFINEMENT_BINDER: &str = "__elem";

impl Refinement {
    /// Construct a refinement over a **genuinely new** predicate term — one this
    /// call site is *creating*, with no prior refinement identity to preserve
    /// (a freshly-emitted filter, a synthesized loop-join condition, a compiled
    /// predicate). Prefer this to a `Refinement { predicate }` literal so the
    /// intent is legible: `born` is *wrong* for a **rewrite** of an existing
    /// predicate, which must instead flow through
    /// [`crate::ccl::ccl_utils::PredMemo`] to keep occurrences that shared one
    /// `Rc` sharing one `Rc` (see the note on [`Refinement::predicate`]).
    pub fn born(predicate: Rc<TypedExpr>) -> Self {
        Refinement { predicate }
    }

    /// Construct a refinement **deliberately sharing** an existing predicate
    /// term: a second occurrence of *the same* refinement, in another type slot.
    /// This is what lowering does when one filtered domain rides a source, a map,
    /// a cast target, and a consumer contract — one allocation, several slots —
    /// and it is the sharing every rebuilding pass then has to preserve.
    ///
    /// Distinct from [`born`](Self::born) in intent, not mechanism: `born` says
    /// "this predicate did not exist before", this says "this predicate already
    /// exists and I mean to alias it". Together they are the only two spellings —
    /// a `Refinement { predicate }` literal states neither.
    pub fn sharing(predicate: &Rc<TypedExpr>) -> Self {
        Refinement::born(Rc::clone(predicate))
    }

    /// The [`PredicateId`] of this refinement's predicate term.
    pub fn predicate_id(&self) -> PredicateId {
        Rc::as_ptr(&self.predicate)
    }
}

impl PartialEq for Refinement {
    /// Two refinements match iff they carry structurally equal predicate
    /// *terms* ([`eq_refinement_predicate`]). Structural equality makes
    /// refinement-bearing `Type`/`Expr` equality agnostic to *where* a
    /// predicate was constructed, so a `{D | p}` that join planning
    /// re-minted at a marker (`make_iterate` / `make_restrict` /
    /// `refine_with`) compares equal to its structural twin — which is what
    /// lets the post-planning `typecheck` chain the re-minted refinements. This
    /// is *equality*, not implication — `{T | p}` and `{T | q}` with
    /// structurally-distinct predicates remain unequal.
    ///
    /// The comparison is **type-blind**: a predicate's embedded `Type`s are
    /// inference metadata, so copies of one predicate — freshened for a
    /// specialization, rebuilt by a discharge, pinned at different use types —
    /// denote the same refinement while their type slots differ. Comparing the
    /// term and skipping the types keeps those copies equal, exactly as the
    /// [`Hash`](std::hash::Hash) impl keeps them hash-equal.
    ///
    /// Every refinement binds the same reserved [`REFINEMENT_BINDER`], so
    /// equality is plain structural equality of the bare predicate — the
    /// binder appears identically on both sides, with no α-renaming to do.
    ///
    /// Pointer-equal predicates short-circuit: a refinement that merely flows
    /// around (a vacuous substitution) keeps sharing its predicate `Rc`, so
    /// the common case never compares structure.
    fn eq(&self, other: &Self) -> bool {
        if Rc::ptr_eq(&self.predicate, &other.predicate) {
            return true;
        }

        eq_refinement_predicate(&self.predicate, &other.predicate)
    }
}

impl Eq for Refinement {}

/// The **"same-restriction" relation** on refinement predicate terms: the
/// equality that backs [`Refinement`] and the counterpart of
/// [`hash_refinement_predicate`]. It is *deliberately* type-blind — it compares
/// node shape, scalar leaves (operators, builtins, literals, names, tags),
/// binder names, and child `Expr`s pairwise, but never the embedded `Type`s
/// (`ty` slots, annotations, binding types). Those are inference metadata, not
/// part of what restriction a refinement imposes, and copies of one predicate
/// legitimately differ in them (freshened for a specialization, rebuilt by a
/// discharge, pinned at different use types). So this is a structural relation
/// chosen for its context, not an approximation of a finer one — there is no
/// plan to make it a derived `==` (which would wrongly compare those slots).
///
/// Binder names compare by equality, which coincides with α-equivalence under
/// the Barendregt convention (uniquified, globally-distinct binders; copies
/// preserve uids). Should a future pass need to compare predicates whose bound
/// binders were independently minted, this is the site to make α-aware (thread
/// a binder correspondence) rather than chase global name determinism.
///
/// One type-anchored slot **is** compared: a [`TypedExprNode::Cast`]'s
/// `target` carries the cast's domain-refinement *predicate term*
/// ([`ccl_utils::cast_target_refinement`]) — a semantic filter, not inference
/// metadata. Two predicates that each contain a cast and differ only in the
/// nested filter (e.g. embedded comprehensions filtering `> 0` vs `< 0`)
/// denote different refinements; conflating them would let refinement-deficit
/// matching accept an unsatisfied demand and refinement dedup drop a runtime
/// `Restrict`. The target's *base* types are still skipped. The recursion
/// terminates on tree shape alone: a predicate is an immutable `Rc<TypedExpr>`,
/// which is acyclic, so cast targets cannot cycle back into a term under
/// comparison — no coinduction guard is needed.
///
/// Everything this distinguishes beyond [`hash_refinement_predicate`]'s
/// stream (binder names, `Source` names, record field names, pattern tags,
/// cast-target predicates) makes eq finer than hash, preserving the
/// `Eq`/`Hash` contract.
pub(crate) fn eq_refinement_predicate(a: &TypedExpr, b: &TypedExpr) -> bool {
    eq_refinement_predicate_go(a, b)
}

/// Compare two cast targets' domain-refinement predicates term-wise (see
/// [`eq_refinement_predicate`]). Pointer-equal predicates short-circuit;
/// otherwise the comparison recurses structurally (acyclic terms, so it
/// terminates without a cycle guard).
fn eq_cast_target_predicates(t1: &Type, t2: &Type) -> bool {
    match (
        ccl_utils::cast_target_refinement(t1),
        ccl_utils::cast_target_refinement(t2),
    ) {
        (None, None) => true,
        (Some(r1), Some(r2)) => {
            if Rc::ptr_eq(&r1.predicate, &r2.predicate) {
                return true;
            }
            eq_refinement_predicate_go(&r1.predicate, &r2.predicate)
        }
        _ => false,
    }
}

/// Recursive worker for [`eq_refinement_predicate`].
fn eq_refinement_predicate_go(a: &TypedExpr, b: &TypedExpr) -> bool {
    use TypedExprNode as N;
    fn all_eq(xs: &[TypedExpr], ys: &[TypedExpr]) -> bool {
        xs.len() == ys.len()
            && xs
                .iter()
                .zip(ys)
                .all(|(x, y)| eq_refinement_predicate_go(x, y))
    }
    match (&a.node, &b.node) {
        (N::Lit(x), N::Lit(y)) => x == y,
        (N::Var(x), N::Var(y)) => x == y,
        (N::Builtin(x), N::Builtin(y)) => x == y,
        (N::Proj(x), N::Proj(y)) => x == y,
        (N::Source(x), N::Source(y)) => x == y,
        (N::Defer, N::Defer) | (N::Error, N::Error) => true,
        (
            N::Apply {
                function: f1,
                argument: a1,
            },
            N::Apply {
                function: f2,
                argument: a2,
            },
        ) => eq_refinement_predicate_go(f1, f2) && eq_refinement_predicate_go(a1, a2),
        (
            N::Cast {
                value: v1,
                target: t1,
            },
            N::Cast {
                value: v2,
                target: t2,
            },
        ) => eq_refinement_predicate_go(v1, v2) && eq_cast_target_predicates(t1, t2),
        (
            N::BinOp {
                left: l1,
                op: o1,
                right: r1,
            },
            N::BinOp {
                left: l2,
                op: o2,
                right: r2,
            },
        ) => o1 == o2 && eq_refinement_predicate_go(l1, l2) && eq_refinement_predicate_go(r1, r2),
        (N::UnaryOp(k1, e1), N::UnaryOp(k2, e2)) => k1 == k2 && eq_refinement_predicate_go(e1, e2),
        (
            N::Lambda {
                param: p1,
                body: b1,
                ..
            },
            N::Lambda {
                param: p2,
                body: b2,
                ..
            },
        ) => p1.name == p2.name && eq_refinement_predicate_go(b1, b2),
        (
            N::Aggregate {
                input: i1,
                kind: k1,
            },
            N::Aggregate {
                input: i2,
                kind: k2,
            },
        ) => k1 == k2 && eq_refinement_predicate_go(i1, i2),
        (
            N::Let {
                binding: bd1,
                bound_expr: e1,
                body: b1,
            },
            N::Let {
                binding: bd2,
                bound_expr: e2,
                body: b2,
            },
        ) => {
            bd1.name == bd2.name
                && eq_refinement_predicate_go(e1, e2)
                && eq_refinement_predicate_go(b1, b2)
        }
        (N::List(x), N::List(y))
        | (N::Tuple(x), N::Tuple(y))
        | (N::Compose(x), N::Compose(y))
        | (N::Copair(x), N::Copair(y))
        | (N::DisjointJoin(x), N::DisjointJoin(y)) => all_eq(x, y),
        (
            N::Case {
                scrutinee: s1,
                branches: br1,
            },
            N::Case {
                scrutinee: s2,
                branches: br2,
            },
        ) => {
            let scrutinee_eq = match (s1, s2) {
                (None, None) => true,
                (Some(x), Some(y)) => eq_refinement_predicate_go(x, y),
                _ => false,
            };
            scrutinee_eq
                && br1.len() == br2.len()
                && br1.iter().zip(br2).all(|(x, y)| {
                    let pattern_eq = match (&x.pattern, &y.pattern) {
                        (None, None) => true,
                        (Some(p), Some(q)) => p.tag == q.tag && p.binding.name == q.binding.name,
                        _ => false,
                    };
                    pattern_eq
                        && eq_refinement_predicate_go(&x.guard, &y.guard)
                        && eq_refinement_predicate_go(&x.body, &y.body)
                })
        }
        (
            N::VariantCtor {
                tag: t1,
                payload: p1,
            },
            N::VariantCtor {
                tag: t2,
                payload: p2,
            },
        ) => t1 == t2 && eq_refinement_predicate_go(p1, p2),
        (N::Record(f1), N::Record(f2)) => {
            f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2)
                    .all(|((n1, e1), (n2, e2))| n1 == n2 && eq_refinement_predicate_go(e1, e2))
        }
        (N::ExprStmt { expr: e1, body: b1 }, N::ExprStmt { expr: e2, body: b2 }) => {
            eq_refinement_predicate_go(e1, e2) && eq_refinement_predicate_go(b1, b2)
        }
        (
            N::Feed {
                name: n1,
                value: v1,
            },
            N::Feed {
                name: n2,
                value: v2,
            },
        )
        | (
            N::Define {
                name: n1,
                value: v1,
            },
            N::Define {
                name: n2,
                value: v2,
            },
        ) => n1 == n2 && eq_refinement_predicate_go(v1, v2),
        _ => false,
    }
}

/// Structural hash of a refinement predicate, the hashing counterpart of
/// [`eq_refinement_predicate`]: it hashes the predicate's node discriminant
/// and scalar leaves (operators, builtins, literals, names) and recurses
/// into child `Expr`s, but never hashes the embedded `Type`s. Skipping
/// types keeps the hash stable while inference resolves the predicate's
/// type slots in place, and keeps it non-recursive through refinements (so
/// it always terminates and adds no extra borrows).
fn hash_refinement_predicate<H: std::hash::Hasher>(e: &TypedExpr, state: &mut H) {
    use std::hash::Hash;
    std::mem::discriminant(&e.node).hash(state);
    match &e.node {
        TypedExprNode::Lit(Lit::Int(n)) => n.hash(state),
        TypedExprNode::Lit(Lit::String(s)) => s.hash(state),
        TypedExprNode::Lit(Lit::Bool(b)) => b.hash(state),
        TypedExprNode::Lit(Lit::Unit) => {}
        TypedExprNode::Var(name) => name.hash(state),
        TypedExprNode::Builtin(b) => b.hash(state),
        TypedExprNode::BinOp { op, .. } => op.hash(state),
        TypedExprNode::UnaryOp(kind, _) => kind.hash(state),
        TypedExprNode::Aggregate { kind, .. } => kind.hash(state),
        TypedExprNode::VariantCtor { tag, .. } => tag.hash(state),
        TypedExprNode::Proj(ProjKey::Index(i)) => i.hash(state),
        TypedExprNode::Proj(ProjKey::Field(f)) => f.hash(state),
        _ => {}
    }
    e.walk_children(|child| hash_refinement_predicate(child, state));
}

impl std::hash::Hash for Refinement {
    /// Hashes the predicate's *structure* (refined `Type`s are hashed as
    /// `ConstrainCache` keys). [`hash_refinement_predicate`] hashes the
    /// predicate's node shape and scalar leaves but skips embedded `Type`s,
    /// so the hash is stable even though a refinement's twin may carry
    /// differently-resolved type slots; `==` ([`eq_refinement_predicate`]) is
    /// the matching type-blind relation, finer only by leaves the hash skips,
    /// which keeps the `Eq`/`Hash` contract. The predicate is immutable, so a
    /// `Type` used as a `ConstrainCache` key never re-hashes differently.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        hash_refinement_predicate(&self.predicate, state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BinOpKind, CompareKind};

    /// Two predicates that each contain a [`TypedExprNode::Cast`] and differ
    /// only in the *target's* domain-refinement predicate denote different
    /// refinements: the nested filter is semantic, not inference metadata, so
    /// [`eq_refinement_predicate`] must compare cast targets rather than skip
    /// them as type slots (conflating them could drop a runtime `Restrict`).
    #[test]
    fn refinement_eq_distinguishes_cast_target_predicates() {
        let filter = |op: CompareKind| {
            TypedExpr::binop(
                TypedExpr::var("x"),
                BinOpKind::Compare(op),
                TypedExpr::lit(Lit::Int(0)),
            )
        };
        let cast_pred = |op: CompareKind| {
            TypedExpr::cast(
                TypedExpr::var("xs"),
                ccl_utils::refined_data_fun(Type::Hole, filter(op), Type::Hole),
            )
        };
        let refinement = |pred: TypedExpr| Refinement::born(Rc::new(pred));

        let gt = refinement(cast_pred(CompareKind::Greater));
        let gt_twin = refinement(cast_pred(CompareKind::Greater));
        let lt = refinement(cast_pred(CompareKind::Less));

        assert_eq!(
            gt, gt_twin,
            "casts with structurally equal target predicates are one refinement"
        );
        assert_ne!(
            gt, lt,
            "casts differing only in the target's nested filter are distinct refinements"
        );
    }

    /// A shape test looks *through* a refinement: a refined mutable variable is still
    /// one and a refined channel is still a channel. Nothing in the pipeline
    /// wraps a handle today — a handle type is built structurally rather than
    /// resolved from a variable, so no position accumulates a refinement onto one — which
    /// is exactly why the rule needs stating here: it is the accessors' contract,
    /// not a shape a program can be written to exercise.
    #[test]
    fn handle_accessors_see_through_a_refinement() {
        let refinement = Refinement::born(Rc::new(TypedExpr::lit(Lit::Bool(true))));
        let refine = |t: Type| Type::Refinement(Box::new(t), refinement.clone());
        let int = Type::Base(BaseType::Int);
        let mut_var = Type::History {
            value: Box::new(int.clone()),
            domain: Box::new(Type::Txn),
            kind: HistoryKind::Overwrite,
        };
        let channel = Type::History {
            value: Box::new(int.clone()),
            domain: Box::new(Type::UIntRange(3)),
            kind: HistoryKind::Append,
        };

        assert_eq!(refine(mut_var.clone()).mut_value_type(), Some(&int));
        assert_eq!(
            refine(channel.clone()).as_feed(),
            Some((&Type::UIntRange(3), &int))
        );
        assert!(refine(mut_var).is_handle() && refine(channel.clone()).is_handle());

        // The two kinds are not interchangeable: a channel reads as its whole
        // stream, a mutable variable as one value, so neither accessor answers for the other.
        assert_eq!(channel.mut_value_type(), None);
        assert_eq!(
            Type::History {
                value: Box::new(int.clone()),
                domain: Box::new(Type::Txn),
                kind: HistoryKind::Overwrite,
            }
            .as_feed(),
            None
        );

        // A refined *non*-handle peels to a non-handle, which is the case every
        // caller of these accessors actually hits (`x = 0; x += 1`).
        assert_eq!(refine(int).mut_value_type(), None);
    }

    /// The transaction-commit domain renders by its bare name (mirrors the
    /// prototype's `CommitTime` Display), including as a function domain.
    #[test]
    fn txn_type_display() {
        assert_eq!(Type::Txn.to_string(), "Txn");
        assert_eq!(
            Type::fun(Type::Txn, Type::Base(BaseType::Int)).to_string(),
            "(Txn ⇒ Int)"
        );
    }

    /// A tagged sum renders in CHL's surface syntax: braces around the arms,
    /// each arm introduced by a backtick, its stored type in braces of its own.
    ///
    /// Three rules, all visible here. A `Unit` payload is the **nullary**
    /// constructor and renders bare — "stores nothing" is the whole content, so
    /// `` `abort{Unit} `` would spell an absence as a presence. A payload that
    /// already renders brace-delimited **reuses** those braces, which is what
    /// makes a record arm read `` `pair{a: Int, b: Int} ``. And a single-arm sum
    /// is not special-cased: it is just the general form with one arm.
    #[test]
    fn variant_type_display_is_surface_syntax() {
        let commit_abort = Type::variant(vec![
            (FieldKey::Name("commit".into()), Type::Base(BaseType::Int)),
            (FieldKey::Name("abort".into()), Type::Base(BaseType::Unit)),
        ]);
        assert_eq!(commit_abort.to_string(), "{`commit{Int} | `abort}");

        // Single arm, with and without a stored type.
        assert_eq!(
            Type::variant(vec![(
                FieldKey::Name("none".into()),
                Type::Base(BaseType::Unit)
            )])
            .to_string(),
            "{`none}"
        );
        assert_eq!(
            Type::variant(vec![(
                FieldKey::Name("some".into()),
                Type::Base(BaseType::Int)
            )])
            .to_string(),
            "{`some{Int}}"
        );

        // A record payload's braces are the arm's braces.
        let record = Type::Record(vec![
            ("a".to_string(), Type::Base(BaseType::Int)),
            ("b".to_string(), Type::Base(BaseType::Int)),
        ]);
        assert_eq!(
            Type::variant(vec![(FieldKey::Name("pair".into()), record)]).to_string(),
            "{`pair{a: Int, b: Int}}"
        );
    }

    /// An **anonymous positional** sum is not a tagged variant and keeps its own
    /// rendering: `++`/`Copair` produces `Index` keys that carry no
    /// user-meaningful information, so the arms print as a flat `A | B` join
    /// rather than being dressed up as surface arms nobody wrote.
    #[test]
    fn anonymous_positional_sum_still_renders_as_a_flat_join() {
        let anon = Type::variant(vec![
            (FieldKey::Index(0), Type::Base(BaseType::Int)),
            (FieldKey::Index(1), Type::Base(BaseType::String)),
        ]);
        assert_eq!(anon.to_string(), "Int | String");
    }

    // ----- TagMap -----

    fn name(s: &str) -> FieldKey {
        FieldKey::Name(s.into())
    }

    /// Arms land in canonical key order regardless of insertion order, so
    /// structural equality coincides with "same tags, same arms".
    #[test]
    fn tag_map_is_canonically_ordered() {
        let a = TagMap::from_arms(vec![(name("some"), 1), (name("none"), 2)]);
        let b = TagMap::from_arms(vec![(name("none"), 2), (name("some"), 1)]);
        assert_eq!(a, b, "insertion order must not be observable");
        assert_eq!(
            a.keys().cloned().collect::<Vec<_>>(),
            vec![name("none"), name("some")],
            "keys iterate in canonical order"
        );
    }

    /// Lookup is by tag, and an absent tag is `None` rather than an error —
    /// that is the width-subtyping case (the producer never emits it).
    #[test]
    fn tag_map_absent_tag_is_none_not_an_error() {
        let m = TagMap::from_arms(vec![(name("some"), 7)]);
        assert_eq!(m.get(&name("some")), Some(&7));
        assert_eq!(m.get(&name("none")), None);
        assert_eq!(m.position(&name("none")), None);
    }

    /// A tag's position depends on its own map's key set — the reason positions
    /// must never be compared across two sums.
    #[test]
    fn tag_map_position_is_relative_to_its_own_key_set() {
        let narrow = TagMap::from_arms(vec![(name("b"), ())]);
        let wide = TagMap::from_arms(vec![(name("a"), ()), (name("b"), ())]);
        assert_eq!(narrow.position(&name("b")), Some(0));
        assert_eq!(wide.position(&name("b")), Some(1));
    }

    /// Positional sums are the `Index`-keyed case of the same structure, and
    /// their keys sort numerically rather than lexicographically.
    #[test]
    fn tag_map_indexed_keys_sort_numerically() {
        let m = TagMap::from_arms((0..12).rev().map(|i| (FieldKey::Index(i), i)).collect());
        assert_eq!(
            m.keys().cloned().collect::<Vec<_>>(),
            (0..12).map(FieldKey::Index).collect::<Vec<_>>()
        );
        assert_eq!(m.position(&FieldKey::Index(10)), Some(10));
    }

    /// `zip_matching` pairs by tag, so two sums with different tag sets cannot
    /// be silently mispaired the way zipping two arm vectors would.
    #[test]
    fn tag_map_zip_matching_pairs_by_tag() {
        let l = TagMap::from_arms(vec![(name("a"), 1), (name("b"), 2)]);
        let r = TagMap::from_arms(vec![(name("b"), 20), (name("c"), 30)]);
        let paired: Vec<_> = l
            .zip_matching(&r)
            .map(|(k, a, b)| (k.clone(), *a, *b))
            .collect();
        assert_eq!(paired, vec![(name("b"), 2, 20)], "only shared tags pair");
        assert!(!l.same_tags(&r));
        assert!(l.same_tags(&TagMap::from_arms(vec![(name("b"), ()), (name("a"), ())])));
    }

    #[test]
    #[should_panic(expected = "duplicate tag")]
    fn tag_map_rejects_duplicate_tags() {
        let _ = TagMap::from_arms(vec![(name("a"), 1), (name("a"), 2)]);
    }

    /// `zip_same_tags` lifts a binary operation pointwise, pairing by tag and not
    /// by position — so it stays correct when the two maps' canonical orders would
    /// have mispaired arms had they been zipped as vectors.
    #[test]
    fn tag_map_zip_same_tags_is_pointwise_by_tag() {
        let l = TagMap::from_arms(vec![(name("a"), 1), (name("b"), 2)]);
        let r = TagMap::from_arms(vec![(name("b"), 20), (name("a"), 10)]);
        let combined = l.zip_same_tags(&r, "test", |x, y| x + y);
        assert_eq!(
            combined,
            TagMap::from_arms(vec![(name("a"), 11), (name("b"), 22)])
        );
    }

    /// A missing arm has nothing to combine with, so it is a caller bug rather than
    /// a case to absorb — unlike [`TagMap::zip_matching`], which skips it, and
    /// unlike a *query* over two sums, which can answer conservatively.
    #[test]
    #[should_panic(expected = "arm sets differ")]
    fn tag_map_zip_same_tags_rejects_differing_arm_sets() {
        let l = TagMap::from_arms(vec![(name("a"), 1), (name("b"), 2)]);
        let r = TagMap::from_arms(vec![(name("a"), 10)]);
        let _ = l.zip_same_tags(&r, "test", |x, y| x + y);
    }

    /// A dependent arrow's claim *stores* an index and *reads* as the binder's
    /// name, detached from the arrow or not. Two spellings, two mechanisms: a
    /// rendering that holds the arrow reads its name slot, and one that does
    /// not falls back to the reference's own hint. Identity is the index in
    /// both cases, which is what the assertion on the term checks.
    #[test]
    fn a_dependent_arrow_renders_its_binder_by_name() {
        let k = crate::ccl::Name::raw("k");
        let refinement = Type::Refinement(
            Box::new(Type::Base(BaseType::Int)),
            Refinement::born(Rc::new(TypedExpr::binop(
                TypedExpr::var(crate::ccl::Name::elem()),
                BinOpKind::Compare(CompareKind::Equals),
                TypedExpr::var(k.clone()),
            ))),
        );
        let ty = Type::pi(k.clone(), Type::Base(BaseType::Int), refinement);
        assert_eq!(ty.to_string(), "((k: Int) ⇒ {Int | __elem == k})");

        // Detached from the arrow, the reference still reads as the binder —
        // now off its own hint rather than off the arrow's name slot. A bare
        // `#0` in a diagnostic tells a reader nothing, and a fragment plucked
        // out of a half-assembled arrow is exactly what a diagnostic blames.
        let Type::Fun { codomain, .. } = &ty else {
            panic!("expected an arrow");
        };
        assert_eq!(codomain.to_string(), "{Int | __elem == k}");

        // Stored, though, it is the index: the spelling is metadata that
        // identity ignores, so the refinement is α-canonical.
        let Type::Refinement(_, r) = &**codomain else {
            panic!("expected the refinement");
        };
        let TypedExprNode::BinOp { right, .. } = &r.predicate.node else {
            panic!("expected the dependent refinement");
        };
        let TypedExprNode::Var(reference) = &right.node else {
            panic!("expected a variable reference");
        };
        assert_eq!(reference.pi_bound_index(), Some(0));
        assert_eq!(
            *reference,
            crate::ccl::Name::pi_bound_bare(0),
            "the hint does not participate in identity"
        );
    }

    /// The index counts arrow crossings, so an unnamed arrow between the
    /// reference and its binder occupies an environment entry: dropping it
    /// would resolve the reference to the wrong binder.
    #[test]
    fn an_unnamed_crossing_still_counts_when_rendering() {
        let refinement = Type::Refinement(
            Box::new(Type::Base(BaseType::Int)),
            Refinement::born(Rc::new(TypedExpr::var(crate::ccl::Name::pi_bound_bare(1)))),
        );
        // (k: Int) ⇒ (Int ⇒ {Int | #1}) — one unnamed crossing in between.
        let ty = Type::Fun {
            name: Some(crate::ccl::Name::raw("k")),
            kind: FunKind::Compute,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::fun(Type::Base(BaseType::Int), refinement)),
        };
        assert_eq!(ty.to_string(), "((k: Int) ⇒ (Int ⇒ {Int | k}))");
    }
}

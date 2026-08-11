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

/// Whether a [`Type::Fun`]'s domain is a **capability** or a **collection** — the
/// compute-function vs data-function distinction.
///
/// - [`FunKind::Compute`] — `α ⇒ β`: the domain is a *capability*, the inputs
///   the function accepts. No data sits behind it, so shrinking the domain only
///   under-promises; the contravariant meet at a control-flow join is a sound,
///   lossy simplification.
/// - [`FunKind::Data`] — `α ⤇ β`: the domain is a *collection*'s index set.
///   The domain *is* the data map, so a lossy domain is lost data;
///   joins of data functions must be lossless — never a meet. Two collections over
///   genuinely distinct domains have no common type at all; the sum that keeps both is
///   entered by `box`, a term ([`Builtin::Box`](crate::ccl::Builtin)), not by the join.
///
/// Set at introduction (list literals, comprehensions, `++`, registered
/// sources, and every `History` erasure are `Data`; `lambda`/`def` are
/// `Compute`). The audit rule for a rebuilt or erased arrow: it is `Data` iff
/// `extent_of` will drive iteration off its domain. See
/// `design/type-inference.md`,
/// "4.6 Data vs compute functions and conditional-collection domain joins".
///
/// FunKind is **inferred** (see `design/type-inference.md`,
/// "4.6 Data vs compute functions and conditional-collection domain joins"):
/// where the structure fixes it (a list literal is `Data`, a scalar op is
/// `Compute`) a concrete kind is stamped; where it depends on use or on an
/// unresolved source (a map/comprehension) a [`FunKind::Var`] is minted and the
/// solver resolves it, like a type variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunKind {
    /// domain (`⇒`): lossy meet at a join is fine.
    Compute,
    /// domain (`⤇`): the domain is data; joins must be lossless.
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

/// Bounds on a [`FunKindVar`], over the two-point kind lattice `Data ⊑ Compute`.
///
/// The lattice has only two points, so "bounds" collapse to two flags rather
/// than the polar bound *lists* an [`crate::ccl::InferVar`] carries — and no
/// [`Type`] sits inside, so a `FunKindVar` never forms a cycle. Resolution is a
/// flag read: `forced_compute ∧ forced_data` is the conflict (`Compute ⊑ κ ⊑
/// Data`, impossible — the `Compute <: Data` rejection); `forced_compute` alone
/// → `Compute`; `forced_data` alone → `Data`; neither → the caller's
/// domain-derived default.
#[derive(Debug, Default, Clone, Copy)]
pub struct FunKindBounds {
    /// A `Compute` value flows *into* this kind (`κ ⊒ Compute ⟹ κ = Compute`).
    pub forced_compute: bool,
    /// This kind is *demanded* as `Data` (`κ ⊑ Data ⟹ κ = Data`).
    pub forced_data: bool,
}

/// A kind-inference variable — an unknown [`FunKind`] the solver pins down by
/// accumulating [`FunKindBounds`]. Identity (`uid`) is immutable and lives outside
/// the `RefCell`, so equality/hashing is borrow-free and never inspects the
/// bounds (mirroring [`crate::ccl::InferVar`]).
pub struct FunKindVar {
    /// Stable, globally-unique identity.
    pub uid: FunKindVarId,
    /// Mutable kind bounds.
    pub bounds: RefCell<FunKindBounds>,
    /// Vars `u` such that `self <: u` (this kind is below them). A `Compute`
    /// force propagates *up* to them (`self = Compute ⟹ u = Compute`).
    uppers: RefCell<Vec<Rc<FunKindVar>>>,
    /// Vars `l` such that `l <: self` (this kind is above them). A `Data` force
    /// propagates *down* to them (`self = Data ⟹ l = Data`).
    lowers: RefCell<Vec<Rc<FunKindVar>>>,
}

impl FunKindVar {
    /// Allocate a fresh kind variable with empty bounds and no links.
    pub fn fresh() -> Rc<FunKindVar> {
        Rc::new(FunKindVar {
            uid: FunKindVarId(FUN_KIND_VAR_COUNTER.fetch_add(1, Ordering::Relaxed)),
            bounds: RefCell::new(FunKindBounds::default()),
            uppers: RefCell::new(Vec::new()),
            lowers: RefCell::new(Vec::new()),
        })
    }

    /// Force this kind to `Compute` and propagate transitively up the `<:` links.
    ///
    /// Propagation keeps the flags at a fixpoint *incrementally*, so — unlike a
    /// one-shot copy of the flags present when a link is first drawn — a force
    /// that arrives strictly after its link still reaches every var it must. The
    /// monotone flag (false → true) both terminates the walk and makes it
    /// cycle-safe: a var already `Compute` short-circuits before recursing.
    pub fn force_compute(self: &Rc<Self>) {
        if self.bounds.borrow().forced_compute {
            return;
        }
        self.bounds.borrow_mut().forced_compute = true;
        for u in self.uppers.borrow().iter() {
            u.force_compute();
        }
    }

    /// Force this kind to `Data` and propagate transitively down the `<:` links.
    /// The dual of [`FunKindVar::force_compute`]; same fixpoint/termination argument.
    pub fn force_data(self: &Rc<Self>) {
        if self.bounds.borrow().forced_data {
            return;
        }
        self.bounds.borrow_mut().forced_data = true;
        for l in self.lowers.borrow().iter() {
            l.force_data();
        }
    }

    /// A snapshot `(uppers, lowers)` of this var's `<:` links. Freshening uses
    /// it to mirror def-site links onto the per-instantiation copies — the flags
    /// alone are not enough, since a force arriving *after* instantiation must
    /// still traverse the link to the sibling instantiation.
    pub fn links(&self) -> (Vec<Rc<FunKindVar>>, Vec<Rc<FunKindVar>>) {
        (self.uppers.borrow().clone(), self.lowers.borrow().clone())
    }

    /// Record the edge `lower <: upper` and reconcile the flags already present
    /// on either end. Later forces on either var propagate through the stored
    /// link via [`FunKindVar::force_compute`]/[`FunKindVar::force_data`].
    pub fn link(lower: &Rc<FunKindVar>, upper: &Rc<FunKindVar>) {
        if Rc::ptr_eq(lower, upper) {
            return;
        }
        lower.uppers.borrow_mut().push(Rc::clone(upper));
        upper.lowers.borrow_mut().push(Rc::clone(lower));
        if lower.bounds.borrow().forced_compute {
            upper.force_compute();
        }
        if upper.bounds.borrow().forced_data {
            lower.force_data();
        }
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
    /// non-dependent arrow `domain ⇒ codomain`. When `name` is `Some(x)` it
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
        /// Whether this function is a capability (`Compute`) or a data collection
        /// (`Data`). See [`FunKind`]. The derived [`PartialEq`] compares it: a
        /// data function and a compute function over the same domain/codomain
        /// are genuinely different types (one carries data, one a capability).
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
    Variant(Vec<(FieldKey, Type)>),
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
    /// Either way it is **invariant** in both children (a history flowing
    /// through a function parameter both reads and writes), and it is a
    /// **transient** variant like `Hole` / `Infer`: it exists only between type
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
    /// A **dependent sum** `Σ (witness). body`: a value pairing a witness with a
    /// body whose type may depend on it. A **conditional collection** (the
    /// lossless join of data functions at a control-flow merge) is the finite
    /// instance — the witness is a type ranging over the branches' candidate
    /// domains ([`TypeKind::Enumerated`]) and the body is `WitnessRef ⤇ V`. The other
    /// instances differ only in their witness *kind*: [`TypeKind::UIntRanges`] for a
    /// `List` (every index range) and [`TypeKind::Any`] for `Collection[T]` (the
    /// whole universe).
    ///
    /// **Entered** only by a term — [`Builtin::Box`](crate::ccl::Builtin) or a keyed
    /// entry builtin — never by a demand: there is no `𝑇 <: Σ` subtyping arm, so
    /// nothing ever flows *into* a sum. Joining sums does form one, which is a different
    /// thing: its candidates are the joined sums', so it introduces nothing that was not
    /// already introduced. See `src/ccl/design/type-inference.md`, "Only a term builds a sum".
    ///
    /// Consumed as a subtype, which *names* the witness rather than presenting a
    /// domain for it: the consumer is typed under a reference to the sum's own binder and
    /// its result closed back over that name, so a domain-preserving consumer keeps the sum
    /// and a witness-independent one (an aggregate) loses it. See
    /// `src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness".
    ///
    /// **Durable, not transient.** A program can hold one: `box(xs)`'s type carries a
    /// sum through inference and `lambda_elim` and into planning, where realization
    /// performs the finite-Σ ≡ gated-union isomorphism and erases it. A sum whose
    /// witness kind *describes* its domains cannot be realized that way and is rejected
    /// by name at op-conversion.
    Sigma(Box<SigmaType>),
    /// A **type-level reference to a Sigma's type-witness** — the witness in *domain*
    /// position, e.g. the body `WitnessRef ⤇ V` of a conditional collection.
    ///
    /// It **names the binder it belongs to** ([`SigmaType::binder`]), for the same reason
    /// a Pi binder is a `Name`: when a pass decomposes a Σ-typed term the occurrences
    /// scatter across the pieces, and which binder they belong to has to survive that.
    /// Identity by nesting position cannot — position is exactly what decomposition
    /// destroys.
    ///
    /// **Every** witness is referenced this way, bound or free, exactly as a Pi binder's
    /// occurrences are one `Var` whether the lambda binding them is in the type or outside
    /// it. Which one it is, is a question about *scope* and is asked where it matters:
    /// compaction threads the binders it has descended through and sorts an occurrence into
    /// an atom (bound) or the witness slot (free, awaiting its close); the coalesced-type
    /// check asks the same question as well-formedness.
    ///
    /// The range lives on the **binder**, not here — a reference names a binder, and the
    /// binder is what has a range ([`witness_ctx`]). So this leaf carries identity alone.
    ///
    /// **Not transient.** It is bound by its Σ and is exactly as durable as that Σ, which
    /// since `box` is an ordinary type a program can hold: `box(xs)`'s type carries one
    /// through inference and `lambda_elim` and into planning. Two different things remove
    /// it, and neither is a discharge to a concrete domain by the type system:
    ///
    /// - **Elimination**, when a consumer opens the sum — the witness is discharged per
    ///   candidate, and the sum survives or collapses by whether the consumer's result
    ///   still mentions it.
    /// - **Realization** (`planning::conditionals`), which performs the finite-Σ ≡
    ///   gated-union isomorphism and erases the Σ and the `box` together. This is what
    ///   retires the ones a program merely *holds*, and it happens after the type system
    ///   is done.
    ///
    /// So none reaches op-conversion — but by realization, not by being short-lived. A Σ
    /// that does reach it (a described witness kind, which cannot be realized) is rejected
    /// there by name.
    ///
    /// Named for the *reference*, not the witness: the witness itself is the
    /// [`Witness`] slot on the Σ ([`SigmaType::witness`]), classified by a
    /// [`TypeKind`]. Two distinct things, and calling both "witness" is what forced
    /// every mention of this one to be qualified.
    WitnessRef(crate::ccl::infer_var::WitnessBinderId),
    // Planned:
    // Pi { param: String, param_ty: Box<Type>, body_ty: Box<Type> }
}

/// The payload of a [`Type::Sigma`] — a dependent sum `Σ (witness). body`.
/// Boxed inside `Type` to keep the enum small.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SigmaType {
    /// What the Sigma is summed over — a type (a domain), classified by a
    /// [`TypeKind`]. The kind also selects the eliminator.
    pub witness: Witness,
    /// The body `B(witness)` — an arbitrary type that may depend on the witness.
    /// The **conditional-collection** instance's body is the data function
    /// `WitnessRef ⤇ V` (the *factored* form, built by
    /// [`SigmaType::over`]); other Σ
    /// instances may have non-function bodies, so this stays a general `Type`.
    /// Code that reads a function body's parts (codomain, element binder) does so
    /// only where it already knows the instance is a conditional collection.
    pub body: Box<Type>,
}

/// A **witness**: a type (a domain) that a [`SigmaType`] is summed over, and the binder
/// its [`Type::WitnessRef`] occurrences name.
///
/// Both halves, in one value, deliberately. The **kind** describes the domains it ranges
/// over — a finite candidate set ([`TypeKind::Enumerated`]), every index range
/// ([`TypeKind::UIntRanges`]), or the whole universe ([`TypeKind::Any`]) — which is what
/// keeps Σ subtyping to a single rule (kind containment plus body subtyping) with no
/// per-witness-flavour cases. The **binder** is its identity, and it lives here rather
/// than on the sum because a kind travelling without one is how a witness acquires a
/// second name: a site holding only a kind must invent a binder to build a sum, and
/// inventing is right only when the witness is genuinely new.
///
/// So the operations are named for the question a caller has to answer. Deriving —
/// [`map_types`](Self::map_types), [`with_kind`](Self::with_kind) — carries the binder;
/// [`fresh`](Self::fresh) mints one and is the visible act of saying "this is a different
/// witness"; [`alpha_convert`](Self::alpha_convert) is the same witness renamed, which a
/// scheme instantiation owes each use.
///
/// It stays distinct from [`TypeKind`] itself: folding it in would make a Σ's witness
/// field *be* a kind, re-conflating "what the Σ is summed over" with the classifier
/// filling it — the collision the `WitnessRef` name exists to avoid.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Witness {
    /// What the witness ranges over.
    kind: TypeKind,
    /// Its binder — what the [`Type::WitnessRef`]s standing for it point at.
    ///
    /// Held **here**, beside the kind, rather than on the sum: a witness is one thing, and
    /// storing its two halves apart is what let them travel apart. Every site that
    /// mis-minted a binder had the kind in hand and no binder with it, so reattaching one
    /// was a decision each site made separately — and three of them made it wrong. With
    /// the halves together, carrying the identity is what happens by default and
    /// [`Witness::fresh`] is the visible act of not carrying it.
    binder: crate::ccl::infer_var::WitnessBinderId,
}

/// A **classifier of types** — which types it admits.
///
/// Used today only as the classifier of a Σ's type-witness ([`Witness`]), which is
/// the sole kind-carrying position in the grammar; since a Σ's witness is a data
/// function's domain, every type a kind classifies here happens to be a domain. That is
/// a fact about current usage, not part of the notion — nothing in
/// [`admits`](TypeKind::admits) or [`contains`](TypeKind::contains) is domain-specific.
///
/// Note the direction: a kind admits many types and a type is admitted by many kinds, so
/// there is no "kind of a type" to read off. What a type determines is the *minimal* kind
/// containing it, the singleton [`Enumerated`](TypeKind::Enumerated).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// A finite, explicitly **enumerated** set of candidate domains, in
    /// branch/contribution order (a tested contract). Statically enumerable →
    /// the value-`Case` fan-out. The conditional-collection case, the only one
    /// wired today.
    Enumerated(Vec<Type>),
    /// Every **`UIntRange`** — the kind that classifies a `List`'s domain. Not a finite
    /// candidate set (there is one range per length), and not a down-set of any
    /// single domain either: the down-set of a large range would admit *sparse*
    /// subsets, whereas membership here is exactly "is a `Type::UIntRange`", i.e. a
    /// dense prefix. That distinction is load-bearing — it is what stops a
    /// *filtered* range `{[0, k) | p}` (a `Refinement`, not a `UIntRange`) passing
    /// as a `List`, which would supply a length witness for a domain that has holes.
    UIntRanges,
    /// **Any** domain — the universe `*` (`Collection(T)`; not enumerable →
    /// an opaque domain). Type reserved; machinery lands with the collections
    /// work.
    Any,
}

/// The witness part of a `Σ… ⤇ V` rendering — listed candidates in braces, a
/// described kind by its own glyph.
impl fmt::Display for TypeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeKind::Enumerated(candidates) => {
                let cs: Vec<_> = candidates.iter().map(|t| t.to_string()).collect();
                write!(f, "{{{}}}", cs.join(", "))
            }
            TypeKind::UIntRanges => write!(f, "[..]"),
            TypeKind::Any => write!(f, "*"),
        }
    }
}

/// What is left to discharge for a kind containment to hold — the residue of
/// [`TypeKind::contains`], which reports the edge itself by returning `Some`.
///
/// Containment is not always self-contained: a candidate that is still a bare
/// inference **variable** has no shape for a membership predicate to read, and
/// "whatever this resolves to must inhabit 𝐾" is not expressible as a subtyping bound
/// — no type 𝑇 has `α <: 𝑇` iff `α` is a range. So it is recorded *as a kinding
/// constraint on the variable*, beside its bounds, and discharged when the variable
/// resolves.
///
/// Obligations are conjunctive: every entry must hold. None is polar — a kinding
/// constraint asserts something about a variable's eventual resolution, which is the
/// same fact at either position.
#[derive(Debug, Clone, Default)]
pub struct KindObligations {
    /// **Kinding** constraints `?𝑣 :: 𝐾` — a listed candidate that is still a bare
    /// variable, together with the described kind it must inhabit.
    pub kinds: Vec<(Rc<InferVar>, TypeKind)>,
    /// The **pairing** a listing-against-listing edge leaves open: `(subs, sups)`,
    /// discharged by finding, for *each* sub candidate, some sup candidate whose body
    /// edge it satisfies — the `∃` of the Σ-width rule.
    ///
    /// Handed back rather than decided because the per-pairing test is *subtyping*, and
    /// only the solver can run that. Set membership — every sub candidate appearing
    /// verbatim among the sups — is the `𝑒 = 𝑑` instance of the same search, which is
    /// what [`holds_structurally`](Self::holds_structurally) falls back to.
    pub pairing: Option<(Vec<Type>, Vec<Type>)>,
}

impl KindObligations {
    /// Whether every obligation already holds **as written**.
    ///
    /// This is the discharge available where there is no constraint graph to emit
    /// into: the compact-domain lattice, and the post-coalesce kinding check. A
    /// pending kinding constraint can never be discharged that way — a variable with
    /// no shape at either point is one that never resolved.
    ///
    /// A pairing is discharged by its **identity** instance — every sub candidate
    /// appearing verbatim among the sups. That is *sound* rather than complete: equality
    /// implies the body edge, so this can reject an edge the solver-side search would
    /// allow. Conservative is the right direction where there is no solver to search
    /// with.
    pub fn holds_structurally(&self) -> bool {
        self.kinds.is_empty()
            && self
                .pairing
                .as_ref()
                .is_none_or(|(subs, sups)| subs.iter().all(|d| sups.contains(d)))
    }
}

impl TypeKind {
    /// The domains this kind **lists**, or `None` when it *describes* them instead.
    ///
    /// This is the one place the listed/described split is decided. Every other
    /// kind-level operation is written against it, so a new kind has to answer this
    /// question and nothing else has to remember to ask.
    pub fn listed(&self) -> Option<&[Type]> {
        match self {
            TypeKind::Enumerated(domains) => Some(domains),
            TypeKind::UIntRanges | TypeKind::Any => None,
        }
    }

    /// Mutable analog of [`listed`](Self::listed).
    pub fn listed_mut(&mut self) -> Option<&mut [Type]> {
        match self {
            TypeKind::Enumerated(domains) => Some(domains),
            TypeKind::UIntRanges | TypeKind::Any => None,
        }
    }

    /// The types this kind carries as **children** — every `Type` inside it, which
    /// substitution, freshening, extrusion and structural comparison must reach.
    ///
    /// A *superset* of [`listed`](Self::listed), and the distinction is not
    /// cosmetic. Listed domains are the kind's *members*, compared by value and
    /// placed in the domain lattice. A described kind lists no members but may still
    /// be **parameterized** by a type that is not one of its domains — the key type
    /// of a keyed kind is the standing example: its members are refinements
    /// `{𝐾 | tok}`, not `𝐾` itself, so `𝐾` is a child to be traversed and never a
    /// domain to be matched. Conflating the two silently drops such a type from every
    /// traversal.
    pub fn children(&self) -> &[Type] {
        match self {
            TypeKind::Enumerated(domains) => domains,
            TypeKind::UIntRanges | TypeKind::Any => &[],
        }
    }

    /// Mutable analog of [`children`](Self::children).
    pub fn children_mut(&mut self) -> &mut [Type] {
        match self {
            TypeKind::Enumerated(domains) => domains,
            TypeKind::UIntRanges | TypeKind::Any => &mut [],
        }
    }

    /// Rebuild with `f` applied to each child (see [`children`](Self::children)),
    /// preserving which kind this is. A kind with no children is returned unchanged,
    /// which is why traversals need no per-kind arm of their own.
    pub fn map_children(&self, mut f: impl FnMut(&Type) -> Type) -> TypeKind {
        match self {
            TypeKind::Enumerated(domains) => {
                TypeKind::Enumerated(domains.iter().map(&mut f).collect())
            }
            TypeKind::UIntRanges | TypeKind::Any => self.clone(),
        }
    }

    /// Whether this kind **admits** `ty` — the membership predicate that gives a
    /// *described* kind its content.
    ///
    /// Membership and kind subtyping are different questions with different shapes:
    /// this takes one type and answers about one kind, while
    /// [`contains`](Self::contains) takes two kinds. They meet in exactly one place —
    /// a listed kind is contained in a described one iff the description admits every
    /// candidate — which is why a new kind needs this and a row in the order, and
    /// nothing else.
    ///
    /// Every arm below is the notion's answer for its kind, but `contains` — the only
    /// caller — reaches only the ones that *neither absorb nor list*: it settles ⊤ by
    /// absorption and a listing-against-listing by the pairing rule, both before
    /// membership is consulted. So the reachable question today is exactly "is this a
    /// dense prefix range". Worth knowing before reading a change to another arm as
    /// live: whether a new kind's arm is reached depends on which rule `contains`
    /// settles it by, not on the arm being written.
    ///
    /// That this predicate can be *written at all* is what makes kind **variables**
    /// unnecessary: membership is decidable from the classified type, so the only thing
    /// inference can be missing is that type. Contrast [`FunKind`], which classifies
    /// provenance rather than shape and therefore has no such predicate and does need
    /// [`FunKindVar`]. See `src/ccl/design/type-inference.md`, "What the kind level needs
    /// from the solver".
    ///
    /// Note the asymmetry with a *type*: a kind admits many types, and a type is
    /// admitted by many kinds. There is no "kind of a type" to read off — only, for a
    /// given type, the minimal kind containing it (the singleton listing).
    pub fn admits(&self, ty: &Type) -> bool {
        match self {
            // ⊤: every type.
            TypeKind::Any => true,
            // A dense prefix range, and nothing else. A `Refinement` over one is not a
            // `UIntRange`, so a filtered collection is not admitted — it would be handed
            // a length witness for a domain with holes.
            TypeKind::UIntRanges => matches!(ty, Type::UIntRange(_)),
            TypeKind::Enumerated(domains) => domains.contains(ty),
        }
    }

    /// Whether every domain `self` ranges over is one `sup` ranges over — the
    /// `𝐾₀ <: 𝐾₁` premise of Σ-width. `Some` is the edge holding, carrying whatever
    /// still has to be discharged for it ([`KindObligations`]); `None` is a genuine
    /// non-subtype.
    ///
    /// Ordinary subtyping one level up — a relation between two *classifiers* of types,
    /// not between two types.
    /// A **singleton** listed kind is contained like any other; it is not a back door
    /// for entering a sum. Nothing views a plain data function as a one-candidate sum —
    /// that would build a sum by subsumption, and only a term builds one
    /// (`src/ccl/design/type-inference.md`, "Only a term builds a sum").
    ///
    /// Obligations ride the return value rather than an out-parameter so a rejected
    /// edge cannot leave a caller holding the ones gathered before it was rejected.
    pub fn contains(&self, sup: &TypeKind) -> Option<KindObligations> {
        // ⊤ absorbs, structurally rather than by a row per kind.
        if matches!(sup, TypeKind::Any) {
            return Some(KindObligations::default());
        }
        match (self.listed(), sup) {
            // Both list: the `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁` of the Σ-width rule, handed back as a
            // **pairing** obligation. It cannot be answered here because the per-pairing
            // test is a body edge — subtyping — and it must not be answered by set
            // membership either: that is only the `𝑒 = 𝑑` instance, and taking it as the
            // rule is what makes a candidate-specific correspondence look impossible.
            //
            // The search is also the one comparison that cannot **wait**: matching a
            // candidate against a finite set of alternatives is a *disjunction*, which a
            // bounds-recording solver cannot hold open — that needs a choice, and a
            // choice here is neither confluent nor undoable. So the discharge requires
            // ground candidates, and an unresolved one is a rejection rather than a
            // recorded constraint, which is what keeps a Σ from being formed before
            // coalesce.
            (Some(subs), sups @ TypeKind::Enumerated(_)) => {
                let sups = sups.listed().expect("an enumerated kind lists its domains");
                Some(KindObligations {
                    pairing: Some((subs.to_vec(), sups.to_vec())),
                    ..KindObligations::default()
                })
            }
            // A listed kind is contained in a *description* iff the description
            // [`admits`](Self::admits) every candidate — the one place membership and
            // kind subtyping meet. A *conjunction* of per-candidate questions, and a
            // conjunction of atomic constraints is exactly what a bounds graph records:
            // so a candidate with no shape yet does not need a verdict now, it needs a
            // **kinding constraint**.
            (Some(subs), described) => {
                let mut obligations = KindObligations::default();
                for d in subs {
                    if described.admits(d) {
                        continue;
                    }
                    // A bare variable is the *only* undecidable candidate: every other
                    // head — a refinement, an arrow, an atom — is already readable by
                    // the predicate, whatever variables sit inside it. `{[0, k) | p}` is
                    // a `Refinement` and so is not a `UIntRange`, and no resolution of
                    // `k` changes that.
                    let Type::Infer(v) = d else {
                        return None;
                    };
                    obligations.kinds.push((Rc::clone(v), described.clone()));
                }
                Some(obligations)
            }
            // Two described kinds relate only by being the same description: neither
            // lists domains to compare, and no description here is a sub-description of
            // another (⊤ is already handled above).
            (None, sup) => (self == sup).then(KindObligations::default),
        }
    }

    /// [`contains`](Self::contains) where there is **no constraint graph** to emit
    /// obligations into, so each one counts only if it already holds as written
    /// ([`KindObligations::holds_structurally`]).
    ///
    /// Two callers need this — the compact-domain lattice and the post-coalesce
    /// kinding check — and they must agree with the Σ-width rule. Running the same
    /// containment through one shared discharge is what makes that structural rather
    /// than a coincidence to be maintained.
    pub fn contains_ground(&self, sup: &TypeKind) -> bool {
        self.contains(sup).is_some_and(|o| o.holds_structurally())
    }

    /// Whether a data function whose domain this kind classifies has to **record a
    /// witness**: a kind listing exactly one domain determines that domain, so there is
    /// nothing to record; everything else leaves open which domain was taken.
    ///
    /// **This is not the retired singleton collapse.** It says nothing about a Σ *value*.
    /// `Σ σ ∈ {𝐷 ⤇ 𝑉}. σ` — what `box` builds over a single candidate — is a sum and
    /// stays one; introduction is a term, so nothing collapses it back
    /// (`src/ccl/design/type-inference.md`, "Only a term builds a sum"). The question here
    /// is the opposite one and arises only where no introduction happened: given a domain
    /// kind that *materialization* produced by merging constraints, is the domain
    /// determined? Read this as a fact about a domain, never as an equation between a
    /// one-candidate sum and a plain collection.
    ///
    /// The single test behind [`into_data_fun`](Self::into_data_fun)'s two outcomes,
    /// so anything that must agree with what materialization produces — the
    /// ground-domain invariant coalesce asserts, for one — reads it here rather than
    /// re-deriving it.
    ///
    /// Note what it does *not* separate: an **empty** listing also answers `true` here,
    /// because "not exactly one" is the only distinction materialization needs. A listing
    /// is non-empty by construction ([`SigmaType::over`] asserts it), so this is a sound
    /// reading — but it is why a caller computing candidates cannot use this to decide
    /// whether it has enough of them.
    pub fn needs_witness(&self) -> bool {
        !matches!(self.listed(), Some([_]))
    }

    /// Materialize `(self, codomain)` as the type of a data function whose domain
    /// this kind classifies — the inverse of reading an arrow's domain as a kind.
    ///
    /// A kind that determines its domain materializes as the plain data function
    /// `𝐷 ⤇ 𝑉`; one that does not materializes as the sum, because which domain was
    /// taken is then real information. That single test
    /// ([`needs_witness`](Self::needs_witness), whose doc says what it is *not*) is what
    /// keeps `𝐷 ⤇ 𝑉`, `Σ 𝐷 ∈ {𝐷₀, 𝐷₁}. 𝐷 ⤇ 𝑉` and `List(𝑉)` one construction rather than
    /// three.
    ///
    /// Reachable only from a **domain kind the solver merged**, never from a `box` — a
    /// boxed value's sum is carried in its own slot and rebuilt by the close, so it does
    /// not pass through here and cannot be collapsed by the branch below.
    pub fn into_data_fun(self, name: Option<crate::ccl::Name>, codomain: Type) -> Type {
        if !self.needs_witness() {
            let Some([sole]) = self.listed() else {
                unreachable!("a kind that determines its domain lists exactly one")
            };
            return Type::Fun {
                name,
                kind: FunKind::Data,
                domain: Box::new(sole.clone()),
                codomain: Box::new(codomain),
            };
        }
        // **Factored, for every kind.** A described kind can only be written this way —
        // `List(𝑉)` names infinitely many domains, so there is no candidate list to pair
        // with the codomain — and the two forms cannot be segregated by kind, because a
        // described sum and a listing sum have to *meet*: a `List(𝑉)` parameter annotation
        // and a conditional collection arrive as two bounds on one variable. Written in
        // different forms they collide instead (a witness body cannot merge with an arrow
        // body), which is what makes the factored form the normal form rather than a
        // choice.
        Type::Sigma(Box::new(SigmaType::over(self, name, codomain)))
    }
}

/// The **witness range index** — what each witness binder ranges over, reachable from
/// the binder alone.
///
/// A range is a fact about the consumption that named the witness, and the index is how a
/// reader holding only a [`Type::WitnessRef`] — which names a binder and nothing else —
/// finds it.
///
/// One law, **union**, so writers need not agree on order or completeness and none can
/// narrow what another recorded. An entry only ever grows, and a reader cannot observe a
/// narrower range than has been recorded. That is what makes an index safe here rather than
/// a second authority.
///
/// Scoped to one inference run: entries are dropped with the
/// [`InferArena`](crate::ccl::infer::InferArena) that minted the binders, so a binder's
/// range cannot outlive the graph it describes. Thread-local because inference is
/// non-reentrant per thread and `cargo test` runs whole programs concurrently.
pub mod witness_ctx {
    use super::TypeKind;
    use crate::ccl::infer_var::WitnessBinderId;
    use std::cell::RefCell;
    use std::collections::HashMap;

    thread_local! {
        static RANGES: RefCell<HashMap<WitnessBinderId, TypeKind>> =
            RefCell::new(HashMap::new());
    }

    /// Note that `binder` ranges over at least `kind`.
    ///
    /// The law is **widening**, so writers need not agree on order or completeness and
    /// none can narrow what another recorded. Two enumerations union; a *described* kind
    /// wins over an enumeration, because it names domains no listing can (`UIntRanges` is
    /// every index range, `Any` every domain), and `Any` wins over everything.
    pub fn note_range(binder: WitnessBinderId, kind: &TypeKind) {
        RANGES.with(|m| {
            let mut m = m.borrow_mut();
            let widened = match m.get(&binder) {
                None => kind.clone(),
                Some(prev) => widen(prev, kind),
            };
            m.insert(binder, widened);
        });
    }

    fn widen(a: &TypeKind, b: &TypeKind) -> TypeKind {
        match (a, b) {
            (TypeKind::Any, _) | (_, TypeKind::Any) => TypeKind::Any,
            (TypeKind::Enumerated(xs), TypeKind::Enumerated(ys)) => {
                let mut out = xs.clone();
                for y in ys {
                    if !out.contains(y) {
                        out.push(y.clone());
                    }
                }
                TypeKind::Enumerated(out)
            }
            // One describes and the other lists: the description is the wider of the two.
            (described, TypeKind::Enumerated(_)) => described.clone(),
            (TypeKind::Enumerated(_), described) => described.clone(),
            (x, _) => x.clone(),
        }
    }

    /// What `binder` ranges over, if it names a witness minted in this run.
    pub fn range(binder: WitnessBinderId) -> Option<TypeKind> {
        RANGES.with(|m| m.borrow().get(&binder).cloned())
    }

    /// Drop every entry — the index's scope ends with its inference run.
    pub fn clear() {
        RANGES.with(|m| m.borrow_mut().clear());
    }
}

impl SigmaType {
    /// `Σ (𝑤: kind). 𝑤 ⤇ codomain` — the shape every data-function sum has: a **new**
    /// witness, and a body that is the data function from it to the shared element type.
    ///
    /// The single place a kind becomes a Σ witness, so it is where the listing's
    /// non-emptiness is checked.
    pub fn over(kind: TypeKind, name: Option<crate::ccl::Name>, codomain: Type) -> SigmaType {
        // An **empty** listing has no domain the witness could be, so `Σ 𝐷 ∈ {}. 𝐷 ⤇ 𝑉` is a
        // collection type nothing inhabits — and it is not caught downstream: it passes
        // [`TypeKind::needs_witness`] (which asks "not exactly one") and is vacuously contained
        // in every kind (a `∀` over no candidates), so it propagates as a plausible ⊥
        // instead of failing. Callers that compute a listing must decide what an empty
        // result means before building a sum from it.
        debug_assert!(
            kind.listed().is_none_or(|domains| !domains.is_empty()),
            "a Σ's listed witness kind must name at least one domain"
        );
        let witness = Witness::fresh(kind);
        let domain = Type::WitnessRef(witness.binder());
        SigmaType::bound(
            witness,
            Type::Fun {
                name,
                kind: FunKind::Data,
                domain: Box::new(domain),
                codomain: Box::new(codomain),
            },
        )
    }

    /// `Σ (𝑤: kind). 𝑤` — the sum whose body *is* a **new** witness, what
    /// [`Builtin::Box`](crate::ccl::Builtin) introduces.
    ///
    /// `kind`'s candidates are whole types, so the sum denotes a value inhabiting one of
    /// them: Σ-*introduction*, and a term. With *domains* as candidates the identical
    /// shape is a sum `Σ 𝐷 ∈ 𝐾. 𝐷` standing where a domain belongs, a type fabricated for what is a variable, which
    /// `src/ccl/design/type-inference.md`, "Why a name, and not a type" rejects in favour
    /// of naming it — and [`has_sum_in_domain_position`] is the wall that keeps them apart.
    pub fn of(kind: TypeKind) -> SigmaType {
        debug_assert!(
            kind.listed().is_none_or(|domains| !domains.is_empty()),
            "a Σ's listed witness kind must name at least one domain"
        );
        let witness = Witness::fresh(kind);
        let body = Type::WitnessRef(witness.binder());
        SigmaType::bound(witness, body)
    }

    /// `Σ (witness). body` — the only constructor.
    ///
    /// One, because with the binder inside the [`Witness`] there is no second question to
    /// answer: minting, deriving and renaming are all choices about *which witness*, made
    /// before you get here ([`Witness::fresh`], [`Witness::with_kind`],
    /// [`Witness::alpha_convert`], or simply reusing one). What used to be three
    /// constructors was three ways of pairing a binder with a body, and the pairing is
    /// exactly what went wrong.
    ///
    /// No vacuity check here, deliberately. A body that does not mention its witness is
    /// vacuous by the witness-erasure law, but this is also every pass's rebuild — a
    /// substitution walking an outer sum whose binder happens to live only in a nested
    /// sum's *body* passes through exactly that shape transiently. The pairing error such
    /// a check would catch is no longer expressible anyway: the binder arrives inside the
    /// [`Witness`], so the only way to pair a body with a foreign one is
    /// [`Witness::bound_to`].
    pub fn bound(witness: Witness, body: Type) -> SigmaType {
        SigmaType {
            witness,
            body: Box::new(body),
        }
    }

    /// This sum **under a fresh binder**, its body's occurrences renamed with it.
    ///
    /// What instantiating a scheme owes a sum: a scheme binds its witness, so each
    /// instantiation needs its own or every use names the one the scheme wrote — and
    /// `box`'s scheme is a single `Σ 𝜎 ∈ {α}. 𝜎`, so sharing it makes every `box` in a
    /// program name one witness.
    pub fn alpha_convert(&self) -> SigmaType {
        let witness = self.witness.alpha_convert();
        let renamed = subst_witness_ref(
            &self.body,
            self.binder(),
            &Type::WitnessRef(witness.binder()),
        );
        if renamed == *self.body {
            // Vacuous in its own witness: nothing to rename, and `bound` would rightly
            // reject the result.
            return self.clone();
        }
        SigmaType::bound(witness, renamed)
    }

    /// This sum **renamed onto `to`** — α-conversion at a chosen binder.
    ///
    /// A binder is bound, so renaming it changes nothing about the type. What it changes
    /// is what *other* types may name: a variable whose lower bounds are sums holds one
    /// sum-typed value, and every sum among them is a description of that one value, so
    /// they are brought under one binder before anything opens them. See
    /// [`crate::ccl::infer_var::InferVar::witness_binder`].
    pub fn rename_binder(&self, to: crate::ccl::infer_var::WitnessBinderId) -> SigmaType {
        if self.binder() == to {
            return self.clone();
        }
        let renamed = subst_witness_ref(&self.body, self.binder(), &Type::WitnessRef(to));
        if renamed == *self.body {
            // Vacuous in its own witness: nothing names the binder, so nothing to rename.
            return self.clone();
        }
        SigmaType::bound(Witness::bound_to(to, self.kind().clone()), renamed)
    }

    /// This sum's binder — the id its body's [`Type::WitnessRef`]s name.
    pub fn binder(&self) -> crate::ccl::infer_var::WitnessBinderId {
        self.witness.binder()
    }

    /// This sum's witness kind.
    pub fn kind(&self) -> &TypeKind {
        self.witness.kind()
    }

    /// The body at a given candidate — `𝐵[𝑑]`, the witness replaced throughout.
    ///
    /// Every Σ rule is stated in terms of this: width is
    /// `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁. 𝐵₀[𝑑] <: 𝐵₁[𝑒]` and elimination is `∀ 𝑑 ∈ 𝐾. 𝐵[𝑑] <: 𝑈`
    /// (`src/ccl/design/type-inference.md`, "How a sum flows through the solver"). A
    /// rule that instantiates both sides before emitting any edge never depends on an
    /// unfixed correspondence, which is what lets the body be an arbitrary type rather
    /// than an arrow the rule destructures.
    pub fn instantiate_body(&self, candidate: &Type) -> Type {
        let out = subst_witness_ref(&self.body, self.binder(), candidate);
        // **The body really is instantiated.** Every Σ rule compares instantiated bodies,
        // and an occurrence surviving here would be a rule comparing `𝐵` where it states
        // `𝐵[𝑑]`. That used to be caught downstream, by a *bound* witness turning up at a
        // subtyping edge; now that bound and free are spelled the same, no downstream site
        // can tell them apart, so the invariant is asserted where it is established — which
        // is also the only place it is provable.
        debug_assert!(
            !mentions_witness(&out, self.binder()),
            "instantiating `𝐵[𝑑]` left an occurrence of the witness behind: {out}"
        );
        out
    }

    /// Whether the body *is* this sum's witness — the **unfactored** shape
    /// `Σ 𝜎 ∈ 𝐾. 𝜎`, what [`crate::ccl::Builtin::Box`] introduces.
    ///
    /// Legal only when `𝐾`'s candidates are whole types, so the sum denotes a value
    /// inhabiting one of them. With *domains* as candidates the same shape is a sum
    /// standing where a domain belongs — a type fabricated for what is a variable — which
    /// `src/ccl/design/type-inference.md`, "Why a name, and not a type" rejects in favour
    /// of naming it. [`has_sum_in_domain_position`] is the check that keeps the two apart.
    pub fn body_is_witness(&self) -> bool {
        matches!(&*self.body, Type::WitnessRef(w) if *w == self.binder())
    }

    /// The **witness-independent residue** of the body: the part of `𝐵[𝑤]` that does not
    /// vary with the witness, paired with its element binder.
    ///
    /// Σ-width is `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁. 𝐵₀[𝑑] <: 𝐵₁[𝑒]`, and the implementation splits
    /// that into a **search** over the witness-*dependent* part and one edge for the
    /// residue. The split is not an optimization: the search tries candidates and
    /// discards failures, which is only sound because a comparison of two *ground*
    /// candidates records nothing on any variable. The residue may mention inference
    /// variables, so emitting it inside the search would leave bounds behind from
    /// attempts that failed.
    ///
    /// A data-function body `𝑤 ⤇ 𝑉` has residue `𝑉` — one codomain shared across
    /// candidates. A body that *is* the witness (what [`Builtin::Box`](crate::ccl::Builtin)
    /// introduces) has **no**
    /// residue: every part of it varies, the search covers all of it, and there is no
    /// second edge to emit. Hence `Option` rather than a destructure that assumes an
    /// arrow.
    pub fn body_residue(&self) -> Option<(&Option<crate::ccl::Name>, &Type)> {
        match &*self.body {
            Type::Fun { name, codomain, .. } => Some((name, codomain)),
            Type::WitnessRef(_) => None,
            other => unreachable!("unexpected Sigma body shape: {other:?}"),
        }
    }
}

impl Witness {
    /// A **new** witness: a kind, and a binder minted for it.
    ///
    /// The one act of origination. Every other way to obtain a `Witness` carries an
    /// existing binder, so a sum built from one is the same sum — which is what makes a
    /// duplicate a visible call to this rather than the default.
    pub fn fresh(kind: TypeKind) -> Witness {
        Witness {
            kind,
            binder: crate::ccl::infer_var::fresh_witness_binder_id(),
        }
    }

    /// A witness re-formed from a binder already in circulation and the kind it ranges
    /// over — **the representation boundary, and the one deliberate re-binding.**
    ///
    /// Two callers, and neither is a solver site choosing a name. Materialization crosses
    /// from the compact world, where a sum's kind is a `CompactWitnessKind` (candidates are
    /// `CompactType`s) rather than a [`TypeKind`]: the pair has to be re-formed there
    /// because the kind is being *converted*, so no amount of pairing them earlier removes
    /// it. And [`Type::without_witness_binders`] re-binds on purpose, assigning de Bruijn
    /// depth as the binder — that is the whole point of the canonicalization, not a seam.
    ///
    /// Every other caller holds a witness and passes it. If this acquires a third caller
    /// in the solver, that is the smell: it means a kind travelled without its binder
    /// again.
    pub fn bound_to(binder: crate::ccl::infer_var::WitnessBinderId, kind: TypeKind) -> Witness {
        Witness { kind, binder }
    }

    /// What this witness ranges over.
    pub fn kind(&self) -> &TypeKind {
        &self.kind
    }

    /// The binder its occurrences name.
    pub fn binder(&self) -> crate::ccl::infer_var::WitnessBinderId {
        self.binder
    }

    /// **The same witness over a different kind** — a join widens the candidates without
    /// making the witness a different one.
    pub fn with_kind(&self, kind: TypeKind) -> Witness {
        Witness {
            kind,
            binder: self.binder(),
        }
    }

    /// **The same witness under a fresh binder.** What instantiating a scheme owes one:
    /// a scheme binds its witness, so each instantiation needs its own, or every use names
    /// the one the scheme wrote. Callers must rename the occurrences to match — see
    /// [`SigmaType::alpha_convert`], which does both halves.
    pub fn alpha_convert(&self) -> Witness {
        Witness::fresh(self.kind.clone())
    }

    /// The type children this witness carries — its kind's
    /// [`children`](TypeKind::children).
    pub fn types(&self) -> &[Type] {
        self.kind.children()
    }

    /// Mutable analog of [`types`](Self::types).
    pub fn types_mut(&mut self) -> &mut [Type] {
        self.kind.children_mut()
    }

    /// Rebuild this witness with `f` applied to each type child — **the binder carries**,
    /// because mapping a witness's candidates does not make it another witness.
    pub fn map_types(&self, f: impl FnMut(&Type) -> Type) -> Witness {
        self.with_kind(self.kind.map_children(f))
    }
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
/// tag (as produced by `++`/CollectionUnion and other unnamed sums),
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
            Type::Variant(inner) => match synthetic_payloads(inner) {
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

/// Whether [`Display`](std::fmt::Display) writes witness binder ids (`CCL_SHOW_BINDERS`).
///
/// Read once. A `Display` impl runs on every rendered type, and this is a debugging
/// affordance rather than a behavioural switch.
fn show_binders() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("CCL_SHOW_BINDERS").is_some())
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Base(b) => write!(f, "{}", b.keyword()),
            // `n == 0` means an empty range (e.g. the domain of `[]`); render
            // it as `∅` instead of computing `n - 1` and underflowing.
            Type::UIntRange(0) => write!(f, "∅"),
            Type::UIntRange(n) => write!(f, "[0, {}]", n - 1),
            // The arrow reflects the resolved `kind`: `⇒` for a compute
            // capability (and an unresolved kind var), `⤇` for a data domain
            // (see `FunKind::arrow`). Once kind inference resolves every arrow
            // once resolved, a data collection renders `⤇`, making the domain/capability
            // distinction legible in every type string.
            Type::Fun {
                name: Some(x),
                kind,
                domain,
                codomain,
            } => write!(f, "(({x}: {domain}) {} {codomain})", kind.arrow()),
            Type::Fun {
                name: None,
                kind,
                domain,
                codomain,
            } => write!(f, "({domain} {} {codomain})", kind.arrow()),
            Type::Tuple(ts) => {
                let parts: Vec<_> = ts.iter().map(|t| t.to_string()).collect();
                write!(f, "({})", parts.join(", "))
            }
            Type::Record(fields) => {
                let parts: Vec<_> = fields.iter().map(|(n, t)| format!("{n}: {t}")).collect();
                write!(f, "{{{}}}", parts.join(", "))
            }
            Type::Variant(tags) => {
                // Anonymous positional variants (all tags are
                // `FieldKey::Index`, as `++`/CollectionUnion produces) are
                // rendered as a flat `A | B` join — the positional tags
                // carry no user-meaningful information. Nested
                // all-positional variants flatten recursively so
                // `a ++ b ++ c` prints as `A | B | C` rather than
                // `[._0: [._0: A | ._1: B] | ._1: C]`.
                if let Some(payloads) = synthetic_payloads(tags) {
                    let parts: Vec<_> = payloads.iter().map(|t| t.to_string()).collect();
                    write!(f, "{}", parts.join(" | "))
                } else {
                    // CHL's surface spelling — see `fmt_variant_arms`. A `Unit`
                    // payload is the nullary constructor and renders bare.
                    crate::util::fmt_variant_arms(
                        f,
                        tags.iter().map(|(n, t)| {
                            let payload = match t {
                                Type::Base(BaseType::Unit) => None,
                                _ => Some(t.to_string()),
                            };
                            (n.to_string(), payload)
                        }),
                    )
                }
            }
            // A **singleton** prints as the literal it pins: `{Int | __elem == 5}` is
            // `5`. That is the whole content of the type, and spelling it out puts a
            // predicate in front of the reader at every literal. Every other
            // refinement prints in the general form.
            Type::Refinement(t, r) => match singleton_value(self) {
                Some(lit) => write!(f, "{}", symbolic::symbolic(lit)),
                None => write!(f, "{{{t} | {}}}", symbolic::symbolic(&r.predicate)),
            },
            Type::Hole => write!(f, "_"),
            Type::Infer(var) => write!(f, "?{}", var.uid),
            Type::DataSource(name) => write!(f, "source({name})"),
            Type::ChanDom(name, _) => write!(f, "chan({name})"),
            Type::Txn => write!(f, "Txn"),
            Type::History {
                value,
                domain,
                kind,
            } => {
                if *kind == HistoryKind::Overwrite {
                    write!(f, "Mut({value}, {domain})")
                } else {
                    write!(f, "feed({domain} ⇒ {value})")
                }
            }
            Type::Sigma(s) => {
                // The binder is written, and its **id is not**: which position the
                // witness occupies is the whole distinction between a sum over *domains*
                // (`Σ σ ∈ 𝐾. σ ⤇ 𝑉` — a collection) and one over whole *types*
                // (`Σ σ ∈ 𝐾. σ` — what `box` builds), and a shorthand that elides the
                // binder renders the two identically. Rendering the id instead would make
                // every golden depend on minting order for a distinction no reader of a
                // single type needs; two sums that differ only in binder identity are
                // α-equivalent, and `without_witness_binders` is how code compares them.
                if show_binders() {
                    write!(f, "Σ σ@{} ∈ {}. {}", s.binder(), s.witness.kind(), s.body)
                } else {
                    write!(f, "Σ σ ∈ {}. {}", s.witness.kind(), s.body)
                }
            }
            Type::WitnessRef(b) => {
                // Binder ids off by default: they would make every golden depend on minting
                // order for a distinction no reader of a single type needs, and two sums
                // differing only in binder identity are α-equivalent. `CCL_SHOW_BINDERS`
                // turns them on for the case that *is* about identity — two types that
                // print identically and compare unequal, where the plain rendering shows
                // nothing at all.
                if show_binders() {
                    write!(f, "σ@{b}")
                } else {
                    write!(f, "σ")
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

    /// Helper for creating a dependent (Pi) **compute** function type
    /// `(name: domain) ⇒ codomain`.
    pub fn pi(name: impl Into<crate::ccl::Name>, domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: Some(name.into()),
            kind: FunKind::Compute,
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
    /// can never silently flip a data arrow to compute or drop its Pi binder. A
    /// non-arrow exemplar yields a plain `Compute` arrow with no binder — the
    /// safe default at a site with no arrow to copy from.
    ///
    /// **A sum is an arrow.** `Σ 𝑤 ∈ 𝐾. (𝑤 ⤇ 𝑉)` is a collection exactly as `𝐷 ⤇ 𝑉`
    /// is; the witness binder only says its domain is whichever candidate was taken. So
    /// a sum exemplar rebuilds its *body* and closes the result back under the same
    /// witness — dropping that binder is the same silent loss as flipping the kind, and
    /// it is worse, because the rebuilt domain is usually the witness itself and a
    /// `WitnessRef` outside its binder means nothing at all.
    pub fn fun_like(exemplar: &Type, domain: Self, codomain: Self) -> Self {
        match exemplar {
            Type::Fun { name, kind, .. } => Type::Fun {
                name: name.clone(),
                kind: kind.clone(),
                domain: Box::new(domain),
                codomain: Box::new(codomain),
            },
            // Through **every** wrapper: a sum's body may be another sum, and rebuilding
            // only the innermost would drop the binders above it.
            Type::Sigma(s) if matches!(&*s.body, Type::Fun { .. } | Type::Sigma(_)) => {
                Type::Sigma(Box::new(SigmaType::bound(
                    s.witness.clone(),
                    Type::fun_like(&s.body, domain, codomain),
                )))
            }
            _ => Type::fun(domain, codomain),
        }
    }

    /// The type of a **list**: a dependent sum `Σ (𝐷: UIntRanges). 𝐷 ⤇ elem` — a
    /// *type*-witness whose kind is every index range ([`TypeKind::UIntRanges`]), so
    /// the length is the witness **domain** rather than a separate scalar value, and
    /// `len` is a property of that domain. An `Array` reaches it as `box(arr)`, whose
    /// one-candidate sum `Σ (𝐷 ∈ {[0, k)}). 𝐷 ⤇ elem` is contained by plain kind
    /// containment: `{[0, k)} ⊆ UIntRanges`. The `box` is not optional — without it there
    /// is no edge at all (`src/ccl/design/collections.md`, "Subtyping").
    ///
    /// There is deliberately no `{𝑖 | 𝑖 < 𝑛}` domain refinement: the *kind* already
    /// says "a dense prefix range", so nothing needs saying about the elements — and
    /// a filtered range, being a `Refinement` rather than a `UIntRange`, is excluded
    /// by construction rather than by a gate that must remember not to strip
    /// refinements.
    ///
    /// Contrast a conditional collection, whose kind is a *finite* candidate set
    /// ([`TypeKind::Enumerated`]).
    pub fn list_of(elem: Type) -> Self {
        TypeKind::UIntRanges.into_data_fun(None, elem)
    }

    /// The type of a **collection**: the dependent sum `Σ (𝐷: Any). 𝐷 ⤇ elem` — a
    /// *type*-witness of [`TypeKind::Any`] (the universe of domains). Its domain is an
    /// unknown, unordered, opaque domain, which is what makes it the ⊤ of the kind
    /// order.
    ///
    /// `Any` is that ⊤ and **nothing more**. In particular it is not load-bearing for
    /// keyed-ness: a `Map`/`Set` is a sum over `TypeKind::Keyed`, not over a
    /// `Collection(𝐾)` key-set witness — that design was rejected, and why is in
    /// `src/ccl/design/collections.md`, "The referenceable opaque domain".
    ///
    /// Reaching this type is [`Builtin::Box`](crate::ccl::Builtin)-mediated like every
    /// other subtyping edge into a sum: a bare
    /// `𝐷 ⤇ 𝑉` is *not* below it, because that edge would build a sum by
    /// subsumption, and a structural top is an upper bound of every pair of data
    /// functions — which is precisely the implicit join the explicit-`box` design
    /// exists to surface (`src/ccl/design/type-inference.md`, "Only a term builds a sum").
    ///
    /// Contrast a conditional collection
    /// ([`TypeKind::Enumerated`] — a *finite* set of candidate domains) and
    /// [`list_of`](Self::list_of) (`TypeKind::UIntRanges` — every index range). This is
    /// the non-enumerable, opaque-domain sibling.
    pub fn collection_of(elem: Type) -> Self {
        TypeKind::Any.into_data_fun(None, elem)
    }

    /// The domain of the arrow this type denotes, seeing through a sum's binder.
    ///
    /// **A sum is an arrow.** `Σ 𝑤 ∈ 𝐾. (𝑤 ⤇ 𝑉)` is the same collection as `𝐷 ⤇ 𝑉`,
    /// with a binder saying its domain is whichever candidate the witness took — so the
    /// domain it reports is that witness. Callers that go on to *rebuild* the arrow are
    /// safe by construction ([`fun_like`](Self::fun_like) re-closes the binder); a caller
    /// that instead *inspects* the answer must ask whether it is witness-bound before
    /// treating it as a domain it can read (`iterate` does, since an undetermined witness
    /// has no static extent).
    ///
    /// `None` for an **unfactored** sum (`Σ σ ∈ {𝑇ᵢ}. σ`, what `box` builds): its
    /// candidates are whole types rather than domains, so there is no one domain to
    /// report without factoring it first.
    pub fn domain(&self) -> Option<Type> {
        match self {
            Type::Fun { domain, .. } => Some(domain.as_ref().clone()),
            Type::Sigma(s) => s.body.domain(),
            _ => None,
        }
    }

    /// The codomain of the arrow this type denotes, seeing through a sum's binder.
    ///
    /// Unlike [`domain`](Self::domain) this is always safe to read: a factored sum shares
    /// one element type across its candidates, so the codomain never mentions the witness.
    pub fn codomain(&self) -> Option<Type> {
        match self {
            Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
            Type::Sigma(s) => s.body.codomain(),
            _ => None,
        }
    }

    /// A structural copy with every Σ binder **canonicalized by nesting depth**, so that two
    /// α-equivalent sums compare equal.
    ///
    /// Binder ids are minted per sum and globally unique, which is what lets an occurrence
    /// name its binder after a term has been taken apart. The price is that two sums built by
    /// *different derivations* — an inferred type and a hand-written expected one — are
    /// structurally unequal though they denote the same type. This is the witness counterpart
    /// of [`without_pi_names`](Self::without_pi_names), and exists for the same reason.
    ///
    /// Canonicalization is by **de Bruijn index**, not by erasure: replacing every binder with
    /// one constant would make `Σ 𝑤₁. Σ 𝑤₂. 𝑤₁` and `Σ 𝑤₁. Σ 𝑤₂. 𝑤₂` compare equal, which is
    /// the distinction the ids exist to keep.
    pub fn without_witness_binders(&self) -> Type {
        fn go(ty: &Type, scope: &mut Vec<crate::ccl::infer_var::WitnessBinderId>) -> Type {
            use crate::ccl::infer_var::WitnessBinderId;
            match ty {
                // Index from the innermost binder outward, so the name is the *shape* of the
                // reference rather than the identity of what it points at. An occurrence with
                // no binder in scope keeps its own id: it is free, and the free-witness check
                // is what has an opinion about that.
                Type::WitnessRef(w) => match scope.iter().rev().position(|b| b == w) {
                    Some(depth) => Type::WitnessRef(WitnessBinderId(depth as u32)),
                    None => Type::WitnessRef(*w),
                },
                Type::Sigma(s) => {
                    // The kind's candidates are written in the *enclosing* scope, so they are
                    // canonicalized before this binder is pushed.
                    let witness = s.witness.map_types(|t| go(t, scope));
                    scope.push(s.binder());
                    let body = go(&s.body, scope);
                    scope.pop();
                    // De Bruijn *depth* as the binder, which is the whole point of this
                    // canonicalization — so it is a deliberate re-binding rather than a
                    // derivation, and `bound_to` is how it is said.
                    Type::Sigma(Box::new(SigmaType::bound(
                        Witness::bound_to(
                            WitnessBinderId(scope.len() as u32),
                            witness.kind().clone(),
                        ),
                        body,
                    )))
                }
                other => {
                    let mut out = other.clone();
                    out.walk_children_mut(|c| *c = go(c, scope));
                    out
                }
            }
        }
        go(self, &mut Vec::new())
    }

    /// A structural copy with every Pi binder name erased (`Fun.name → None`)
    /// and every function **kind** canonicalized to `Compute`.
    ///
    /// The binder is load-bearing only inside the type solver (it carries
    /// dependent-refinement correspondences); downstream passes treat function
    /// types structurally and a `Some`/`None` binder is the same arrow to them.
    /// Use this when comparing types for structural equality across a pass that
    /// does not preserve the cosmetic binder.
    ///
    /// FunKind is normalized for the same reason: **lambda elimination preserves a
    /// function's denotation but not its kind representation** — a data
    /// collection (`⤇`) becomes a point-free form built from compute combinators
    /// (`zip`, `apply`, `const`), so the reconstructed arrow reads `Compute`
    /// though it denotes the same collection. The kind did its work at inference
    /// (lossless conditional-collection joins at coalesce); post-elimination it is not preserved, so
    /// the structural-equality asserts (and the feed-operand agreement check)
    /// compare modulo it. (FunKind-aware subtyping therefore acts in
    /// *Emit*-mode inference, not the post-elimination Check-mode pass.)
    ///
    /// Under the Barendregt convention the blindness needed at the remaining
    /// call sites (lambda elimination's type-preservation asserts) is exactly
    /// `Some` vs `None`: both compared types descend from one derivation, so
    /// when both carry a binder it is the *same* [`crate::ccl::Name`] (uids are preserved
    /// by every copy along the lineage). What elimination does not preserve is
    /// the binder's presence — rebuilt combinator arrows (`fun_ty_or_hole`,
    /// [`Type::fun`]) are constructed with `name: None`. If those sites ever
    /// preserve binders on rebuilt arrows, this helper can retire.
    pub fn without_pi_names(&self) -> Type {
        match self {
            Type::Fun {
                domain, codomain, ..
            } => Type::Fun {
                name: None,
                // Canonicalize kind — elimination does not preserve it (see the
                // doc above); comparing modulo it is what these structural asserts
                // want.
                kind: FunKind::Compute,
                domain: Box::new(domain.without_pi_names()),
                codomain: Box::new(codomain.without_pi_names()),
            },
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| t.without_pi_names()).collect()),
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), t.without_pi_names()))
                    .collect(),
            ),
            Type::Variant(tags) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), t.without_pi_names()))
                    .collect(),
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
            Type::Sigma(s) => Type::Sigma(Box::new(SigmaType::bound(
                s.witness.map_types(|t| t.without_pi_names()),
                s.body.without_pi_names(),
            ))),
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::WitnessRef(_)
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
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::WitnessRef(_)
            | Type::Txn => {}
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
            Type::Variant(tags) => {
                for (_, t) in tags {
                    f(t);
                }
            }
            // The witness's type children and the body are the Sigma's children.
            Type::Sigma(s) => {
                for t in s.witness.types() {
                    f(t);
                }
                f(&s.body);
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
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::WitnessRef(_)
            | Type::Txn => {}
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
            Type::Variant(tags) => {
                for (_, t) in tags {
                    f(t);
                }
            }
            Type::Sigma(s) => {
                for t in s.witness.types_mut() {
                    f(t);
                }
                f(&mut s.body);
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

/// Whether `ty` contains a **sum standing where a domain belongs**: an unfactored
/// `Σ 𝜎 ∈ 𝐾. 𝜎` in a **data** function's domain.
///
/// A *compute* function's domain is exempt, and not as a concession: it is an ordinary
/// parameter type, and passing a boxed value to a function is exactly what
/// [`crate::ccl::Builtin::Box`] is for. Only a data function's domain is an index set,
/// where "one of `𝐾`" describes no index.
///
/// That position is the one naming the witness exists to keep a sum out of. A domain
/// has to be *something*, and "one of `𝐾`" is not a type — it is a variable, so naming it
/// (naming it) is the only option that does not fabricate one
/// (`src/ccl/design/type-inference.md`, "Why a name, and not a type"). A sum that reaches
/// a domain anyway is read downstream as a concrete index set: it is what asks planning
/// for the iteration extent of "one of two ranges", which has no answer.
///
/// Positional rather than a test on the candidates, deliberately: the *shape* is
/// legitimate elsewhere — it is exactly what `box` introduces — so what makes it wrong is
/// where it sits, and a predicate on the candidates alone would have to guess at which
/// types can be domains.
pub fn has_sum_in_domain_position(ty: &Type) -> bool {
    fn unfactored_sum_within(ty: &Type) -> bool {
        if matches!(ty, Type::Sigma(s) if s.body_is_witness()) {
            return true;
        }
        let mut found = false;
        ty.walk_children(|c| found |= unfactored_sum_within(c));
        found
    }
    let mut found = matches!(
        ty,
        Type::Fun { domain, kind: FunKind::Data, .. } if unfactored_sum_within(domain)
    );
    ty.walk_children(|c| found |= has_sum_in_domain_position(c));
    found
}

/// Whether `ty` contains a **free** [`Type::WitnessRef`] — one with no enclosing
/// [`Type::Sigma`] *within this type* to bind it.
///
/// A bound witness is ordinary and expected: it is how a sum's body names the domain the
/// witness picked. A **free** one is a type that has lost its binder, which is what
/// happens when a pass opens a sum to reach its body and does not close it again. Such a
/// type means nothing on its own — `s` denotes "whichever domain", and with no sum there
/// is no "which" to range over — so consumers downstream read it as a concrete leaf and
/// compare it against real domains.
///
/// The scoping mirrors [`subst_witness_ref`] exactly: a sum binds the witness in its
/// **body**, while its kind's candidates are written in the enclosing scope, so a
/// reference among them belongs to an *outer* binder and is free unless one exists.
/// `in_scope` are the binders already open around this type — empty for a standalone
/// type, and the enclosing tree's binders for a type slot inside a term (see
/// `debug_assert_no_free_witness`).
pub fn has_free_witness_ref(
    ty: &Type,
    in_scope: &[crate::ccl::infer_var::WitnessBinderId],
) -> bool {
    fn go(ty: &Type, scope: &mut Vec<crate::ccl::infer_var::WitnessBinderId>) -> bool {
        match ty {
            // Free iff it names no binder in scope. Testing the **name** rather than
            // "is there a sum somewhere above" is what makes this catch the real error:
            // an occurrence sitting under an *unrelated* sum is still free.
            Type::WitnessRef(w) => !scope.contains(w),
            Type::Sigma(s) => {
                // The kind's candidates are written in the enclosing scope; only the body
                // is under this binder.
                if s.witness.types().iter().any(|t| go(t, scope)) {
                    return true;
                }
                scope.push(s.binder());
                let found = go(&s.body, scope);
                scope.pop();
                found
            }
            other => {
                let mut found = false;
                other.walk_children(|c| found |= go(c, scope));
                found
            }
        }
    }
    go(ty, &mut in_scope.to_vec())
}

/// Replace every occurrence of `binder` in `ty` by `candidate` — the same substitution
/// [`SigmaType::instantiate_body`] performs, for a type that is **not** a sum's body.
///
/// A witness escapes its sum once a term is decomposed: a filter's predicate is indexed by
/// the element, so its types name the witness while no `Σ` is in sight. Instantiating such
/// a type means substituting at the occurrences, there being no binder to strip.
pub fn instantiate_witness(
    ty: &Type,
    binder: crate::ccl::infer_var::WitnessBinderId,
    candidate: &Type,
) -> Type {
    subst_witness_ref(ty, binder, candidate)
}

/// Point every **unbound** witness occurrence in `ty` at `binder`.
///
/// Materialization is the only place that knows which sum a witness atom belongs to: the
/// compact carrier is anonymous by construction, so occurrences come back out of it
/// carrying [`WitnessBinderId::UNBOUND`](crate::ccl::infer_var::WitnessBinderId::UNBOUND)
/// and this is the close that names them. Occurrences already pointing at a *different*
/// binder are left alone — they belong to a nested sum, the same asymmetry
/// [`subst_witness_ref`] walks.
pub fn bind_unbound_witnesses(ty: &Type, binder: crate::ccl::infer_var::WitnessBinderId) -> Type {
    use crate::ccl::infer_var::WitnessBinderId;
    match ty {
        Type::WitnessRef(w) if *w == WitnessBinderId::UNBOUND => Type::WitnessRef(binder),
        other => {
            let mut out = other.clone();
            out.walk_children_mut(|c| *c = bind_unbound_witnesses(c, binder));
            out
        }
    }
}

/// Whether `ty` mentions `binder` anywhere. Binder ids are globally unique, so any
/// occurrence is this binder's and no scope tracking is needed to recognise one.
fn mentions_witness(ty: &Type, binder: crate::ccl::infer_var::WitnessBinderId) -> bool {
    if matches!(ty, Type::WitnessRef(w) if *w == binder) {
        return true;
    }
    let mut found = false;
    ty.walk_children(|c| found |= mentions_witness(c, binder));
    found
}

/// Replace the occurrences of **one binder's** witness with `candidate`.
///
/// Substitution is by **identity**: only `WitnessRef`s naming `binder` are rewritten, so
/// a nested sum's occurrences are untouched because they name a different binder. That is
/// what the binder id buys — the discipline used to be positional (stop at a nested sum's
/// *body*, descend into its *kind*), which encoded the same rule in where a type sits
/// rather than in what it says, and could not survive a term being decomposed.
///
/// A reference naming a **different** binder is never touched — it belongs to another sum,
/// and rewriting it would capture. Identity is what makes that test exact, so the walk can
/// descend everywhere rather than stopping at positions where a foreign witness might sit.
fn subst_witness_ref(
    ty: &Type,
    binder: crate::ccl::infer_var::WitnessBinderId,
    candidate: &Type,
) -> Type {
    match ty {
        Type::WitnessRef(w) if *w == binder => candidate.clone(),
        Type::Sigma(s) => Type::Sigma(Box::new(SigmaType::bound(
            s.witness
                .map_types(|t| subst_witness_ref(t, binder, candidate)),
            // Descending is safe now: a nested sum's occurrences name *its* binder, so
            // the identity test above skips them. The positional rule had to refuse.
            subst_witness_ref(&s.body, binder, candidate),
        ))),
        Type::Fun {
            name,
            kind,
            domain,
            codomain,
        } => Type::Fun {
            name: name.clone(),
            kind: kind.clone(),
            domain: Box::new(subst_witness_ref(domain, binder, candidate)),
            codomain: Box::new(subst_witness_ref(codomain, binder, candidate)),
        },
        Type::Tuple(ts) => Type::Tuple(
            ts.iter()
                .map(|t| subst_witness_ref(t, binder, candidate))
                .collect(),
        ),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), subst_witness_ref(t, binder, candidate)))
                .collect(),
        ),
        Type::Variant(tags) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), subst_witness_ref(t, binder, candidate)))
                .collect(),
        ),
        Type::Refinement(base, r) => Type::Refinement(
            Box::new(subst_witness_ref(base, binder, candidate)),
            r.clone(),
        ),
        Type::History {
            value,
            domain,
            kind,
        } => Type::History {
            value: Box::new(subst_witness_ref(value, binder, candidate)),
            domain: Box::new(subst_witness_ref(domain, binder, candidate)),
            kind: *kind,
        },
        // A witness naming a **different** binder belongs to a nested sum, and an
        // **opened** one belongs to whichever elimination opened it. Neither is this
        // binder's, and substituting either would capture.
        Type::WitnessRef(_)
        | Type::Base(_)
        | Type::UIntRange(_)
        | Type::Hole
        | Type::Infer(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn => ty.clone(),
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
        | (N::CollectionUnion(x), N::CollectionUnion(y)) => all_eq(x, y),
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
        // A realized conditional collection. Reachable inside a predicate because a
        // filter's predicate carries its own copy of the source (`__elem ▷ src ▷ 𝑓`), so
        // when `src` is a conditional, realization rewrites it *in the predicate*.
        (N::Realize(v1), N::Realize(v2)) => eq_refinement_predicate_go(v1, v2),
        _ => {
            // **A missing arm is not "unequal", it is unanswered.** Falling through with
            // two nodes of the *same* shape means this function has no rule for that
            // shape, and reporting `false` makes a predicate compare unequal to a
            // structural copy of itself — reflexivity, quietly lost. It surfaces far away
            // as a type mismatch whose two sides print identically, since the predicate is
            // the one part of a type `Display` does not show.
            debug_assert!(
                std::mem::discriminant(&a.node) != std::mem::discriminant(&b.node),
                "eq_refinement_predicate has no arm for {:?}; two nodes of one shape \
                 compared unequal, so a rebuilt predicate no longer equals itself",
                std::mem::discriminant(&a.node),
            );
            false
        }
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

    /// **A rebuilt predicate equals itself, `Realize` included.** Refinement equality is
    /// structural precisely so a predicate re-minted by planning compares equal to the one
    /// it was built from; a node variant with no arm in `eq_refinement_predicate_go` breaks
    /// that for every predicate containing it, and silently — pointer-equal predicates
    /// short-circuit, so it bites only where a predicate is *rebuilt*, which is exactly
    /// where the equality is load-bearing.
    ///
    /// `Realize` reaches a predicate because a filter's predicate carries its own copy of
    /// the source, so a conditional source gets realized inside it. The symptom is remote
    /// and unhelpful: a type mismatch whose two sides print identically, the predicate
    /// being the part of a type `Display` does not show.
    #[test]
    fn a_rebuilt_predicate_containing_realize_equals_itself() {
        let realizing = || {
            Rc::new(
                TypedExpr::new(TypedExprNode::Realize(Box::new(
                    TypedExpr::new(TypedExprNode::Var(crate::ccl::Name::elem()))
                        .with_ty(Type::Base(BaseType::Int)),
                )))
                .with_ty(Type::Base(BaseType::Int)),
            )
        };
        // Two *separately built* copies: distinct `Rc`s, so the pointer short-circuit
        // cannot hide a missing arm.
        let (a, b) = (Refinement::born(realizing()), Refinement::born(realizing()));
        assert!(
            !Rc::ptr_eq(&a.predicate, &b.predicate),
            "the premise: these must be distinct terms"
        );
        assert_eq!(
            a, b,
            "a rebuilt predicate must equal the one it was built from"
        );
    }

    /// A rebuild against a **sum** exemplar keeps the witness binder.
    ///
    /// `fun_like` exists so a downstream rebuild cannot silently drop what the exemplar
    /// knew. A sum knows one thing more than a plain arrow — that its domain is whichever
    /// candidate the witness took — and losing that is worse than losing the kind: the
    /// rebuilt domain is usually the witness itself, and a `WitnessRef` with no binder
    /// denotes nothing, so every later comparison reads it as a concrete leaf.
    #[test]
    fn fun_like_rebuilds_under_a_sum_exemplar() {
        let int = Type::Base(BaseType::Int);
        let exemplar = Type::Sigma(Box::new(SigmaType::over(
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            None,
            int.clone(),
        )));
        let Type::Sigma(ex) = &exemplar else {
            unreachable!("built as a sum")
        };
        let rebuilt = Type::fun_like(
            &exemplar,
            Type::WitnessRef(ex.binder()),
            Type::Base(BaseType::Bool),
        );
        let Type::Sigma(s) = &rebuilt else {
            panic!("a sum exemplar must rebuild into a sum, got {rebuilt}");
        };
        assert_eq!(
            s.kind(),
            &TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            "the witness kind carries over"
        );
        assert!(
            matches!(
                &*s.body,
                Type::Fun {
                    kind: FunKind::Data,
                    ..
                }
            ),
            "the body stays a data arrow, got {}",
            s.body
        );
        assert!(
            !has_free_witness_ref(&rebuilt, &[]),
            "the rebuilt domain's witness is bound by the re-closed sum, got {rebuilt}"
        );
    }

    use crate::ccl::{BinOpKind, CompareKind};

    fn rng(n: usize) -> Type {
        Type::UIntRange(n)
    }

    /// Membership is a predicate on **one** type against **one** kind, and
    /// listed-in-described containment is built from it — so the two cannot disagree
    /// about what a description covers.
    #[test]
    fn containment_in_a_description_is_membership_of_every_candidate() {
        assert!(TypeKind::UIntRanges.admits(&rng(3)));
        assert!(!TypeKind::UIntRanges.admits(&Type::DataSource("s".into())));
        // A refined range is not a range: a filtered collection must not be admitted and
        // handed a length witness for a domain with holes.
        let refined = Type::Refinement(
            Box::new(rng(3)),
            Refinement {
                predicate: Rc::new(TypedExpr::lit(Lit::Bool(true))),
            },
        );
        assert!(!TypeKind::UIntRanges.admits(&refined));

        assert!(
            TypeKind::Enumerated(vec![rng(2), rng(3)])
                .contains(&TypeKind::UIntRanges)
                .is_some_and(|o| o.kinds.is_empty()),
            "every candidate is a range, and nothing is left over"
        );
        assert!(
            TypeKind::Enumerated(vec![rng(2), refined])
                .contains(&TypeKind::UIntRanges)
                .is_none()
        );
    }

    /// `Any` is ⊤, and holds that position *structurally* — `contains` answers for it
    /// before looking at what `self` is, rather than carrying a row per kind — while
    /// being below nothing narrower.
    #[test]
    fn any_is_the_top_of_the_kind_lattice() {
        for k in [
            TypeKind::Enumerated(vec![rng(3)]),
            TypeKind::UIntRanges,
            TypeKind::Any,
        ] {
            assert!(k.contains(&TypeKind::Any).is_some(), "{k:?} <: ⊤");
        }
        assert!(TypeKind::Any.admits(&Type::DataSource("s".into())));
        assert!(
            TypeKind::Any.contains(&TypeKind::UIntRanges).is_none(),
            "⊤ is not below anything narrower"
        );
    }

    /// The two halves of containment differ in whether they can **wait**. A description
    /// is a predicate — a conjunction — so a candidate with no shape becomes a *kinding
    /// constraint* on that variable rather than a verdict. A listing is a finite
    /// disjunction, which a bounds solver cannot hold open: it becomes a *pairing* to be
    /// searched over ground candidates, and an unresolved candidate has only the identity
    /// instance left, which a variable cannot satisfy.
    #[test]
    fn only_containment_in_a_description_defers_to_a_kinding_constraint() {
        let v = InferVar::fresh(0);
        let unresolved = TypeKind::Enumerated(vec![Type::Infer(Rc::clone(&v))]);

        let obligations = unresolved
            .contains(&TypeKind::UIntRanges)
            .expect("a description holds pending the candidate's kind");
        assert_eq!(obligations.kinds.len(), 1);
        assert!(Rc::ptr_eq(&obligations.kinds[0].0, &v), "on that variable");
        assert_eq!(obligations.kinds[0].1, TypeKind::UIntRanges);
        assert!(
            obligations.pairing.is_none(),
            "a description is not a pairing"
        );

        let listed = unresolved
            .contains(&TypeKind::Enumerated(vec![rng(3)]))
            .expect("a listing hands back the pairing rather than deciding it");
        assert_eq!(
            listed.pairing,
            Some((vec![Type::Infer(v)], vec![rng(3)])),
            "both candidate lists, for the search to run over"
        );
        assert!(
            !listed.holds_structurally(),
            "and with no solver, only the identity instance is available — which an \
             unresolved candidate cannot satisfy"
        );
    }

    /// Set membership is *one* pairing, not the rule. A listing is contained in another
    /// whenever **each** of its candidates has **some** counterpart there, so the kind
    /// level reports the search rather than pre-empting it with equality.
    #[test]
    fn a_listing_against_a_listing_is_a_pairing_not_set_membership() {
        let refined = Type::Refinement(
            Box::new(rng(3)),
            Refinement {
                predicate: Rc::new(TypedExpr::lit(Lit::Bool(true))),
            },
        );
        let obligations = TypeKind::Enumerated(vec![rng(3)])
            .contains(&TypeKind::Enumerated(vec![refined.clone()]))
            .expect("the edge is reported, its pairing left to the solver");
        assert_eq!(obligations.pairing, Some((vec![rng(3)], vec![refined])));
        assert!(
            !obligations.holds_structurally(),
            "the identity instance does not hold here — a search is required, which is \
             exactly what makes this an obligation rather than a verdict"
        );
    }

    /// Nothing is left outstanding once a candidate is ground, which is what lets the
    /// compact lattice and the post-coalesce check discharge with
    /// [`KindObligations::holds_structurally`] rather than a constraint graph.
    #[test]
    fn a_ground_candidate_leaves_no_obligation() {
        assert!(TypeKind::Enumerated(vec![rng(3)]).contains_ground(&TypeKind::UIntRanges));
        assert!(
            !TypeKind::Enumerated(vec![Type::Infer(InferVar::fresh(0))])
                .contains_ground(&TypeKind::UIntRanges),
            "an unresolved candidate has no shape to be ground about"
        );
    }

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
        let commit_abort = Type::Variant(vec![
            (FieldKey::Name("commit".into()), Type::Base(BaseType::Int)),
            (FieldKey::Name("abort".into()), Type::Base(BaseType::Unit)),
        ]);
        assert_eq!(commit_abort.to_string(), "{`commit{Int} | `abort}");

        // Single arm, with and without a stored type.
        assert_eq!(
            Type::Variant(vec![(
                FieldKey::Name("none".into()),
                Type::Base(BaseType::Unit)
            )])
            .to_string(),
            "{`none}"
        );
        assert_eq!(
            Type::Variant(vec![(
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
            Type::Variant(vec![(FieldKey::Name("pair".into()), record)]).to_string(),
            "{`pair{a: Int, b: Int}}"
        );
    }

    /// An **anonymous positional** sum is not a tagged variant and keeps its own
    /// rendering: `++`/`CollectionUnion` produces `Index` keys that carry no
    /// user-meaningful information, so the arms print as a flat `A | B` join
    /// rather than being dressed up as surface arms nobody wrote.
    #[test]
    fn anonymous_positional_sum_still_renders_as_a_flat_join() {
        let anon = Type::Variant(vec![
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
}

#[cfg(test)]
mod sum_in_domain_position_tests {
    use super::*;

    fn sum_over(candidates: Vec<Type>) -> Type {
        Type::Sigma(Box::new(SigmaType::of(TypeKind::Enumerated(candidates))))
    }

    /// The shape the design rejects: a sum standing where a **data** function's domain
    /// belongs. "One of `𝐾`" describes no index, so a consumer reads it as a concrete
    /// index set and asks planning for the iteration extent of two ranges at once.
    #[test]
    fn a_sum_in_a_data_domain_is_rejected() {
        let ty = Type::data_fun(
            sum_over(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            Type::Base(BaseType::Int),
        );
        assert!(has_sum_in_domain_position(&ty), "{ty}");
    }

    /// Nested in the domain counts too: a two-generator comprehension's index is a *pair*,
    /// and a sum inside it is the same defect one level down.
    #[test]
    fn a_sum_nested_in_a_data_domain_counts() {
        let ty = Type::data_fun(
            Type::Tuple(vec![
                Type::UIntRange(2),
                sum_over(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            ]),
            Type::Base(BaseType::Int),
        );
        assert!(has_sum_in_domain_position(&ty), "{ty}");
    }

    /// A **compute** function's domain is exempt, and not as a concession: it is an
    /// ordinary parameter type, and passing a boxed value to a function is exactly what
    /// `box` is for.
    #[test]
    fn a_sum_in_a_compute_domain_is_an_ordinary_parameter() {
        let ty = Type::fun(
            sum_over(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            Type::Base(BaseType::Int),
        );
        assert!(!has_sum_in_domain_position(&ty), "{ty}");
    }

    /// And the *factored* sum — a collection whose domain is its own witness — is the
    /// normal form, not one standing where a domain belongs. Distinguishing the two is the whole point: they
    /// differ only in whether the body is the witness or a function of it.
    #[test]
    fn a_factored_collection_sum_is_not_one() {
        let ty = Type::Sigma(Box::new(SigmaType::over(
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            None,
            Type::Base(BaseType::Int),
        )));
        assert!(!has_sum_in_domain_position(&ty), "{ty}");
    }
}

#[cfg(test)]
mod witness_identity_tests {
    use super::*;

    /// Deriving carries the binder — a join widens a collection's candidates without
    /// making it a different collection.
    #[test]
    fn with_kind_keeps_the_witness() {
        let w = Witness::fresh(TypeKind::Enumerated(vec![Type::UIntRange(2)]));
        let wider = w.with_kind(TypeKind::Enumerated(vec![
            Type::UIntRange(2),
            Type::UIntRange(3),
        ]));
        assert_eq!(w.binder(), wider.binder());
    }

    /// Mapping the candidates is a derivation too, so it keeps the binder — this is what
    /// makes every pass's rebuild carry the identity without each one deciding to.
    #[test]
    fn map_types_keeps_the_witness() {
        let w = Witness::fresh(TypeKind::Enumerated(vec![Type::UIntRange(2)]));
        let mapped = w.map_types(|_| Type::UIntRange(9));
        assert_eq!(w.binder(), mapped.binder());
        assert_eq!(
            mapped.kind(),
            &TypeKind::Enumerated(vec![Type::UIntRange(9)])
        );
    }

    /// `fresh` is the one act of origination, so two of them are two witnesses even at an
    /// identical kind.
    #[test]
    fn fresh_witnesses_at_one_kind_stay_distinct() {
        let kind = TypeKind::Enumerated(vec![Type::UIntRange(2)]);
        assert_ne!(
            Witness::fresh(kind.clone()).binder(),
            Witness::fresh(kind).binder()
        );
    }

    /// α-conversion renames the body with the binder. Renaming one without the other is
    /// the stranding every constructor here exists to prevent, so the test asserts both
    /// halves moved together.
    #[test]
    fn alpha_convert_moves_the_body_with_the_binder() {
        let sum = SigmaType::over(
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            None,
            Type::Base(BaseType::Int),
        );
        let converted = sum.alpha_convert();
        assert_ne!(sum.binder(), converted.binder(), "a fresh binder");
        assert_eq!(
            *converted.body,
            Type::data_fun(
                Type::WitnessRef(converted.binder()),
                Type::Base(BaseType::Int)
            ),
            "and the body names it, not the old one"
        );
        assert_eq!(sum.kind(), converted.kind(), "the kind is unchanged");
    }
}

#[cfg(test)]
mod witness_subst_tests {
    use super::*;

    fn range(n: usize) -> Type {
        Type::UIntRange(n)
    }

    /// Build a sum over a fresh witness, its body written against that witness's binder.
    fn sum(
        kind: TypeKind,
        body: impl FnOnce(crate::ccl::infer_var::WitnessBinderId) -> Type,
    ) -> SigmaType {
        let witness = Witness::fresh(kind);
        let body = body(witness.binder());
        SigmaType::bound(witness, body)
    }

    /// A body that *is* the witness instantiates to the candidate itself — the
    /// unfactored shape `box` builds, where every part of the body varies.
    #[test]
    fn a_bare_witness_body_instantiates_to_the_candidate() {
        let s = sum(TypeKind::Enumerated(vec![range(3)]), |w| {
            Type::WitnessRef(w)
        });
        assert_eq!(s.instantiate_body(&range(3)), range(3));
    }

    /// A data-function body instantiates in its domain, leaving the codomain — the
    /// witness-independent residue — untouched.
    #[test]
    fn an_arrow_body_instantiates_only_its_domain() {
        let s = sum(TypeKind::UIntRanges, |w| {
            Type::data_fun(Type::WitnessRef(w), Type::Base(BaseType::Int))
        });
        assert_eq!(
            s.instantiate_body(&range(2)),
            Type::data_fun(range(2), Type::Base(BaseType::Int))
        );
    }

    /// A nested sum's body names the **inner** binder, so substituting the outer one
    /// leaves it alone. The rule is identity, not nesting position: this holds however
    /// deeply the inner sum sits, and would hold even if it did not nest at all.
    #[test]
    fn a_nested_sums_body_is_not_captured() {
        let inner = Type::Sigma(Box::new(sum(TypeKind::UIntRanges, Type::WitnessRef)));
        let outer = sum(TypeKind::Enumerated(vec![range(1)]), |_| inner.clone());
        assert_eq!(outer.instantiate_body(&range(1)), inner);
    }

    /// A candidate listed in a nested sum's **kind** is a type in the *outer* scope, so
    /// it may name the outer witness — and substituting the outer binder rewrites it,
    /// while the inner sum's own body is untouched in the same pass.
    #[test]
    fn a_nested_sums_candidates_are_in_the_outer_scope() {
        let outer_witness = Witness::fresh(TypeKind::Enumerated(vec![range(4)]));
        let outer_binder = outer_witness.binder();
        let inner = sum(
            TypeKind::Enumerated(vec![Type::WitnessRef(outer_binder)]),
            Type::WitnessRef,
        );
        let inner_binder = inner.binder();
        let outer = SigmaType::bound(outer_witness, Type::Sigma(Box::new(inner)));
        let Type::Sigma(got) = outer.instantiate_body(&range(4)) else {
            panic!("instantiating an arrow-free body keeps the nested sum");
        };
        assert_eq!(
            got.kind(),
            &TypeKind::Enumerated(vec![range(4)]),
            "the outer witness in the inner kind is substituted"
        );
        assert_eq!(
            &*got.body,
            &Type::WitnessRef(inner_binder),
            "the inner sum's own body still names its own binder"
        );
    }
}

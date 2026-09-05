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
/// pairing well-defined; it does not decide *identity*.
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
/// - [`FunKind::Data`] — `α ⤇ β`: the domain is a *collection*'s index set.
///   The domain *is* the data map, so a lossy domain is lost data;
///   joins of data functions must be lossless — never a meet. Two collections over
///   distinct domains have no common type at all; the sum that keeps both is
///   entered by `box`, a term ([`Builtin::Box`](crate::ccl::Builtin)), not by the join.
///
/// Set at introduction (list literals, comprehensions, `++`, registered
/// sources, and every `History` erasure are `Data`; `lambda`/`def` are
/// `Compute`). A rebuilt or erased function type is `Data` iff it types a
/// collection, and `Compute` iff it types something that is called. The domain
/// decides nothing: both kinds carry every domain type, so a rewrite that mints a
/// type takes the kind from the construct it is building, and a rewrite that
/// rebuilds one carries the kind it was handed ([`Type::fun_like`]). See
/// `design/type-inference.md`,
/// "4.6 Data vs compute functions".
///
/// FunKind is **inferred** (see `design/type-inference.md`,
/// "4.6 Data vs compute functions"):
/// where the structure fixes it (a list literal is `Data`, a scalar op is
/// `Compute`) a concrete kind is stamped; where it depends on use or on an
/// unresolved source (a map/comprehension) a [`FunKind::Var`] is minted and the
/// solver resolves it, like a type variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunKind {
    /// A compute function / capability (`⇒`): lossy meet at a join is fine.
    Compute,
    /// A data function / collection (`⤇`): the domain is data; joins must be lossless.
    ///
    /// Carries the **Σ binders** of the sum this function is, when it is one: a
    /// `Σ (σ : 𝐾). σ ⤇ 𝑉` is a data function binding `σ` over its domain, and the binder
    /// rides the function the way the Pi binder (`Fun::name`) rides it over the codomain. A
    /// plain collection carries none (`None`; an empty list is not a state). A sum and a
    /// plain collection are distinct types with no common upper bound in either direction.
    /// Behind `Option<Rc<…>>` so the slot costs a plain collection one niche-optimized
    /// pointer: `FunKind` sits in every `Type::Fun`, and `Type` is cloned pervasively.
    Data(Option<Rc<Vec<Witness>>>),
    /// An unresolved kind, pinned down by the solver at coalesce. Identity is by
    /// the variable's `uid`, so `FunKind` (and `Type`) keep deriving
    /// `PartialEq`/`Eq`/`Hash` — the [`FunKindVar`] impls compare by `uid` only.
    Var(Rc<FunKindVar>),
}

impl FunKind {
    /// The Σ binders this kind carries — empty for everything but a sum-carrying
    /// [`FunKind::Data`]. Outermost first.
    pub fn witnesses(&self) -> &[Witness] {
        match self {
            FunKind::Data(Some(ws)) => ws,
            _ => &[],
        }
    }

    /// The Σ binders this kind is **written** over — a concrete `Data` carrying a slot.
    ///
    /// A consumer's kind variable carries binders too ([`FunKindVar::binder_ids`]), and they
    /// are deliberately not reported here: they are the *scope* each arm's domain is renamed
    /// into, not a name the consumer states. The sum it turns out to be is formed at its
    /// domain position, where the references have merged (`named_by_domain` in
    /// `crate::ccl::infer::solver::coalesce`) — reading the binder off the kind instead
    /// names the index one way there and another at the position, and a reference resolving
    /// to the second escapes the first.
    pub fn sum_binders(&self) -> Option<Rc<Vec<Witness>>> {
        match self {
            FunKind::Data(Some(ws)) if !ws.is_empty() => Some(Rc::clone(ws)),
            _ => None,
        }
    }

    /// The binders a function of this kind **states**, with what each ranges over.
    ///
    /// A variable states none. It has binder *identities* once its arity is known
    /// ([`binder_ids`](Self::binder_ids)), but what they range over is the merge of what
    /// reached each position, which compaction answers — so a variable that reported a range
    /// here would be answering a question that is not the kind graph's, and the two answers
    /// would differ by whatever each walk did instead.
    ///
    /// Two *related* kinds have **corresponding** binders and not shared ones: what carries a
    /// reference from one to the other is the substitution the relating edge draws, which is
    /// what makes a reference correct across a change of context without every context
    /// having to agree on a name.
    pub fn named_binders(&self) -> Vec<Witness> {
        match self {
            FunKind::Var(_) => Vec::new(),
            other => other.witnesses().to_vec(),
        }
    }

    /// The identities of the binders a function of this kind is over, one per position —
    /// available whether or not the kind states what they range over.
    pub fn binder_ids(&self) -> Vec<WitnessId> {
        match self {
            FunKind::Var(v) => v.binder_ids(),
            other => other.witnesses().iter().map(|w| *w.id()).collect(),
        }
    }

    /// Mutable analog of [`witnesses`](Self::witnesses) — copy-on-write through the
    /// `Rc`, for a whole-type walk that rewrites every position together.
    pub fn witnesses_mut(&mut self) -> &mut [Witness] {
        match self {
            FunKind::Data(Some(ws)) => Rc::make_mut(ws).as_mut_slice(),
            _ => &mut [],
        }
    }

    /// The display arrow for this kind: `⇒` for compute, `⤇` for data. A variable
    /// renders by its pin, so a consumer function reads as the collection it is; an
    /// unpinned one renders `⇒`.
    pub fn arrow(&self) -> &'static str {
        match self {
            FunKind::Compute => "⇒",
            FunKind::Data(..) => "⤇",
            // Every data spelling reads as a collection: `Data` is data with plain-vs-sum
            // still open, and `Plain` and `Sum` are the two ways it settles. Rendering
            // those as `⇒` printed a collection as a capability.
            FunKind::Var(v) if v.resolved().is_data() => "⤇",
            FunKind::Var(_) => "⇒",
        }
    }

    /// This kind **as far as anything has determined it** — the one lattice a function's
    /// kind is answered in, whether it was written down or inferred.
    ///
    /// A concrete kind is its own answer; a variable's is what its component was pinned to.
    /// There is no second encoding of these states, so no phase can lose a distinction an
    /// earlier one made by translating between two spellings of the lattice.
    pub fn resolved(&self) -> KindPin {
        match self {
            FunKind::Compute => KindPin::Compute,
            FunKind::Data(None) => KindPin::Plain,
            FunKind::Data(Some(ws)) => KindPin::Sum(ws.len()),
            FunKind::Var(v) => v.resolved(),
        }
    }

    /// Whether a function of this kind may be **a sum** — its slot is filled, or its
    /// variable has not yet been narrowed away from one.
    ///
    /// `Data(None)` answers `false`: a plain collection and a sum are two of the three
    /// concrete kinds, and neither is below the other, so a phase that forms a sum from a
    /// plain collection is performing an edge `constrain_fun_kind` refuses.
    pub fn admits_sum(&self) -> bool {
        match self {
            FunKind::Compute => false,
            FunKind::Data(slot) => slot.is_some(),
            // **Unpinned is not a licence.** Nothing determined this kind, so it is not
            // known to be data at all, let alone a sum; admitting one here wraps a function
            // whose kind no value ever settled.
            FunKind::Var(v) => matches!(v.resolved(), KindPin::Data | KindPin::Sum(_)),
        }
    }

    /// How many binders a function of this kind is over, where anything has said.
    pub fn arity(&self) -> Option<usize> {
        self.resolved().arity()
    }

    /// A fresh inferred kind (a new [`FunKindVar`] with empty bounds).
    pub fn fresh_var() -> FunKind {
        FunKind::Var(FunKindVar::fresh())
    }

    /// A fresh kind variable **pinned to `Data`** — a consumer's function, polymorphic in
    /// the slot but a collection by construction (`src/ccl/design/type-inference.md`,
    /// "Consuming a sum: pinning the consumer's kind"). The kind equation relates it to
    /// a plain collection and to a sum alike; a capability flowing in is the conflict.
    pub fn fresh_data() -> FunKind {
        let v = FunKindVar::fresh();
        v.stamp_data();
        FunKind::Var(v)
    }
}

/// Stable identity of a [`FunKindVar`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunKindVarId(pub(crate) u32);

impl fmt::Display for FunKindVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\u{03ba}{}", self.0)
    }
}

static FUN_KIND_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

#[cfg(debug_assertions)]
thread_local! {
    /// Every kind variable minted on this thread, for [`dump_kind_vars`]. Diagnostic only —
    /// the counterpart of the inference arena, and read by nothing that decides anything.
    static KIND_VARS: RefCell<Vec<Rc<FunKindVar>>> = const { RefCell::new(Vec::new()) };
}

/// Every kind variable and everything recorded on it, newest last — the whole kind graph in
/// one place, for reading what the edges actually say.
#[cfg(debug_assertions)]
pub fn fun_kind_vars() -> Vec<Rc<FunKindVar>> {
    KIND_VARS.with(|ks| ks.borrow().clone())
}

/// A one-line rendering of every kind variable minted on this thread. Diagnostic only.
///
/// Debug-only with the register it reads: nothing outside a diagnostic consults it, and a
/// release build has no register to render.
/// Which inference variable owns each kind variable, for the dump — the reverse of
/// [`crate::ccl::InferVar::fun_kind`].
#[cfg(debug_assertions)]
fn kind_var_owners() -> std::collections::HashMap<u32, Vec<String>> {
    let mut out: std::collections::HashMap<u32, Vec<String>> = std::collections::HashMap::new();
    for v in crate::ccl::infer_var::arena_vars() {
        out.entry(v.fun_kind.uid.0)
            .or_default()
            .push(format!("?{}", v.uid.0));
    }
    out
}

#[cfg(debug_assertions)]
pub fn dump_kind_vars() -> String {
    fun_kind_vars()
        .iter()
        .map(|v| {
            let owners = kind_var_owners();
            match owners.get(&v.uid.0) {
                Some(os) => format!("{} owner={}", v.debug_dump(), os.join(",")),
                None => format!("{} owner=-", v.debug_dump()),
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// What a [`FunKindVar`] has been pinned to.
///
/// `Data` and `Compute` are **incomparable**, so a kind edge fixes a variable
/// rather than bounding it, and there is nothing to accumulate but which of the
/// two points something pinned it to. An [`crate::ccl::InferVar`] carries polar
/// bound *lists*; this carries one of four states, and since no [`Type`] sits
/// inside, a `FunKindVar` never forms a cycle.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum KindPin {
    /// Nothing pinned this kind: any of the three concrete kinds still satisfies it.
    #[default]
    Unpinned,
    /// Pinned to `Compute`.
    Compute,
    /// Pinned to **data**, with plain-vs-sum still open — what a consumer is minted at
    /// ([`FunKind::fresh_data`]). It excludes `Compute` and nothing else.
    Data,
    /// Pinned to a plain collection, [`FunKind::Data`] with no slot.
    Plain,
    /// Pinned to a sum over this many binders.
    ///
    /// The **arity**, not the binders. Whether a function is over binders and how many are
    /// facts about its kind — presence is what makes a sum and a plain arrow unrelatable —
    /// but *which* binder is not: a variable picks its binder names where its arity becomes
    /// known ([`FunKindVar::binder_ids`]), so naming them here would be a second answer.
    Sum(usize),
    /// Pinned to two kinds at once — read at coalesce
    /// ([`FunKind::resolved`]).
    Conflict,
}

impl KindPin {
    /// The join in the semilattice bottomed at `Unpinned` and topped by `Conflict`, with
    /// two chains between them: `Compute` alone, and `Data` below both `Plain` and every
    /// `Sum(𝑛)`. Points on different chains — and two `Sum`s of unequal arity — join to
    /// `Conflict`.
    ///
    /// Commutative, associative, and idempotent, which is what makes a
    /// variable's pin independent of the order the pins arrive in: every reader
    /// folds the same set and no fold step reads a value a later step can
    /// change.
    pub fn join(self, other: KindPin) -> KindPin {
        use KindPin::{Compute, Conflict, Data, Plain, Sum, Unpinned};
        match (self, other) {
            (Unpinned, p) | (p, Unpinned) => p,
            (Conflict, _) | (_, Conflict) => Conflict,
            (Compute, Compute) => Compute,
            // A capability meeting data, in any of its three spellings.
            (Compute, _) | (_, Compute) => Conflict,
            // `Data` says only "not a capability", so anything data refines it.
            (Data, p) | (p, Data) => p,
            (Plain, Plain) => Plain,
            // **A plain collection and a sum do not merge.** Neither is below the other:
            // entering a sum is a term, and a sum is not a collection with the choice
            // forgotten. One function required to be both is the same contradiction a
            // capability meeting a collection is.
            (Plain, Sum(_)) | (Sum(_), Plain) => Conflict,
            // **Two sums at one kind are one consumption reached twice.** Their arities
            // must agree; a disagreement is a mismatch between the two types, not a state
            // to reconcile.
            (Sum(a), Sum(b)) if a == b => Sum(a),
            (Sum(_), Sum(_)) => Conflict,
        }
    }

    /// Whether this pin admits only data — a collection, in either spelling.
    pub fn is_data(&self) -> bool {
        matches!(self, KindPin::Data | KindPin::Plain | KindPin::Sum(_))
    }

    /// How many binders this pin is over, where it says.
    ///
    /// **A plain collection binds nothing, and that is an answer.** `Plain` is one of the
    /// three settled points, so a comprehension built over a plain source adds zero
    /// positions to its own width; reading it as unknown loses the width of every *other*
    /// source beside it, and the comprehension then binds nothing at all. `Data` is the
    /// genuine absence — data with plain-vs-sum still open.
    pub fn arity(&self) -> Option<usize> {
        match self {
            KindPin::Sum(n) => Some(*n),
            KindPin::Plain => Some(0),
            _ => None,
        }
    }
}

/// What a [`FunKindVar`] has recorded — polar bounds, like any other variable's.
///
/// Everything a kind answers is *derived* from these rather than stored: whether it is a
/// collection at all, how many binders it is over, and what each of those binders ranges
/// over. That is what makes a fact reaching one end of an edge visible from the other, and
/// what removes any need to propagate by hand.
#[derive(Default)]
struct FunKindBounds {
    /// What **construction** said this kind is, before any edge.
    ///
    /// A consumer's function is data by construction ([`FunKind::fresh_data`]) with
    /// plain-vs-sum still open, and no `FunKind` spells that — `Data(None)` is already the
    /// plain collection. So it is a stamp rather than a bound: a fact about how the variable
    /// was made, folded in beside what the edges recorded.
    stamped: KindPin,
    /// Kinds recorded **below** this variable — what has flowed into it.
    lower: Vec<FunKind>,
    /// The kinds this one is a collection **built over**, in generator order.
    ///
    /// A different relation from the bounds, because it states something different. A
    /// `Fun <: Fun` edge relates two spellings of *one* collection, so the two are over the
    /// same number of binders and position *i* is position *i*. A comprehension is a
    /// collection built over its generators, so it binds one position per position of each —
    /// its arity is their **sum** and the correspondence is a concatenation. Recording it as
    /// a bound would claim a subtyping that does not hold and pair positions that are not
    /// the same position.
    built_over: Vec<FunKind>,
    /// Kinds recorded **above** it — what it must satisfy.
    upper: Vec<FunKind>,
    /// The kind this one is a **copy of**, where it was made by instantiating a scheme.
    ///
    /// Not a bound, and not a pair of them. Mutual bounds would say the two kinds are equal,
    /// which recouples the pins that freshening exists to separate — "a pin the definition
    /// site acquires later must not reach this instantiation" (`freshen_kind_var`). What a
    /// copy shares is *which binder each position is*, not what the kind resolves to, and a
    /// bound cannot say the first without saying the second.
    instantiated_from: Option<Rc<FunKindVar>>,
    /// This kind's binder names, one per position, picked where the arity became known.
    ///
    /// Not an `Option` per slot: a name is picked for every position at once, because the
    /// arity is what says how many there are, and nothing before it can name any of them.
    settled: Vec<crate::ccl::infer_var::WitnessBinderId>,
}

/// The combined width of the sources a collection is **built over**, or `None` where
/// nothing has said.
///
/// One position per position of each source, so the widths add. An empty list is not width
/// zero: a kind nothing was built over says nothing about its width, and folding it to `0`
/// would call every ordinary collection plain.
fn built_width(sources: &[FunKind]) -> Option<usize> {
    if sources.is_empty() {
        return None;
    }
    sources
        .iter()
        .map(FunKind::arity)
        .try_fold(0, |acc, n| Some(acc + n?))
}

/// A kind-inference variable — an unknown [`FunKind`], and **the identity of the binders the
/// function it kinds is over**: binder *i* is [`binder_ids`](Self::binder_ids)`[i]`, picked where
/// the arity becomes known.
///
/// The two eliminations cannot know a function's kind: applying a value and destructuring a
/// function are one node for a collection and for a capability alike. Each mints one of
/// these, and the kinds that reach it are recorded as bounds.
///
/// Bounds are **not identity**. Two variables related by an edge have *corresponding*
/// binders, not the same ones — which is what the Σ rule reads — and a substitution maps
/// between them, derived once the kind graph is closed and the arities are known.
///
/// Identity (`uid`) is immutable and lives outside the `RefCell`, so equality and hashing are
/// borrow-free and never inspect what has been recorded — mirroring [`crate::ccl::InferVar`].
pub struct FunKindVar {
    /// Stable, globally-unique identity — and, with a position, each binder's.
    pub uid: FunKindVarId,
    bounds: RefCell<FunKindBounds>,
}

impl FunKindVar {
    /// Allocate a fresh kind variable with nothing recorded.
    pub fn fresh() -> Rc<FunKindVar> {
        let v = Rc::new(FunKindVar {
            uid: FunKindVarId(FUN_KIND_VAR_COUNTER.fetch_add(1, Ordering::Relaxed)),
            bounds: RefCell::new(FunKindBounds::default()),
        });
        #[cfg(debug_assertions)]
        KIND_VARS.with(|ks| ks.borrow_mut().push(Rc::clone(&v)));
        v
    }

    /// Record `k` below (or above) this variable. Deduplicated by the point it denotes, so
    /// one edge drawn twice records once.
    pub fn record(&self, k: FunKind, lower: bool) {
        // A variable against itself says nothing, and recording it makes every reader walk
        // a cycle to find that out.
        if matches!(&k, FunKind::Var(v) if v.uid == self.uid) {
            return;
        }
        let mut b = self.bounds.borrow_mut();
        let side = if lower { &mut b.lower } else { &mut b.upper };
        if !side.iter().any(|x| same_fun_kind(x, &k)) {
            side.push(k);
        }
    }

    /// **What this kind is**, as far as everything recorded says: the join of every point
    /// that has reached it, from either side.
    ///
    /// Both sides, because the `FunKind` lattice is flat — a capability, a plain collection
    /// and a sum of a given width are mutually incomparable — so an edge fixes a variable
    /// rather than bounding it, and which side the fact arrived on says nothing.
    ///
    /// `seen` guards the walk: a collection reaches itself through a recurrence, so the
    /// relation is not required to be acyclic.
    pub fn resolved(&self) -> KindPin {
        fn go(v: &FunKindVar, seen: &mut Vec<FunKindVarId>) -> KindPin {
            if seen.contains(&v.uid) {
                return KindPin::Unpinned;
            }
            seen.push(v.uid);
            let b = v.bounds.borrow();
            // **What a collection is built over says what it is.** It binds one position
            // per position of each source, so its width is their sum — a sum of that
            // width, or a plain collection where the sources bind nothing. Answered here
            // rather than beside this, so "what is this kind" and "how wide is it" cannot
            // give different answers about one kind.
            let over = match built_width(&b.built_over) {
                Some(0) => KindPin::Plain,
                Some(n) => KindPin::Sum(n),
                None => KindPin::Unpinned,
            };
            b.lower
                .iter()
                .chain(b.upper.iter())
                .fold(b.stamped.clone().join(over), |acc, k| {
                    let point = match k {
                        FunKind::Var(x) => go(x, seen),
                        other => other.resolved(),
                    };
                    acc.join(point)
                })
        }
        go(self, &mut Vec::new())
    }

    /// Record that this collection is **built over** `src`, ahead of what is already there.
    ///
    /// See [`built_width`] for how the sources' widths add up to this one's.
    ///
    /// Front-first because a sum's positions are ordered — the outermost binds the first
    /// generator — and the caller that has sources to register walks them backwards to nest
    /// its applications. The order is the generator order, not the visit order.
    pub fn contributes_first(self: &Rc<Self>, src: FunKind) {
        self.bounds.borrow_mut().built_over.insert(0, src);
    }

    /// The kinds this one is built over, in generator order.
    pub fn built_over(&self) -> Vec<FunKind> {
        self.bounds.borrow().built_over.clone()
    }

    /// How many binders this kind's function is over, where anything has said.
    pub fn arity(&self) -> Option<usize> {
        self.resolved().arity()
    }

    /// **The names this kind's binders settle on**, minted once and answered from the kind
    /// thereafter — so every occurrence of one unsettled binder comes back as one name.
    ///
    /// Identity and nothing else. What a binder *ranges over* is the merge of what reached
    /// its position, which is `CompactTypeKind::merge`'s question and not the kind graph's
    /// (`var_binder_kind` in `crate::ccl::infer::solver::compact`). A second answer derived
    /// here is a second answer, and the two differ by whatever each walk did instead.
    pub fn binder_ids(self: &Rc<Self>) -> Vec<WitnessId> {
        let Some(arity) = self.arity() else {
            return Vec::new();
        };
        let ids: Vec<crate::ccl::infer_var::WitnessBinderId> = {
            let mut b = self.bounds.borrow_mut();
            if b.settled.len() < arity {
                b.settled
                    .resize_with(arity, crate::ccl::infer_var::fresh_witness_binder_id);
            }
            b.settled[..arity].to_vec()
        };
        ids.iter().copied().map(WitnessId).collect()
    }

    /// Stamp this kind **data** at construction — a collection whatever slot it turns out
    /// to have. The one fact that is not an edge, because no `FunKind` spells it.
    pub fn stamp_data(&self) {
        self.bounds.borrow_mut().stamped = KindPin::Data;
    }

    /// A one-line rendering of everything recorded, for tracing.
    pub fn debug_dump(&self) -> String {
        let (stamped, lower, upper, over) = {
            let b = self.bounds.borrow();
            (
                b.stamped.clone(),
                b.lower.clone(),
                b.upper.clone(),
                b.built_over.clone(),
            )
        };
        let f = |ks: &Vec<FunKind>| {
            ks.iter()
                .map(|k| match k {
                    FunKind::Var(v) => format!("k{}", v.uid.0),
                    FunKind::Data(Some(ws)) => format!(
                        "Sum[{}]",
                        ws.iter()
                            .map(|w| format!("{:?}", w.id()))
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                    other => format!("{:?}", other.resolved()),
                })
                .collect::<Vec<_>>()
                .join(",")
        };
        // The names this kind has picked, where it has picked any: a reader comparing a
        // dump against a rendered type needs to know which `σ@n` belongs to which kind.
        let names = self
            .bounds
            .borrow()
            .settled
            .iter()
            .map(|b| format!("\u{03c3}@{b}"))
            .collect::<Vec<_>>()
            .join(",");
        let from = match self.instantiated_from() {
            Some(o) => format!(" from=k{}", o.uid.0),
            None => String::new(),
        };
        format!(
            "k{} stamp={stamped:?} lower=[{}] upper=[{}] over=[{}] arity={:?} binds=[{names}]{from}",
            self.uid.0,
            f(&lower),
            f(&upper),
            f(&over),
            self.arity(),
        )
    }

    /// The kinds recorded **below** this variable, for a reader deriving the correspondences
    /// between its binders and theirs.
    pub fn lower(&self) -> Vec<FunKind> {
        self.bounds.borrow().lower.clone()
    }

    /// The kinds recorded **above** this one.
    pub fn upper(&self) -> Vec<FunKind> {
        self.bounds.borrow().upper.clone()
    }

    /// Record that this kind is a copy of `original` — see
    /// [`instantiated_from`](FunKindBounds::instantiated_from).
    pub fn copied_from(&self, original: &Rc<FunKindVar>) {
        self.bounds.borrow_mut().instantiated_from = Some(Rc::clone(original));
    }

    /// What this kind is a copy of, where it is one.
    pub fn instantiated_from(&self) -> Option<Rc<FunKindVar>> {
        self.bounds.borrow().instantiated_from.clone()
    }

    /// What this kind was stamped at construction — the one fact no edge spells
    /// ([`stamp_data`](Self::stamp_data)).
    pub fn stamped(&self) -> KindPin {
        self.bounds.borrow().stamped.clone()
    }
}

/// Whether two kinds are the **same bound** — the test for recording one twice.
///
/// Not whether they denote the same point of the lattice. Two sums of one arity are one
/// point and two different bounds: they bind *different* binders, and collapsing them drops
/// an arm of every conditional, so a variable would answer with the first collection that
/// reached it and never learn about the second.
fn same_fun_kind(a: &FunKind, b: &FunKind) -> bool {
    match (a, b) {
        (FunKind::Var(x), FunKind::Var(y)) => x.uid == y.uid,
        (FunKind::Var(_), _) | (_, FunKind::Var(_)) => false,
        // A sum is the binders it is over.
        (FunKind::Data(Some(x)), FunKind::Data(Some(y))) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| p.id() == q.id())
        }
        _ => a.resolved() == b.resolved(),
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
pub fn reset_fun_kind_var_counter() {
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
/// | `Infer(id)` | Type checker only | "Inference variable N from the coalesce pass" | End of inference for any type reachable from the program's root output (flagged as `UnresolvedInfer` by `collect_type_errors`); an induction accumulator's *domain* is necessarily `Infer` until the unified phase resolves it (see `Strictness::PreChannelize`) |
/// | `History` (`history_kind: Overwrite`) | Type checker only | "Mutable variable: a `value` cell tracked over a `domain` (loop index or transaction time)" | the unified phase (`transact_phase` / `mut_elim`, which runs *before* `channelize`; a survivor downstream is a compiler bug) |
/// | `History` (`history_kind: Append`) | Type checker only | "Feed channel `domain ⤇ value`: the defer binding's post-channelize stream type" | `channelize` (which runs after inference; a survivor downstream is a compiler bug) |
/// | `ChanDom(d, _)` | Type checker only | "Rigid nominal domain of feed channel `d` — its domain resolves at channel assembly" | `channelize` (substituted to the concrete channel domain; a survivor downstream is a compiler bug) |
///
/// A type is **concrete** when none of those variants occurs anywhere in it, nor
/// a [`FunKind::Var`]: it is what a checked program exhibits, and what every pass
/// after inference reads. The word is not "ground", which in logic means
/// variable-free — a concrete type may still carry a *free name*, since a
/// refinement predicate references an enclosing binder by name until landing
/// closes it to an index. [`crate::ccl::subst::type_contains_infer`] is the cheap
/// per-type check for the `Infer` case, and `check_fully_typed` the
/// whole-program one.
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
        /// Whether this function is a capability (`Compute`) or a data collection
        /// (`Data`). See [`FunKind`]. The derived [`PartialEq`] compares it: a
        /// data function and a compute function over the same domain/codomain
        /// are genuinely different types (one carries data, one a capability).
        ///
        /// Nothing structural distinguishes the two — only the construction
        /// site knows — so downstream the kind is *carried, never re-derived*:
        /// a typing rule reads it off the node's own type and a rewrite copies
        /// it from the type it replaces ([`Type::fun_like`]).
        fun_kind: FunKind,
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
    /// A base type narrowed by the conjunction of a [`RefinementSet`]'s refinements.
    ///
    /// **Invariants**, both established by [`Type::refined`] (which every
    /// construction site should go through rather than building this variant
    /// directly): the set is non-empty, and the base is not itself a
    /// `Refinement` — nested layers flatten into one set, so `{{𝑇 | 𝑝} | 𝑞}` is
    /// unrepresentable and the question "which layer is outermost" cannot be
    /// asked. See [`RefinementSet`] for why that question had no good answer.
    Refinement(Box<Type>, RefinementSet),
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
    /// may observe a `History` (a survivor at the strict `typecheck` is a compiler bug —
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
        history_kind: HistoryKind,
    },
    /// A **type-level reference to a Sigma's type-witness** — the witness in *domain*
    /// position, e.g. the body `WitnessRef ⤇ V` of a conditional collection.
    ///
    /// It carries **identity alone**: the binder it names. The
    /// range lives on the binder, and whether an occurrence is bound or free is a question
    /// about scope, asked where the answer is available
    /// (`src/ccl/design/type-inference.md`, "Consuming a sum: pinning the consumer's kind").
    ///
    /// One named leaf rather than two, or de Bruijn indices: a term can be decomposed and
    /// its pieces re-typed in a different order, so a positional encoding would have to be
    /// re-indexed by every pass that moves a type, while an identity survives the move. Two
    /// leaves — one for bound, one for free — would make every reader answer a scope
    /// question the scope walk already answers.
    ///
    /// **Not transient.** It is bound by its Σ and exactly as durable — `box(xs)`'s type
    /// carries one through inference and `lambda_elim` into planning. Two things remove it,
    /// neither a discharge to a concrete domain by the type system: **elimination**, when a
    /// consumer opens the sum, and **realization** (`planning::conditionals`), which erases
    /// the Σ and the `box` together after the type system is done. So none reaches
    /// op-conversion — by realization, not by being short-lived. One that does reach it (a
    /// witness over a kind that names no candidates, which cannot be realized) is rejected
    /// there by name.
    ///
    /// Named for the *reference*: the witness itself is the [`Witness`] in the function's
    /// slot ([`FunKind::Data`]), classified by a [`TypeKind`].
    WitnessRef(WitnessId),
    // Planned:
    // Pi { param: String, param_ty: Box<Type>, body_ty: Box<Type> }
}

/// **Which binder a witness is** — its name, and the whole of its identity.
///
/// A newtype over the name rather than the name itself: what a *binder* is called and what a
/// *position on a fun kind* is called are two questions, and only this one identifies a
/// witness.
/// Ordering is by the name, so a set of witnesses is stable across constraint arrival order.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WitnessId(pub crate::ccl::infer_var::WitnessBinderId);

impl WitnessId {
    /// The name this answers to.
    pub fn bound(&self) -> crate::ccl::infer_var::WitnessBinderId {
        self.0
    }
}

impl fmt::Display for WitnessId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl fmt::Debug for WitnessId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\u{03c3}@{}", self.0)
    }
}

/// **Γ — the kinds the witnesses in scope range over.**
///
/// A witness is a name, so a judgment made under binders carries what those binders range
/// over: `Γ ⊢ 𝐴 <: 𝐵` (`src/ccl/design/type-inference.md`, "The witness context"). A Σ's slot
/// is the extension it introduces, and this is the concatenation of the slots a walk has
/// entered.
///
/// Lookup by name, not membership: what a caller needs from a reference is the kind, and
/// asking the reference instead is what lets a second copy of it exist.
#[derive(Clone, Default, Debug)]
pub struct WitnessContext(Vec<Witness>);

impl WitnessContext {
    /// `Γ, σ₀ : 𝐾₀, …` — this context under one more Σ's binders.
    ///
    /// Innermost last, so a shadowing binder is found first. Nothing rebinds a witness name
    /// today (every binder is minted distinct), and the order costs nothing if one ever does.
    pub fn extended(&self, binders: &[Witness]) -> WitnessContext {
        if binders.is_empty() {
            return self.clone();
        }
        let mut out = self.0.clone();
        out.extend(binders.iter().cloned());
        WitnessContext(out)
    }

    /// What `id` ranges over, or `None` where Γ does not classify it — a reference outside
    /// every binder, which is what the escape check reports.
    pub fn type_kind_of(&self, id: &WitnessId) -> Option<TypeKind> {
        self.0
            .iter()
            .rev()
            .find(|w| w.id() == id)
            .map(Witness::type_kind)
    }
}

/// A **witness**: a type (a domain) that a dependent sum is summed over, and the binder its
/// [`Type::WitnessRef`] occurrences name.
///
/// Both halves in one value. The **[`TypeKind`]** classifies the types this binder ranges
/// over — named candidates ([`TypeKind::Enumerated`]), every index range
/// ([`TypeKind::UIntRanges`]), or the whole universe ([`TypeKind::Type`]) — which is what
/// keeps Σ subtyping to a single rule (kind containment plus body subtyping) with no case
/// per kind. The **binder**
/// is its identity, and it lives here rather than on the sum because a kind travelling
/// without one is how a witness acquires a second name: a site holding only a kind must
/// invent a binder to build a sum, and inventing is right only when the witness is new.
///
/// So the operations are named for the question a caller has to answer. Deriving —
/// [`map_types`](Self::map_types) — carries the binder; [`mint`](Self::mint) makes one and is
/// the visible act of saying "this is a different witness"; [`renamed`](Self::renamed) is the
/// same witness under another name, which a scheme instantiation owes each use.
///
/// It stays distinct from [`TypeKind`] itself: folding it in would make a Σ's witness field
/// *be* a kind, re-conflating "what the Σ is summed over" with the classifier filling it —
/// the collision the `WitnessRef` name exists to avoid. Identity is the [`WitnessId`] and
/// nothing else, so two references to one binder are equal by name and there is nothing to
/// reconcile after the fact.
#[derive(Clone)]
pub struct Witness {
    id: WitnessId,
    /// What a **settled** binder ranges over. An unsettled one answers from the bounds
    /// recorded at its position, which compaction reduces (`var_binder_kind`), so there is no
    /// second copy to go stale.
    range: Rc<TypeKind>,
}

// Identity-based, borrow-free: two witnesses are equal iff they share a `uid`. A derived
// comparison would make the same witness under a widened range compare unequal to itself.
impl PartialEq for Witness {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Witness {}
impl std::hash::Hash for Witness {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialOrd for Witness {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Witness {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}
impl fmt::Debug for Witness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.id)
    }
}

/// A **classifier of types** — which types it admits.
///
/// Used today only as the classifier of a Σ's type-witness ([`Witness`]), which is
/// the sole kind-carrying position in the grammar; since a Σ's witness is a data
/// function's domain, every type a kind classifies here happens to be a domain. That is
/// a fact about current usage, not part of the notion — nothing in
/// [`refuses`](TypeKind::refuses) is domain-specific.
///
/// Note the direction: a kind admits many types and a type is admitted by many kinds, so
/// there is no "kind of a type" to read off. What a type determines is the *minimal* kind
/// containing it, the singleton [`Enumerated`](TypeKind::Enumerated).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// Finitely many types, named one by one.
    Enumerated(Vec<Type>),
    /// Every **`UIntRange`**, which is the kind a `List`'s domain has. Not a finite
    /// candidate set (there is one range per length), and not a down-set of any
    /// single range either: the down-set of a large range would admit *sparse*
    /// subsets, whereas membership here is exactly "is a `Type::UIntRange`", i.e. a
    /// dense prefix. That distinction is load-bearing — it is what stops a
    /// *filtered* range `{[0, k) | p}` (a `Refinement`, not a `UIntRange`) passing
    /// as a `List`, which would supply a length witness for a domain that has holes.
    UIntRanges,
    /// Every type **below** a given one — the kind a `Map(K, V)`'s witness is summed
    /// over, written `SubtypesOf(K)`.
    SubtypesOf(Box<Type>),
    /// **Every** type — the kind a `Collection(T)`'s witness is summed over. It names no
    /// candidates, so nothing reads an extent off it. Named for the standard
    /// dependent-type-theory reading (the type of types) rather than for a subtyping ⊤:
    /// it is the top of the *kind* order, and says nothing about values.
    Type,
}

/// The `` `some `` tag of an `Option` — a value that is present.
///
/// Named here, beside [`Type::option_of`], because the runtime builds the same tag when it
/// answers a checked lookup (`FunctionDef::LookupChecked`). One spelling, two builders.
pub const V_SOME: &str = "some";
/// The `` `none `` tag of an `Option` — a value that is absent. See [`V_SOME`].
pub const V_NONE: &str = "none";

/// The kind part of a `Σ… ⤇ V` rendering — candidates in brackets, every other kind by
/// name. Brackets rather than braces because braces are the record type's, and candidates
/// are a sequence rather than a record.
impl fmt::Display for TypeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeKind::Enumerated(candidates) => {
                let cs: Vec<_> = candidates.iter().map(|t| t.to_string()).collect();
                write!(f, "[{}]", cs.join(", "))
            }
            TypeKind::SubtypesOf(k) => write!(f, "SubtypesOf({k})"),
            TypeKind::UIntRanges => write!(f, "UIntRanges"),
            TypeKind::Type => write!(f, "Type"),
        }
    }
}

impl TypeKind {}

impl TypeKind {
    /// The types this kind carries as **children** — every `Type` inside it, which
    /// substitution, freshening, extrusion and structural comparison must reach.
    ///
    /// A *superset* of an [`Enumerated`](Self::Enumerated) kind's candidates, and the
    /// distinction is not cosmetic. Candidates are the kind's *members*, compared by value
    /// and placed in the type lattice. A kind that names no members may still be
    /// **parameterized** by a type that is not one of them: a parameter is a child to be
    /// traversed and never a member to be matched, and conflating the two silently drops
    /// such a type from every traversal. [`SubtypesOf`](Self::SubtypesOf) is
    /// the standing example: its members are the types below its key type, not the key
    /// type itself, so the key is a child to be traversed and never a member to be matched.
    /// Reading it as a member would put it in the lattice; skipping it as a child would
    /// drop it from substitution, freshening, extrusion and structural comparison.
    pub fn children(&self) -> &[Type] {
        match self {
            // A variable carries kinds, never types, so a type traversal finds nothing.
            TypeKind::Enumerated(domains) => domains,
            // The **parameter**, not a domain: traversals must reach it, and the domain
            // lattice must never match against it.
            TypeKind::SubtypesOf(k) => std::slice::from_ref(k),
            TypeKind::UIntRanges | TypeKind::Type => &[],
        }
    }

    /// Mutable analog of [`children`](Self::children).
    pub fn children_mut(&mut self) -> &mut [Type] {
        match self {
            TypeKind::Enumerated(domains) => domains,
            TypeKind::SubtypesOf(k) => std::slice::from_mut(k),
            TypeKind::UIntRanges | TypeKind::Type => &mut [],
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
            TypeKind::SubtypesOf(k) => TypeKind::SubtypesOf(Box::new(f(k))),
            TypeKind::UIntRanges | TypeKind::Type => self.clone(),
        }
    }

    /// Whether this kind **refuses** `ty` — certain non-membership, which is the half of the
    /// membership question every caller of this needs.
    ///
    /// All three ask it to reject: `answer_type_kinds` and `candidate_in_kind` raise
    /// `NotOfKind`, and `coalesce_compact_go` raises `KindMismatch`. So the dangerous answer
    /// is the negative one, and a structural test that reports a difference it cannot yet
    /// distinguish from an unresolved position refuses a program that type-checks. Membership
    /// is three-valued while a type is partial; this answers only the value a rejection may
    /// rest on, and abstains — returns `false` — wherever the truth is unknown.
    ///
    /// **Abstaining is not the same as admitting.** Nothing reads a `false` here as
    /// membership, so an abstention costs detection and never correctness. That is why the
    /// bound's arm can abstain outright: the parameter's real question is subtyping, which
    /// `constrain_type_kinds` draws as an edge, and no structural test standing in for it can
    /// be certain in either direction.
    ///
    /// Membership and kind containment are different questions with different shapes: this
    /// takes one type and answers about one kind, and it decides for itself. Containment takes
    /// two kinds and draws edges, so it lives with the solver
    /// (`crate::ccl::infer::solver::constrain`, `constrain_type_kinds`). They meet in one
    /// place — candidates lie below [`UIntRanges`](TypeKind::UIntRanges) exactly when it
    /// admits every one of them — which is why a new kind needs this and a row in the order,
    /// and nothing else.
    ///
    /// That the membership question can be *asked at all* is what makes type-kind
    /// **variables** unnecessary: it is decidable from the classified type, so the only thing
    /// inference can be missing is that type. Contrast [`FunKind`], which classifies
    /// provenance rather than shape and therefore has no such question and does need
    /// [`FunKindVar`]. See `src/ccl/design/type-inference.md`, "An unresolved candidate
    /// becomes a kinding edge".
    ///
    /// Note the asymmetry with a *type*: a kind admits many types, and a type is admitted by
    /// many kinds. There is no "kind of a type" to read off — only, for a given type, the
    /// minimal kind containing it: that one type as the sole candidate.
    pub fn refuses(&self, ty: &Type) -> bool {
        match self {
            // ⊤: every type, so nothing to refuse.
            TypeKind::Type => false,
            // A dense prefix range, and nothing else. A `Refinement` over one is not a
            // `UIntRange`, so a filtered collection is refused — it would be handed a length
            // witness for a domain with holes. An unresolved head is the one thing this
            // cannot read, and it abstains there.
            TypeKind::UIntRanges => !matches!(
                ty,
                Type::UIntRange(_) | Type::Infer(_) | Type::Hole | Type::SharedHole(_)
            ),
            // **Membership here is subtyping**, which belongs to the solver: constraint time
            // draws the edge (`super::infer::solver::constrain`, `constrain_type_kinds`)
            // rather than asking this. A caller with no graph to draw into therefore has no
            // answer, and had one anyway before — an exact match, which refuses every strict
            // subtype the bound admits.
            TypeKind::SubtypesOf(_) => false,
            // A candidate list names its members, so membership is type equality — a
            // candidate *is* a domain and data domains are invariant, so a refined range is a
            // different candidate from the range it refines. Equality is certain only once
            // both sides are: an unresolved position on either can still be filled to match.
            TypeKind::Enumerated(domains) => {
                !ty.holds_an_unresolved_position()
                    && !domains.iter().any(Type::holds_an_unresolved_position)
                    && !domains.contains(ty)
            }
        }
    }
}

impl Type {
    /// `Σ (𝑤: kind). 𝑤 ⤇ codomain` — the shape every data-function sum has: a **new**
    /// witness, riding the function that binds it ([`FunKind::Data`]'s slot), and a domain
    /// that is the reference to it.
    ///
    /// The single place a kind classifies a Σ's witness, so it is where a candidate-naming
    /// kind is checked for having any.
    pub fn sum_over(type_kind: TypeKind, name: Option<crate::ccl::Name>, codomain: Type) -> Type {
        // **No candidates** leaves the witness no domain it could be, so `Σ (𝐷 : []). 𝐷 ⤇ 𝑉`
        // is a collection type nothing inhabits — and it is not caught downstream: it is
        // vacuously contained in every kind (a `∀` over no candidates), so it propagates as
        // a plausible ⊥ instead of failing. Callers that compute candidates must decide what
        // an empty result means before building a sum from it.
        assert!(
            !matches!(&type_kind, TypeKind::Enumerated(domains) if domains.is_empty()),
            "a Σ's witness type_kind names no domain at all"
        );
        // **The witness ranges over an index, and the candidates are what is recorded below
        // it.** A witness whose range is written directly carries no index to be identified
        // by, so two occurrences of it can be compared only by name — and a name is minted
        // per derivation. Behind a variable, an occurrence denotes the index whatever name
        // it was written with, and instantiating the sum freshens the variable's bounds the
        // way instantiating any scheme freshens a type variable's.
        let witness = Witness::mint(type_kind);
        let domain = Type::WitnessRef(*witness.id());
        Type::Fun {
            name,
            fun_kind: FunKind::Data(Some(Rc::new(vec![witness]))),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// `body` bound over `witness` — the function's slot gains the binder, outermost first.
    ///
    /// The only way to put an existing witness onto a function, because with the binder
    /// inside the [`Witness`] there is no second question to answer: minting, deriving and
    /// renaming are all choices about *which witness*, made before you get here
    /// ([`Witness::mint`], [`Witness::map_types`], or simply reusing one).
    ///
    /// **The body must mention its witness.** A sum whose body does not records a choice
    /// nothing can observe. Asserting it here rather than at the boundaries a sum crosses is
    /// what makes the shape unconstructible: the one substitution that could otherwise
    /// produce it **opens** the function binding the witness it instantiates
    /// ([`WitnessMapping::Discharge`](crate::ccl::subst::WitnessMapping::Discharge))
    /// instead of walking through it.
    pub fn sum_binding(witness: Witness, body: Type) -> Type {
        debug_assert!(
            mentions_witness(&body, witness.id()),
            "a sum's body must mention its own witness, but {body} does not mention {:?}",
            witness.id().clone()
        );
        let Type::Fun {
            name,
            fun_kind: FunKind::Data(slot),
            domain,
            codomain,
        } = body
        else {
            unreachable!("a sum's body is a data function, got a non-data shape")
        };
        // One binder per unification class: two nesting levels can materialize the same
        // root — a chooser reached through two identities — and a binder listed twice
        // binds nothing the first occurrence does not.
        let root = *witness.id();
        if let Some(rest) = &slot
            && rest.iter().any(|w| *w.id() == root)
        {
            return Type::Fun {
                name,
                fun_kind: FunKind::Data(slot),
                domain,
                codomain,
            };
        }
        // The new binder goes outermost; the body's occurrences already name it.
        let mut ws = vec![witness.clone()];
        if let Some(rest) = slot {
            ws.extend(rest.iter().cloned());
        }
        Type::Fun {
            name,
            fun_kind: FunKind::Data(Some(Rc::new(ws))),
            domain,
            codomain,
        }
    }

    /// The Σ binders this type carries — `Some` exactly when it is a sum. Outermost
    /// first; every binder scopes over the domain (and its refinements), never the
    /// codomain, which is the witness-independent residue.
    pub fn sum(&self) -> Option<&[Witness]> {
        match self {
            Type::Fun {
                fun_kind: FunKind::Data(Some(ws)),
                ..
            } if !ws.is_empty() => Some(ws),
            _ => None,
        }
    }

    /// The body at a given candidate — `𝐵[𝑑]`: the **outermost** binder dropped from the
    /// slot and its occurrences replaced throughout.
    ///
    /// Every Σ rule is stated in terms of this: subtyping is
    /// `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁. 𝐵₀[𝑑] <: 𝐵₁[𝑒]` and elimination is `∀ 𝑑 ∈ 𝐾. 𝐵[𝑑] <: 𝑈`
    /// (`src/ccl/design/type-inference.md`, "How a sum flows through the solver").
    pub fn instantiate_sum(&self, candidate: &Type) -> Type {
        let Some([first, ..]) = self.sum() else {
            unreachable!("instantiate_sum on a type that is not a sum: {self}")
        };
        let binder = *first.id();
        let out = crate::ccl::subst::Subst::discharge_witness(&binder, candidate).apply_type(self);
        // **The body really is instantiated.** Every Σ rule compares instantiated bodies,
        // and an occurrence surviving here would be a rule comparing `𝐵` where it states
        // `𝐵[𝑑]`. Bound and free are spelled the same, so no downstream site can tell them
        // apart; the invariant is asserted where it is established, which is also the only
        // place it is provable.
        debug_assert!(
            !mentions_witness(&out, &binder),
            "instantiating `𝐵[𝑑]` left an occurrence of the witness behind: {out}"
        );
        out
    }

    /// This sum **under fresh binders**, its occurrences renamed with them.
    ///
    /// What instantiating a scheme owes a sum: a scheme binds its witnesses, so each
    /// instantiation needs its own or every use names the ones the scheme wrote — and
    /// `box`'s scheme is a single sum, so sharing it would make every `box` in a program
    /// name one witness.
    pub fn alpha_convert_sum(&self) -> Type {
        let Some(ws) = self.sum() else {
            return self.clone();
        };
        // **A scheme binds its witnesses, so each instantiation owes itself its own.**
        // Sharing them would make every use of `box` name the binder the scheme was written
        // with, joining independent collections onto one.
        let fresh: Vec<Witness> = ws.iter().map(|w| Witness::mint(w.type_kind())).collect();
        let renames = ws
            .iter()
            .zip(&fresh)
            .fold(crate::ccl::subst::Subst::id(), |acc, (old, new)| {
                acc.extended_witness_rename(old.id(), new.id())
            });
        let mut out = renames.apply_type(self);
        let Type::Fun { fun_kind, .. } = &mut out else {
            unreachable!("a sum is a function")
        };
        *fun_kind = FunKind::Data(Some(Rc::new(fresh)));
        out
    }
}

impl Witness {
    /// The binder a written sum introduces — the only origination, and it happens where a
    /// sum is *built* ([`Type::sum_over`]) or where a kind variable picks its names
    /// ([`FunKindVar::binder_ids`]). A binder minted anywhere else is a second name for
    /// something that already had one.
    pub(crate) fn mint(type_kind: TypeKind) -> Witness {
        Witness {
            id: WitnessId(crate::ccl::infer_var::fresh_witness_binder_id()),
            range: Rc::new(type_kind),
        }
    }

    /// A settled binder re-formed from a name already in circulation and what it ranges
    /// over — the representation boundary. Materialization crosses it, converting a
    /// [`CompactTypeKind`](crate::ccl::infer::solver::compact::CompactTypeKind) back to a
    /// [`TypeKind`], and `Type::without_witness_binders` re-binds on purpose to assign de
    /// Bruijn depth.
    pub fn bound_to(
        binder: crate::ccl::infer_var::WitnessBinderId,
        type_kind: TypeKind,
    ) -> Witness {
        Witness {
            id: WitnessId(binder),
            range: Rc::new(type_kind),
        }
    }

    /// A binder re-formed from an id already in circulation and what it ranges over — for a
    /// rename, which carries the binder to another id without changing what it stands for.
    pub fn with_id(id: WitnessId, type_kind: TypeKind) -> Witness {
        Witness {
            id,
            range: Rc::new(type_kind),
        }
    }

    /// **Which binder this is.** The whole of identity; a caller that needs a name matches
    /// on it rather than being handed one that may not exist.
    pub fn id(&self) -> &WitnessId {
        &self.id
    }

    /// What this binder ranges over — written for a settled one, read from the bounds at its
    /// position for an unsettled one. One question, so one method.
    pub fn type_kind(&self) -> TypeKind {
        (*self.range).clone()
    }

    /// The type children this binder carries, **borrowed** — for a walk whose lifetime ties
    /// what it collects to the type it is walking. A settled binder's kind is written, so
    /// there is something to borrow; an unsettled one's lives on its kind variable.
    pub fn children(&self) -> &[Type] {
        self.range.children()
    }

    /// The type children this binder carries — its kind's candidates and bounds.
    pub fn types(&self) -> &[Type] {
        self.range.children()
    }

    /// Mutable analog of [`types`](Self::types). Copy-on-write through the `Rc`, which keeps
    /// the identity: a binder whose candidates were rewritten is the same binder.
    pub fn types_mut(&mut self) -> &mut [Type] {
        Rc::make_mut(&mut self.range).children_mut()
    }

    /// This binder under another name, ranging over the same thing — an α-conversion.
    pub fn renamed(&self, id: WitnessId) -> Witness {
        Witness {
            id,
            range: Rc::clone(&self.range),
        }
    }

    /// This binder with `f` applied to each of its kind's children.
    pub fn map_types(&self, f: impl FnMut(&Type) -> Type) -> Witness {
        Witness {
            id: self.id,
            range: Rc::new(self.range.map_children(f)),
        }
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

// Wire shape (inspector): a `Type` serializes as its rendered
// `Display` string (`"Int"`, `"Int -> Int"`), not structurally — the inspector
// schema wants the human type rendering, and structural serialization of the
// type AST would leak internals (`Infer` ids, holes) the client never wants.
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

// This rendering IS the inspector wire format for types — the serde impl above
// `collect_str`s it, and the golden fixtures pin it byte-exactly on every
// `type` field. Changing any notation here (`⇒`, `[0, N]`, `Mut(…)`, the
// singleton spelling, braces) is a deliberate corpus-wide re-bless: rerun
// cambra-inspector/scripts/regen-fixtures.sh and commit the classified diff.
/// Renders through [`fmt_type`] with no enclosing function: a self-contained
/// type carries every function its references name, so the spelling is
/// complete. A type shown detached from a function that binds one of its references renders that
/// reference as its bare index — see [`symbolic::PiBinderEnv`].
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_type(f, self, None)
    }
}

/// `ty` rendered inside `binders` — the [`Display`](fmt::Display) form of
/// [`fmt_type`], for a caller that holds an environment and needs a type
/// string. The symbolic printer takes this for the type slots it renders
/// inside a refinement predicate, so a reference to an enclosing function
/// prints as that function's binder name there too.
pub(crate) struct TypeUnder<'a, 'b>(
    pub(crate) &'a Type,
    pub(crate) Option<&'a symbolic::PiBinderEnv<'b>>,
);

impl fmt::Display for TypeUnder<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_type(f, self.0, self.1)
    }
}

/// Render `ty` inside `binders`, the functions the rendering has descended
/// through. Threading them is what lets a refinement predicate print a
/// reference to one of them by that function's own binder name rather than
/// as a de Bruijn index (`src/ccl/design/type-inference.md`, "Display opens
/// what it descended through").
fn fmt_type(
    f: &mut fmt::Formatter<'_>,
    ty: &Type,
    binders: Option<&symbolic::PiBinderEnv<'_>>,
) -> fmt::Result {
    /// `ty` in the same environment, as something `write!` can take directly, so
    /// a single-child arm formats straight into `f`. The `Tuple`/`Record`/`Variant`
    /// arms still materialize a `String` per child, because they `join` them.
    fn at<'a, 'b>(
        ty: &'a Type,
        binders: Option<&'a symbolic::PiBinderEnv<'b>>,
    ) -> TypeUnder<'a, 'b> {
        TypeUnder(ty, binders)
    }
    match ty {
        Type::Base(b) => write!(f, "{}", b.keyword()),
        // `n == 0` means an empty range (e.g. the domain of `[]`); render
        // it as `∅` instead of computing `n - 1` and underflowing.
        Type::BoundedHole(t) => write!(f, "<:{}", at(t, binders)),
        Type::UIntRange(0) => write!(f, "∅"),
        Type::UIntRange(n) => write!(f, "[0, {}]", n - 1),
        // The rendered symbol reflects the resolved `kind`: `⇒` for a compute
        // capability (and an unresolved kind var), `⤇` for a data collection
        // (see `FunKind::function`), making the collection/capability distinction
        // legible in every type string.
        //
        // The codomain renders one function deeper, named or not: the index
        // counts crossings, so an unnamed one occupies an entry too.
        Type::Fun {
            name,
            fun_kind,
            domain,
            codomain,
        } => {
            // A sum renders as its binder prefixes then the function they bind over. The
            // binder is written, and its **id is not**: rendering the id would make
            // every golden depend on minting order for a distinction no reader of a
            // single type needs; two sums that differ only in binder identity are
            // α-equivalent, and `without_witness_binders` is how code compares them.
            for w in fun_kind.witnesses() {
                if show_binders() {
                    write!(f, "Σ ({} : {}). ", w.id(), w.type_kind())?;
                } else {
                    write!(f, "Σ (σ : {}). ", w.type_kind())?;
                }
            }
            let inner = symbolic::PiBinderEnv::crossing(binders, name.as_ref());
            let cod = at(codomain, Some(&inner));
            let dom = at(domain, binders);
            match name {
                Some(x) => write!(f, "(({x}: {dom}) {} {cod})", fun_kind.arrow()),
                None => write!(f, "({dom} {} {cod})", fun_kind.arrow()),
            }
        }
        Type::Tuple(ts) => {
            let parts: Vec<_> = ts.iter().map(|t| at(t, binders).to_string()).collect();
            write!(f, "({})", parts.join(", "))
        }
        Type::Record(fields) => {
            let parts: Vec<_> = fields
                .iter()
                .map(|(n, t)| format!("{n}: {}", at(t, binders)))
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
                let parts: Vec<_> = payloads
                    .iter()
                    .map(|t| at(t, binders).to_string())
                    .collect();
                write!(f, "{}{ellipsis}", parts.join(" | "))
            } else {
                // CHL's surface spelling — see `fmt_variant_arms`. A `Unit`
                // payload is the nullary constructor and renders bare.
                crate::util::fmt_variant_arms(
                    f,
                    tags.iter().map(|(n, t)| {
                        let payload = match t {
                            Type::Base(BaseType::Unit) => None,
                            _ => Some(at(t, binders).to_string()),
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
        // Refinements render comma-separated (`{Int | p, q}`) — a conjunction.
        // Sorted, because the set is unordered: a rendering must not depend
        // on which order refinements happened to be inserted in, or a diagnostic
        // (or a test comparing rendered types) would see a difference that
        // the type system says is not there.
        //
        // Each refinement renders inside `binders`, so a reference to an enclosing
        // function prints as that function's binder name.
        Type::Refinement(t, refinements) => match singleton_value(ty) {
            Some(lit) => write!(f, "{}@{}", at(t, binders), symbolic::symbolic(lit)),
            None => {
                let mut rendered: Vec<String> = refinements
                    .iter()
                    .map(|r| symbolic::symbolic_under(&r.predicate, binders))
                    .collect();
                rendered.sort();
                write!(f, "{{{} | {}}}", at(t, binders), rendered.join(", "))
            }
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
            history_kind,
        } => {
            let (value, domain) = (at(value, binders), at(domain, binders));
            if *history_kind == HistoryKind::Overwrite {
                write!(f, "Mut({value}, {domain})")
            } else {
                write!(f, "feed({domain} ⤇ {value})")
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
                write!(f, "{b}")
            } else {
                write!(f, "σ")
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
    let Type::Refinement(_, refinements) = ty else {
        return None;
    };
    // Exactly one refinement: a base carrying further restrictions is not a singleton.
    let r = refinements.sole()?;
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
    /// Two spellings for one type would fail
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
            fun_kind: FunKind::Compute,
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
    /// The spellings live in [`V_SOME`]/[`V_NONE`] rather than here, because the runtime
    /// builds the same tags when it answers a checked lookup; when type aliases land this
    /// is replaced by a prelude `` Option(T) = {`some{T} | `none} `` and deleted.
    ///
    /// Tags are listed in **name order** (`none` before `some`) on purpose: the
    /// solver materializes a coalesced variant from a `BTreeMap`, so an inferred
    /// variant's tags always come out name-ordered. Writing the abbreviation in
    /// that same order is what lets an `Option(T)` *annotation* compare equal to
    /// the inferred type structurally instead of differing only by tag order.
    pub fn option_of(payload: Self) -> Self {
        Type::variant(vec![
            (FieldKey::Name(V_NONE.into()), Type::Base(BaseType::Unit)),
            (FieldKey::Name(V_SOME.into()), payload),
        ])
    }

    /// The payload of an [`option_of`](Self::option_of), or `None` for any other type.
    ///
    /// The constructor's inverse, for a rule that recovers an answer it recorded earlier
    /// rather than recomputing it.
    pub fn option_payload(&self) -> Option<&Self> {
        let Type::Variant(arms, Openness::Closed) = self else {
            return None;
        };
        let [(none, _), (some, payload)] = arms.as_slice() else {
            return None;
        };
        (*none == FieldKey::Name(V_NONE.into()) && *some == FieldKey::Name(V_SOME.into()))
            .then_some(payload)
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
    /// constructed function never carries a free name for its own binder and
    /// two α-variant function types are structurally identical. See
    /// `src/ccl/design/type-inference.md`, "Where the conversions run".
    pub fn pi(name: impl Into<crate::ccl::Name>, domain: Self, codomain: Self) -> Self {
        Type::pi_kinded(name, domain, codomain, FunKind::Compute)
    }

    /// [`Type::pi`] at an explicit kind, for a rebuild that carries the `FunKind`
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
        fun_kind: FunKind,
    ) -> Self {
        let name = name.into();
        let codomain = crate::ccl::subst::close_pi_binder(&name, &codomain);
        Type::Fun {
            name: Some(name),
            fun_kind,
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
            Type::Fun { fun_kind, .. } => Some(fun_kind),
            _ => None,
        }
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
    /// a kind and are for a position that means one of the two.
    pub fn pi_eliminated(name: impl Into<crate::ccl::Name>, domain: Self, codomain: Self) -> Self {
        Type::pi_kinded(name, domain, codomain, FunKind::fresh_var())
    }

    /// The non-dependent [`Type::pi_eliminated`] — an elimination's demand
    /// with no Pi binder.
    pub fn fun_eliminated(domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: None,
            fun_kind: FunKind::fresh_var(),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Helper for creating a non-dependent **data** function type
    /// (`name: None`, `kind: Data`) — a collection `domain ⤇ codomain`.
    pub fn data_fun(domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: None,
            fun_kind: FunKind::Data(None),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// A **consumer's** collection function: data by construction, polymorphic in the
    /// slot ([`FunKind::fresh_data`]) so a plain collection and a sum satisfy it alike.
    pub fn consumer_fun(domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: None,
            fun_kind: FunKind::fresh_data(),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// `rebuilt` wearing the sum `exemplar` carries, or `rebuilt` unchanged where there is
    /// none to put back.
    ///
    /// **A sum is a fact about a node, not about its parts.** The binder rides the kind and
    /// the codomain mentions no witness, so nothing a reconstruction reads from a node's
    /// children says its morphism is a collection over one — the lambda rule builds a
    /// compute Pi, and the point-free construction builds a plain function. Every pass that
    /// rebuilds a Σ-typed node therefore has to put the wrapper back from what the node
    /// records, and did so three times with the guard written out each time.
    ///
    /// The domain and codomain still come from `rebuilt`, so a genuine disagreement about
    /// either survives whatever comparison follows.
    pub fn sum_like(exemplar: &Type, rebuilt: Type) -> Type {
        match (exemplar.sum(), rebuilt.domain(), rebuilt.codomain()) {
            (Some(_), Some(d), Some(c)) => Type::fun_like(exemplar, d, c),
            _ => rebuilt,
        }
    }

    /// Rebuild a function type copying `name` and `kind` from an `exemplar`
    /// `Fun`, so a downstream rebuild (lambda elimination, inlining, planning)
    /// can never silently flip a data function to compute or drop its Pi binder. A
    /// non-`Fun` exemplar yields a plain `Compute` function type with no binder —
    /// the safe default at a site with no function type to copy from.
    ///
    /// **A feed channel is a function too**, before `channelize` has made it one: a
    /// [`HistoryKind::Append`] history states the stream `domain ⤇ value`, and
    /// `channelize::erase_chan_domains_in_type` erases it to exactly that. A pass that
    /// rebuilds around a still-unerased handle — the chain a per-iteration feed becomes —
    /// has a kind to copy, and taking the `Compute` default there declares a collection a
    /// capability. ([`HistoryKind::Overwrite`] is not this case: a mutable variable handle
    /// erases to its *value*, so it states no arrow to copy.)
    ///
    /// **A sum is a function.** `Σ (𝑤 : 𝐾). (𝑤 ⤇ 𝑉)` is a collection exactly as `𝐷 ⤇ 𝑉`
    /// is; the witness binder only says its domain is whichever candidate was taken. So
    /// a sum exemplar rebuilds its *body* and puts the result back under the same
    /// witness — dropping that binder is the same silent loss as flipping the kind, and
    /// it is worse, because the rebuilt domain is usually the witness itself and a
    /// `WitnessRef` outside its binder means nothing at all.
    pub fn fun_like(exemplar: &Type, domain: Self, codomain: Self) -> Self {
        match exemplar {
            Type::Fun { name, fun_kind, .. } => {
                // The exemplar's kind is copied as it stands, variable included: a
                // variable *is* the kind at that position, and reading what the solver has
                // recorded on it would make a rebuild depend on when it ran.
                // Construction closes (see [`Type::pi`]): a rebuild computes
                // its codomain from node types, which reference the binder by
                // name. Idempotent on a codomain extracted from a closed
                // function — its references are already indices.
                let codomain = match name {
                    Some(b) => crate::ccl::subst::close_pi_binder(b, &codomain),
                    None => codomain,
                };
                Type::Fun {
                    name: name.clone(),
                    fun_kind: fun_kind.clone(),
                    domain: Box::new(domain),
                    codomain: Box::new(codomain),
                }
            }
            Type::History {
                history_kind: HistoryKind::Append,
                ..
            } => Type::data_fun(domain, codomain),
            _ => Type::fun(domain, codomain),
        }
    }

    /// Is this a type inference has yet to determine — a [`Type::Hole`] placeholder
    /// or an unsolved [`Type::Infer`] variable?
    ///
    /// The rebuilding constructors below refuse to build a function type over one:
    /// a type derived from a placeholder is a guess, and `Hole` is the answer
    /// inference can still fill.
    pub fn is_unresolved(&self) -> bool {
        matches!(self, Type::Hole | Type::Infer(_))
    }

    /// [`Self::fun_like`], returning [`Type::Hole`] when either side is unresolved.
    ///
    /// The rebuilding passes set a result type only where concrete type information
    /// is available, leaving `Hole` for inference to fill rather than committing to a
    /// type built from one.
    pub fn fun_like_or_hole(exemplar: &Type, domain: &Type, codomain: &Type) -> Self {
        if domain.is_unresolved() || codomain.is_unresolved() {
            Type::Hole
        } else {
            Type::fun_like(exemplar, domain.clone(), codomain.clone())
        }
    }

    /// [`Self::fun`] — a `Compute` function with no Pi binder — returning
    /// [`Type::Hole`] when either side is unresolved.
    ///
    /// Callers are the sites where `Compute` is the answer rather than a default: the
    /// type a built-in carries when it stands in a node's function slot (`zip`,
    /// `curry`, `const`, `apply`, an aggregate). Such a built-in transforms morphisms
    /// and has no data behind it, and whatever kind does matter rides the `codomain`
    /// the caller computed. Rebuilding a morphism's own type is the other case and
    /// takes [`Self::fun_like_or_hole`]; `Compute` there reads a collection as a
    /// compute function and strands its consumer.
    pub fn compute_fun_or_hole(domain: &Type, codomain: &Type) -> Self {
        if domain.is_unresolved() || codomain.is_unresolved() {
            Type::Hole
        } else {
            Type::fun(domain.clone(), codomain.clone())
        }
    }

    /// Build `base` narrowed by `refinements` — **the** way to construct a
    /// [`Type::Refinement`], establishing both of its invariants.
    ///
    /// Empty `refinements` yields `base` unrefined (a position claiming nothing is
    /// its base type), and a `base` that is already refined has its refinements
    /// merged in rather than stacked on top, so refinement sets never nest.
    /// Flattening is sound because every refinement at a position restricts the same
    /// underlying element: a refinement narrows which values inhabit a type, it
    /// does not change them, so an outer refinement's [`REFINEMENT_BINDER`] ranges
    /// over exactly the values the inner one does.
    pub fn refined(base: Type, refinements: RefinementSet) -> Type {
        if refinements.is_empty() {
            return base;
        }
        match base {
            Type::Refinement(inner, existing) => {
                Type::Refinement(inner, existing.union(&refinements))
            }
            bare => Type::Refinement(Box::new(bare), refinements),
        }
    }

    /// [`Type::refined`] with a single refinement — the common case at a site that
    /// mints one predicate.
    pub fn refined_one(base: Type, refinement: Refinement) -> Type {
        Type::refined(base, RefinementSet::one(refinement))
    }

    /// The refinements carried at this position — empty for an unrefined type, so a
    /// caller can compare or filter what two positions demand without
    /// case-splitting on whether either is refined.
    pub fn refinements(&self) -> &[Refinement] {
        match self {
            Type::Refinement(_, refinements) => refinements.as_slice(),
            _ => &[],
        }
    }
    /// This type with each witness in `renaming`'s domain replaced by the one it maps to —
    /// **binders included**, so a sum whose binder is renamed is α-converted rather than
    /// having its body's occurrences captured by a name it no longer introduces. The
    /// identity when `renaming` is empty.
    pub fn rename_witnesses(&self, renaming: &WitnessRenaming) -> Type {
        if renaming.is_empty() {
            return self.clone();
        }
        match self {
            // **A reference is a name, so a rename is the whole rewrite.** What the binder
            // ranges over lives on the binder; there is no copy here to carry across.
            Type::WitnessRef(w) => Type::WitnessRef(*renaming.get(w).unwrap_or(w)),
            // An function's slot binders rename with their occurrences — a sum whose binder
            // is renamed is α-converted rather than having its domain's occurrences
            // captured by a name it no longer introduces.
            Type::Fun {
                name,
                fun_kind: FunKind::Data(Some(ws)),
                domain,
                codomain,
            } => Type::Fun {
                name: name.clone(),
                fun_kind: FunKind::Data(Some(Rc::new(
                    ws.iter()
                        .map(|w| {
                            Witness::with_id(
                                renaming.get(w.id()).cloned().unwrap_or_else(|| *w.id()),
                                w.type_kind().map_children(|t| t.rename_witnesses(renaming)),
                            )
                        })
                        .collect(),
                ))),
                domain: Box::new(domain.rename_witnesses(renaming)),
                codomain: Box::new(codomain.rename_witnesses(renaming)),
            },
            other => {
                let mut out = other.clone();
                out.walk_children_mut(|t| *t = t.rename_witnesses(renaming));
                out
            }
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
    /// is a different operation: it drops claims rather than looking past them,
    /// allocates, and is only meaningful on a resolved type. It is the wrong tool
    /// for a shape test, and the difference is not cosmetic — it erases
    /// refinements at every depth, a Σ's candidate domains included, and a
    /// candidate's refinement is the program's filter. Reading a domain out of a
    /// deep-stripped copy drops that filter, and with it the `Restrict` it would
    /// have compiled to.
    /// **The fun kind of the function this type may be** — a function's own, or the slot a
    /// variable carries for whatever function it turns out to stand for.
    ///
    /// A variable answers too, which is what carries a fun kind along a variable-to-variable
    /// edge: a collection reaching `?a` and `?a` flowing into `?b` puts that collection below
    /// `?b`'s kind as well, without either edge having to know what the variables are.
    pub fn fun_kind_of(&self) -> Option<FunKind> {
        match self.peel_refinements() {
            Type::Fun { fun_kind, .. } => Some(fun_kind.clone()),
            Type::Infer(v) => Some(FunKind::Var(Rc::clone(&v.fun_kind))),
            _ => None,
        }
    }

    pub fn peel_refinements(&self) -> &Type {
        match self {
            // One layer suffices: `Type::refined` flattens, so a refinement's
            // base is never itself refined.
            Type::Refinement(inner, _) => inner,
            other => other,
        }
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
                history_kind: HistoryKind::Overwrite,
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
                history_kind: HistoryKind::Append,
            } => Some((domain, value)),
            _ => None,
        }
    }

    /// Whether this denotes a **handle** to state introduced elsewhere — a mutable
    /// variable or a feed channel, either [`HistoryKind`].
    ///
    /// This is the question that does not care which [`HistoryKind`] it is, and the thing
    /// that asks it is a *binding*: naming a handle aliases the state behind it either way,
    /// so the choice between binding the handle and binding a copy of its value
    /// turns on handle-ness alone.
    pub fn is_handle(&self) -> bool {
        matches!(self.peel_refinements(), Type::History { .. })
    }

    /// The type of a **list**: a dependent sum `Σ (𝐷: UIntRanges). 𝐷 ⤇ elem` — a
    /// *type*-witness whose kind is every index range ([`TypeKind::UIntRanges`]), so
    /// the length is the witness **domain** rather than a separate scalar value, and
    /// `len` is a property of that domain. An `Array` reaches it as `box(arr)`, whose
    /// one-candidate sum `Σ (𝐷 ∈ {[0, k)}). 𝐷 ⤇ elem` is contained by plain type-kind
    /// containment: `{[0, k)} ⊆ UIntRanges`. The `box` is not optional — without it there
    /// is no edge at all (`src/ccl/design/type-inference.md`, "Only a term builds a sum").
    ///
    /// There is no `{𝑖 | 𝑖 < 𝑛}` domain refinement: the *kind* already
    /// says "a dense prefix range", so nothing needs saying about the elements — and
    /// a filtered range, being a `Refinement` rather than a `UIntRange`, is excluded
    /// by construction rather than by a gate that must remember not to strip
    /// refinements.
    ///
    /// Contrast a conditional collection, whose kind is a *finite* candidate set
    /// ([`TypeKind::Enumerated`]).
    pub fn list_of(elem: Type) -> Self {
        Type::sum_over(TypeKind::UIntRanges, None, elem)
    }

    /// The type of a **map**: the dependent sum `Σ (𝜎 : SubtypesOf(key)). 𝜎 ⤇ value`.
    ///
    /// Its domain is whichever set of keys the map turned out to hold, and the kind bounds
    /// that set by a type rather than naming its members — so a map keyed by a refined `Int`
    /// satisfies a demand for one keyed by `Int`, and not conversely
    /// ([`TypeKind::SubtypesOf`]). Contrast [`list_of`](Self::list_of), whose
    /// [`UIntRanges`](TypeKind::UIntRanges) takes no parameter, and a conditional collection,
    /// whose candidates are named.
    pub fn map_of(key: Type, value: Type) -> Self {
        Type::sum_over(TypeKind::SubtypesOf(Box::new(key)), None, value)
    }

    /// The type of a **set**: [`map_of`](Self::map_of) at a `unit` value, so the key domain
    /// is the payload and the codomain carries nothing.
    pub fn set_of(key: Type) -> Self {
        Type::map_of(key, Type::Base(BaseType::Unit))
    }

    /// The type of a **full map**: the data function `(𝑘: 𝐾) ⤇ 𝑉`, holding a value for
    /// every key of `𝐾` so a lookup needs no proof of presence. Not a sum
    /// (`src/ccl/design/collections.md`, "The six collection types").
    ///
    /// **A Pi, always.** A full map's value may depend on its key — a `groupby`'s group is
    /// `{𝐼 | key(𝑖) == 𝑘} ⤇ 𝑉` — so the type declares the binder that dependence names.
    /// Without one the codomain edge has no name to put the initializer's binder in
    /// correspondence with (`constrain_go`'s `cod_sl`), and the dependent codomain lands as
    /// a bound naming a binder the holder's telescope does not hold
    /// (`src/ccl/design/type-inference.md`, "The invariant"). A codomain that does not
    /// reference the binder is an ordinary function either way, so the Pi costs a
    /// non-dependent full map nothing.
    ///
    /// The binder is **freshly minted**: two annotation sites are two binding sites and the
    /// closure check is a lookup by uid.
    pub fn full_map_of(key: Type, value: Type) -> Self {
        Type::pi_kinded(
            crate::ccl::Name::fresh("__map_k"),
            key,
            value,
            FunKind::Data(None),
        )
    }

    /// The type of a **collection**: the dependent sum `Σ (𝐷: Any). 𝐷 ⤇ elem` — a
    /// *type*-witness of [`TypeKind::Type`] (the universe of types). Its domain is an
    /// unknown, unordered, opaque domain, which is what makes it the ⊤ of the kind
    /// order.
    ///
    /// `Type` is that ⊤ and **nothing more**: it admits every type, which is what makes
    /// the edge to ⊤ fall out of the ordinary rule instead of needing a row per kind.
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
        Type::sum_over(TypeKind::Type, None, elem)
    }

    /// The domain of the function this type denotes, seeing through a sum's binder.
    ///
    /// **A sum is a function.** `Σ (𝑤 : 𝐾). (𝑤 ⤇ 𝑉)` is the same collection as `𝐷 ⤇ 𝑉`,
    /// with a binder saying its domain is whichever candidate the witness took — so the
    /// domain it reports is that witness. Callers that go on to *rebuild* the function are
    /// safe by construction ([`fun_like`](Self::fun_like) re-closes the binder); a caller
    /// that instead *inspects* the answer must ask whether it is witness-bound before
    /// treating it as a domain it can read (`iterate` does, since an undetermined witness
    /// has no static extent).
    ///
    pub fn domain(&self) -> Option<Type> {
        match self {
            Type::Fun { domain, .. } => Some(domain.as_ref().clone()),
            _ => None,
        }
    }

    /// The codomain of the function this type denotes, seeing through a sum's binder.
    ///
    /// Unlike [`domain`](Self::domain) this is always safe to read: a factored sum shares
    /// one element type across its candidates, so the codomain never mentions the witness.
    pub fn codomain(&self) -> Option<Type> {
        match self {
            Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
            _ => None,
        }
    }

    /// Whether the function this type denotes is indexed by a **witness** rather than by a
    /// written domain — the closed and open spellings of one collection, answered together.
    ///
    /// After `lambda_elim` a collection has two spellings, and which one a reader meets is
    /// a fact about position, not about the collection: the `Σ` sits at the position that
    /// binds the witness, and every interior position carries the sum's *body* with the
    /// witness free (a `Compose` chain composes on codomains, and a `Σ` has none — so
    /// exactly one position per chain can hold the binder). Both spell the same collection,
    /// so a reader asking "is this indexed by a witness" must accept either, and a reader
    /// that tests only the slot silently answers `false` at every interior position.
    ///
    /// Refinements are peeled: a consumer's filter rides the witness (`{𝑤 | 𝑝}`), so a
    /// restricted collection is witness-indexed like an unrestricted one.
    pub fn is_witness_indexed(&self) -> bool {
        let head = {
            let mut t = self;
            while let Type::Refinement(inner, _) = t {
                t = inner;
            }
            t
        };
        head.sum().is_some() || has_free_witness_ref(head, &[])
    }

    /// The kind the witness indexing this collection ranges over — **only where the binder
    /// is**.
    ///
    /// `None` says one of two things, and the difference is what a caller has to think
    /// about: either no witness indexes this collection, or the binder is at an enclosing
    /// position and this is its body ([`is_witness_indexed`](Self::is_witness_indexed)
    /// separates the two). A range belongs to a witness, so the body genuinely cannot
    /// answer: nothing in it names one.
    ///
    /// So a caller needing the kind after inference must read it off a position that binds:
    /// a `box`'s own function type states the sum it introduces, and no rewrite retypes it.
    /// Asking the *node* instead is how a determined witness goes unrecognized wherever the
    /// introduction is interior to a chain.
    pub fn witness_kind(&self) -> Option<TypeKind> {
        match self {
            Type::Refinement(inner, _) => inner.witness_kind(),
            Type::Fun { fun_kind, .. } => fun_kind.witnesses().first().map(Witness::type_kind),
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
    #[cfg(any(test, feature = "test-helpers"))]
    pub fn without_witness_binders(&self) -> Type {
        fn go(ty: &Type, scope: &mut Vec<WitnessId>) -> Type {
            use crate::ccl::infer_var::WitnessBinderId;
            match ty {
                // Index from the innermost binder outward, so the name is the *shape* of the
                // reference rather than the identity of what it points at. An occurrence with
                // no binder in scope keeps its own id: it is free, and the free-witness check
                // is what has an opinion about that.
                Type::WitnessRef(w) => match scope.iter().rev().position(|b| b == w) {
                    Some(depth) => Type::WitnessRef(WitnessId(WitnessBinderId(depth as u32))),
                    None => Type::WitnessRef(*w),
                },
                Type::Fun {
                    name,
                    fun_kind: FunKind::Data(Some(ws)),
                    domain,
                    codomain,
                } => {
                    // The slot is a telescope: binder 𝑖's kind is canonicalized under
                    // binders 0‥𝑖−1, the domain and codomain under all of them.
                    let base = scope.len();
                    let mut kinds: Vec<TypeKind> = Vec::new();
                    for w in ws.iter() {
                        kinds.push(w.type_kind().map_children(|t| go(t, scope)));
                        scope.push(*w.id());
                    }
                    let domain = go(domain, scope);
                    let codomain = go(codomain, scope);
                    scope.truncate(base);
                    // De Bruijn *depth* as the binder, which is the whole point of this
                    // canonicalization — so it is a deliberate re-binding rather than a
                    // derivation, and `bound_to` is how it is said.
                    Type::Fun {
                        name: name.clone(),
                        fun_kind: FunKind::Data(Some(Rc::new(
                            kinds
                                .into_iter()
                                .enumerate()
                                .map(|(i, k)| {
                                    Witness::bound_to(WitnessBinderId((base + i) as u32), k)
                                })
                                .collect(),
                        ))),
                        domain: Box::new(domain),
                        codomain: Box::new(codomain),
                    }
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
    /// name-spelled twin stay unequal here, so the comparisons below hold
    /// only between two types on the same side of a construction boundary. That
    /// is the invariant they are checking, not an assumption they make — a pass
    /// that dropped a binder and left the index behind fails them.
    ///
    /// Under the Barendregt convention the blindness needed at the remaining
    /// call sites (lambda elimination's type-preservation asserts) is exactly
    /// `Some` vs `None`: both compared types descend from one derivation, so
    /// when both carry a binder it is the *same* [`crate::ccl::Name`] (uids are preserved
    /// by every copy in the chain). What elimination does not preserve is
    /// the binder's presence — the rebuilt function types ([`Type::compute_fun_or_hole`],
    /// [`Type::fun`]) are constructed with `name: None`. If those sites ever
    /// preserve binders on rebuilt types, this helper can retire.
    pub fn without_pi_names(&self) -> Type {
        match self {
            Type::Fun {
                fun_kind,
                domain,
                codomain,
                ..
            } => Type::Fun {
                name: None,
                // Canonicalize the kind so the comparison is about *shape*. Nothing
                // here says elimination may lose it — `elim_lambda_kinded` carries a
                // lambda's kind across — only that these asserts are checking
                // domain/codomain structure and the Pi binder, not provenance. A sum's
                // binders stay: erasing them would orphan the domain's occurrences, and
                // being a sum is shape, not provenance.
                fun_kind: match fun_kind.witnesses() {
                    [] => FunKind::Compute,
                    ws => FunKind::Data(Some(Rc::new(
                        ws.iter()
                            .map(|w| w.map_types(|t| t.without_pi_names()))
                            .collect(),
                    ))),
                },
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
            Type::Refinement(base, refinements) => {
                Type::refined(base.without_pi_names(), refinements.clone())
            }
            Type::History {
                value,
                domain,
                history_kind,
            } => Type::History {
                value: Box::new(value.without_pi_names()),
                domain: Box::new(domain.without_pi_names()),
                history_kind: *history_kind,
            },
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::SharedHole(_)
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

    /// Does this type hold a position nothing has resolved yet?
    ///
    /// What a *rejecting* caller must ask before it reads a structural answer: two types that
    /// differ today can still be resolved to the same one, so refusing on a difference is
    /// sound only where nothing is left to resolve. [`TypeKind::refuses`] is the caller.
    ///
    /// [`crate::ccl::subst::type_contains_infer`] answers the `Infer` half and is the cheaper
    /// check where that is all a caller wants; this one is the whole of "unresolved", which is
    /// what certainty needs — see the transient-variant table on [`Type`].
    ///
    /// **A refinement counts as unresolved.** Equality compares a predicate, and the
    /// predicate's own type slots are not reachable from [`walk_children`](Self::walk_children)
    /// — reading them needs `crate::ccl::ccl_utils::walk_refined_predicates` and its visited
    /// set. Answering "unresolved" instead abstains, which costs a refusal this has no
    /// measured caller for and never costs correctness.
    pub fn holds_an_unresolved_position(&self) -> bool {
        if matches!(
            self,
            Type::Infer(_)
                | Type::Hole
                | Type::SharedHole(_)
                | Type::BoundedHole(_)
                | Type::Refinement(..)
        ) {
            return true;
        }
        let mut unresolved = false;
        self.walk_children(|child| unresolved |= child.holds_an_unresolved_position());
        unresolved
    }

    /// Invoke `f` on each direct child [`Type`] of this type.
    ///
    /// "Direct child" means a `Type` reachable through this type's value
    /// fields — the domain and codomain of a `Fun` **and the candidate domains of its Σ
    /// binder kinds**, the elements of a `Tuple` / `Record`, the payloads of a `Variant`, and
    /// the base of a `Refinement`.
    ///
    /// Does **not** descend into the refinement *predicate* (which is a
    /// [`TypedExpr`], not a `Type`).  Callers that need to walk a
    /// refinement's predicate must handle [`Type::Refinement`] explicitly
    /// — e.g. by matching on it before calling this helper.
    /// Every [`Refinement`] riding this type or any of its nested type children,
    /// in pre-order: the refinements at each level before that level's children.
    ///
    /// The one place that shape is written. Three callers need it and each wants
    /// something different from a refinement — the predicate's ids, the
    /// predicate's `Rc` identity, the predicate itself as a child edge — so what
    /// they share is the descent and not the projection. Written out per caller
    /// it was the same `if let Type::Refinement(_, rs) = t { for r in rs … }`
    /// followed by the same `t.walk_children(recurse)`, three times, and a type
    /// variant that carries a nested type would have to be remembered in each.
    ///
    /// Does **not** descend into a predicate's own type slots: a predicate is a
    /// [`TypedExpr`], so its slots are an expression walk's business. A caller
    /// that needs them recurses itself, which `collect_tree_ids` and
    /// `predicate_id_collisions` (`crate::ccl::context`) both do.
    pub fn walk_refinements<'a>(&'a self, f: &mut impl FnMut(&'a Refinement)) {
        if let Type::Refinement(_, refinements) = self {
            for r in refinements.iter() {
                f(r);
            }
        }
        self.walk_children(|c| c.walk_refinements(f));
    }

    pub fn walk_children<'a>(&'a self, mut f: impl FnMut(&'a Type)) {
        match self {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::SharedHole(_)
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::WitnessRef(_)
            | Type::Txn => {}
            // A bounded annotation's bound is an ordinary child type — a pass
            // that rewrites types (uniquify's α-renaming, `subst`) must reach
            // inside it exactly as it reaches inside a `Refinement`.
            Type::BoundedHole(t) => f(t),
            Type::Fun {
                fun_kind,
                domain,
                codomain,
                ..
            } => {
                // A sum's binder kinds are the function's children too — their candidate
                // domains are types substitution, freshening and comparison must reach.
                for w in fun_kind.witnesses() {
                    for t in w.types() {
                        f(t);
                    }
                }
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
            | Type::WitnessRef(_)
            | Type::Txn => {}
            // A bounded annotation's bound is an ordinary child type — a pass
            // that rewrites types (uniquify's α-renaming, `subst`) must reach
            // inside it exactly as it reaches inside a `Refinement`.
            Type::BoundedHole(t) => f(t),
            Type::Fun {
                fun_kind,
                domain,
                codomain,
                ..
            } => {
                for w in fun_kind.witnesses_mut() {
                    for t in w.types_mut() {
                        f(t);
                    }
                }
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

/// A predicate over an operator's result, as a function of the operand terms of
/// one use. A trait instance's associated type may carry one, and depositing that
/// type applies it to the operands the obligation recorded
/// ([`TraitInstance`](crate::ccl::infer::solver::traits::TraitInstance)).
pub type RefinementTemplate = fn(&[TypedExpr]) -> TypedExpr;

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

    /// Construct a refinement by applying a template function to a
    /// list of argument expressions.
    pub fn born_from_template(template: RefinementTemplate, args: &[TypedExpr]) -> Self {
        Self::born(Rc::new(template(args)))
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
/// The relation is **α-invariant**: a reference to a binder the predicate
/// itself introduces compares by *position* rather than by name, so two
/// predicates that differ only in an interior binder's identity are the same
/// restriction. Two lowerings of one filter mint that binder independently —
/// `[x for x in xs if x > 1]` written twice gives `λ x#3 → x#3 > 1` and
/// `λ x#6 → x#6 > 1` — and comparing them by name splits a refinement set that
/// should dedup, which a `Data` domain then reports as two domains that do not
/// join. A reference to a binder *outside* the predicate still compares by
/// name, which is what keeps two refinements about different enclosing binders
/// apart (uids make that comparison exact).
///
/// [`hash_refinement_predicate`] threads the same scope and hashes a bound
/// reference by position, so the `Eq`/`Hash` contract survives α-invariance.
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
    eq_refinement_predicate_go(a, b, &mut Vec::new())
}

/// Binders the two sides of an [`eq_refinement_predicate`] comparison have
/// introduced, paired and innermost last. Two references match when they
/// resolve to the same pair, or when neither resolves and they are the same
/// name; a reference bound on one side only never matches. `rposition` is what
/// makes shadowing right: the innermost pair spelling a name is the one it
/// resolves to.
fn paired_refs_match(
    pairs: &[(crate::ccl::Name, crate::ccl::Name)],
    x: &crate::ccl::Name,
    y: &crate::ccl::Name,
) -> bool {
    match (
        pairs.iter().rposition(|(l, _)| l == x),
        pairs.iter().rposition(|(_, r)| r == y),
    ) {
        (Some(i), Some(j)) => i == j,
        (None, None) => x == y,
        _ => false,
    }
}

/// Compare `a` and `b` with `(l, r)` paired over them, restoring `pairs` before
/// returning — the binder scopes over these children and nothing after them.
fn eq_under_binder(
    pairs: &mut Vec<(crate::ccl::Name, crate::ccl::Name)>,
    l: &crate::ccl::Name,
    r: &crate::ccl::Name,
    children: &[(&TypedExpr, &TypedExpr)],
) -> bool {
    pairs.push((l.clone(), r.clone()));
    let matched = children
        .iter()
        .all(|(x, y)| eq_refinement_predicate_go(x, y, pairs));
    pairs.pop();
    matched
}

/// Compare two cast targets' domain-refinement predicates term-wise (see
/// [`eq_refinement_predicate`]). Pointer-equal predicates short-circuit;
/// otherwise the comparison recurses structurally (acyclic terms, so it
/// terminates without a cycle guard).
fn eq_cast_target_predicates(
    t1: &Type,
    t2: &Type,
    pairs: &mut Vec<(crate::ccl::Name, crate::ccl::Name)>,
) -> bool {
    match (
        ccl_utils::cast_target_refinement(t1),
        ccl_utils::cast_target_refinement(t2),
    ) {
        (None, None) => true,
        // Set equality, whose member comparison is `Refinement`'s own, run
        // **under the enclosing pairing**: a nested predicate may reference a
        // binder the outer predicate introduced (a comprehension inside a
        // filter), and that reference resolves by position like any other, so
        // the comparison cannot start a fresh pairing the way
        // `RefinementSet`'s own `PartialEq` does. Deduplicated on both sides
        // ([`RefinementSet::insert`]), so equal cardinality plus one-way
        // containment is mutual containment — the same argument that impl
        // makes. The mutual recursion terminates on tree shape: predicates are
        // acyclic `Rc<TypedExpr>`s, so a cast target cannot contain the term
        // comparing it.
        (Some(s1), Some(s2)) => {
            s1.len() == s2.len()
                && s1.iter().all(|r1| {
                    s2.iter().any(|r2| {
                        Rc::ptr_eq(&r1.predicate, &r2.predicate)
                            || eq_refinement_predicate_go(&r1.predicate, &r2.predicate, pairs)
                    })
                })
        }
        _ => false,
    }
}

/// Whether `ty` contains a **free** [`Type::WitnessRef`] — one that no enclosing function's
/// slot *within this type* binds.
///
/// A bound witness is ordinary and expected: it is how a sum's body names the domain the
/// witness picked. A **free** one is a type that has lost its binder, which is what
/// happens when a pass reaches into a sum for its body and does not put the binder back. Such a
/// type means nothing on its own — `s` denotes "whichever domain", and with no sum there
/// is no "which" to range over — so consumers downstream read it as a concrete leaf and
/// compare it against real domains.
///
/// The scoping mirrors witness substitution exactly: a sum binds the witness in its
/// **body**, while its kind's candidates are written in the enclosing scope, so a
/// reference among them belongs to an *outer* binder and is free unless one exists.
/// `in_scope` are the binders already open around this type — empty for a standalone
/// type, and the enclosing tree's binders for a type slot inside a term (see
/// `debug_assert_no_free_witness`).
pub fn has_free_witness_ref(ty: &Type, in_scope: &[WitnessId]) -> bool {
    !free_witness_refs(ty, in_scope).is_empty()
}

/// Which witnesses `ty` mentions free — the witnesses of
/// [`has_free_witness_ref`], for a caller that must act on *who* rather than
/// on whether.
///
/// A domain that **is** the witness names one; a domain that merely *mentions* it —
/// `(𝑤, 𝐷)`, the index of a summed collection iterated beside a second generator — names
/// it just as much, and reading only the whole misses it. Every free occurrence is
/// reported, in first-encounter order, without duplicates.
pub fn free_witness_refs(ty: &Type, in_scope: &[WitnessId]) -> Vec<WitnessId> {
    fn go(ty: &Type, scope: &mut Vec<WitnessId>, found: &mut Vec<WitnessId>) {
        match ty {
            // Free iff it names no binder in scope. Testing the **name** rather than
            // "is there a sum somewhere above" is what makes this catch the real error:
            // an occurrence sitting under an *unrelated* sum is still free.
            Type::WitnessRef(w) => {
                // **Bound iff it names a binder in scope.** A reference is a name, so this
                // is name membership and nothing else.
                if !scope.contains(w) && !found.contains(w) {
                    found.push(*w);
                }
            }
            Type::Fun {
                fun_kind: FunKind::Data(Some(ws)),
                domain,
                codomain,
                ..
            } if !ws.is_empty() => {
                // The slot is a **telescope**: binder 𝑖's kind is written under binders
                // 0‥𝑖−1 (a nested source's candidates may name the outer witness), and
                // the domain and codomain are under all of them.
                let base = scope.len();
                for w in ws.iter() {
                    for t in w.types() {
                        go(t, scope, found);
                    }
                    scope.push(*w.id());
                }
                go(domain, scope, found);
                go(codomain, scope, found);
                scope.truncate(base);
            }
            other => other.walk_children(|c| go(c, scope, found)),
        }
    }
    let mut found = Vec::new();
    go(ty, &mut in_scope.to_vec(), &mut found);
    found
}

/// Replace every occurrence of `binder` in `ty` by `candidate` — the same substitution
/// [`Type::instantiate_sum`] performs, for a type reached from outside a sum's body.
///
/// Two shapes arrive here, and realization ([`crate::ccl::planning`]) walks a leg's type
/// slots without knowing which it holds. A witness **escapes** its sum once a term is
/// decomposed: a filter's predicate is indexed by the element, so its types name the
/// witness while no `Σ` is in sight, and instantiating means substituting at the
/// occurrences with no binder to strip. A slot may equally still hold the **whole sum**,
/// which this opens at `candidate` rather than walking through
/// ([`WitnessMapping::Discharge`](crate::ccl::subst::WitnessMapping::Discharge)).
pub fn instantiate_witness(ty: &Type, binder: &WitnessId, candidate: &Type) -> Type {
    crate::ccl::subst::Subst::discharge_witness(binder, candidate).apply_type(ty)
}

/// Whether `ty` mentions `binder` anywhere. Binder ids are globally unique, so any
/// occurrence is this binder's and no scope tracking is needed to recognise one.
pub(crate) fn mentions_witness(ty: &Type, binder: &WitnessId) -> bool {
    fn go(ty: &Type, binder: &WitnessId) -> bool {
        if matches!(ty, Type::WitnessRef(w) if w == binder) {
            return true;
        }
        let mut found = false;
        ty.walk_children(|c| found |= go(c, binder));
        found
    }
    go(ty, binder)
}

/// A renaming of witness references, applied by [`Type::rename_witnesses`].
pub type WitnessRenaming = std::collections::BTreeMap<WitnessId, WitnessId>;

/// Recursive worker for [`eq_refinement_predicate`].
fn eq_refinement_predicate_go(
    a: &TypedExpr,
    b: &TypedExpr,
    pairs: &mut Vec<(crate::ccl::Name, crate::ccl::Name)>,
) -> bool {
    use TypedExprNode as N;
    fn all_eq(
        xs: &[TypedExpr],
        ys: &[TypedExpr],
        pairs: &mut Vec<(crate::ccl::Name, crate::ccl::Name)>,
    ) -> bool {
        xs.len() == ys.len()
            && xs
                .iter()
                .zip(ys)
                .all(|(x, y)| eq_refinement_predicate_go(x, y, pairs))
    }
    match (&a.node, &b.node) {
        (N::Lit(x), N::Lit(y)) => x == y,
        (N::Var(x), N::Var(y)) => paired_refs_match(pairs, x, y),
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
        ) => eq_refinement_predicate_go(f1, f2, pairs) && eq_refinement_predicate_go(a1, a2, pairs),
        (
            N::Cast {
                value: v1,
                target: t1,
            },
            N::Cast {
                value: v2,
                target: t2,
            },
        ) => eq_refinement_predicate_go(v1, v2, pairs) && eq_cast_target_predicates(t1, t2, pairs),
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
        ) => {
            o1 == o2
                && eq_refinement_predicate_go(l1, l2, pairs)
                && eq_refinement_predicate_go(r1, r2, pairs)
        }
        (N::UnaryOp(k1, e1), N::UnaryOp(k2, e2)) => {
            k1 == k2 && eq_refinement_predicate_go(e1, e2, pairs)
        }
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
            // A lambda's parameter is a binder the predicate introduces: pair
            // the two and compare the bodies under the pairing, so the bodies'
            // references to it match by position.
        ) => eq_under_binder(pairs, &p1.name, &p2.name, &[(b1, b2)]),
        (
            N::Aggregate {
                input: i1,
                kind: k1,
            },
            N::Aggregate {
                input: i2,
                kind: k2,
            },
        ) => k1 == k2 && eq_refinement_predicate_go(i1, i2, pairs),
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
            // The definiens sits outside the binder, the body inside it.
            eq_refinement_predicate_go(e1, e2, pairs)
                && eq_under_binder(pairs, &bd1.name, &bd2.name, &[(b1, b2)])
        }
        (N::List(x), N::List(y))
        | (N::Tuple(x), N::Tuple(y))
        | (N::Compose(x), N::Compose(y))
        | (N::Copair(x), N::Copair(y))
        | (N::DisjointJoin(x), N::DisjointJoin(y)) => all_eq(x, y, pairs),
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
                (Some(x), Some(y)) => eq_refinement_predicate_go(x, y, pairs),
                _ => false,
            };
            scrutinee_eq
                && br1.len() == br2.len()
                && br1
                    .iter()
                    .zip(br2)
                    .all(|(x, y)| match (&x.pattern, &y.pattern) {
                        // A payload binder scopes over the guard and the body
                        // both, so both compare under the pairing.
                        (Some(p), Some(q)) => {
                            p.tag == q.tag
                                && eq_under_binder(
                                    pairs,
                                    &p.binding.name,
                                    &q.binding.name,
                                    &[(&x.guard, &y.guard), (&x.body, &y.body)],
                                )
                        }
                        (None, None) => {
                            eq_refinement_predicate_go(&x.guard, &y.guard, pairs)
                                && eq_refinement_predicate_go(&x.body, &y.body, pairs)
                        }
                        _ => false,
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
        ) => t1 == t2 && eq_refinement_predicate_go(p1, p2, pairs),
        (N::Record(f1), N::Record(f2)) => {
            f1.len() == f2.len()
                && f1.iter().zip(f2).all(|((n1, e1), (n2, e2))| {
                    n1 == n2 && eq_refinement_predicate_go(e1, e2, pairs)
                })
        }
        (N::ExprStmt { expr: e1, body: b1 }, N::ExprStmt { expr: e2, body: b2 }) => {
            eq_refinement_predicate_go(e1, e2, pairs) && eq_refinement_predicate_go(b1, b2, pairs)
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
            // A `Feed`/`Define` name is a *use* of the binder that introduced
            // the handle (`ccl::scope`), so it resolves like any reference.
        ) => paired_refs_match(pairs, n1, n2) && eq_refinement_predicate_go(v1, v2, pairs),
        // A realized conditional collection. Reachable inside a predicate because a
        // filter's predicate carries its own copy of the source (`__elem ▷ src ▷ 𝑓`), so
        // when `src` is a conditional, realization rewrites it *in the predicate*.
        (N::Realize(v1), N::Realize(v2)) => eq_refinement_predicate_go(v1, v2, pairs),
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
///
/// A reference to a binder the predicate itself introduces hashes as that
/// binder's **position**, not its name, which is what makes the hash
/// α-invariant alongside `eq`. `scope` carries the binders in scope, innermost
/// last, exactly as [`eq_refinement_predicate`] carries its pairing; a binder's
/// own name is never hashed, so hash stays coarser than `eq` and the
/// `Eq`/`Hash` contract holds.
fn hash_refinement_predicate<H: std::hash::Hasher>(
    e: &TypedExpr,
    state: &mut H,
    scope: &mut Vec<crate::ccl::Name>,
) {
    use std::hash::Hash;
    std::mem::discriminant(&e.node).hash(state);
    match &e.node {
        TypedExprNode::Lit(Lit::Int(n)) => n.hash(state),
        TypedExprNode::Lit(Lit::String(s)) => s.hash(state),
        TypedExprNode::Lit(Lit::Bool(b)) => b.hash(state),
        TypedExprNode::Lit(Lit::Unit) => {}
        // A bound reference hashes by position (innermost match, so shadowing
        // resolves as it does in `eq`); a free one by name.
        TypedExprNode::Var(name) => match scope.iter().rposition(|b| b == name) {
            Some(level) => level.hash(state),
            None => name.hash(state),
        },
        TypedExprNode::Builtin(b) => b.hash(state),
        TypedExprNode::BinOp { op, .. } => op.hash(state),
        TypedExprNode::UnaryOp(kind, _) => kind.hash(state),
        TypedExprNode::Aggregate { kind, .. } => kind.hash(state),
        TypedExprNode::VariantCtor { tag, .. } => tag.hash(state),
        TypedExprNode::Proj(ProjKey::Index(i)) => i.hash(state),
        TypedExprNode::Proj(ProjKey::Field(f)) => f.hash(state),
        _ => {}
    }
    // The binding arms `eq` handles, threading the same scope over the same
    // children. Every other node's children sit in the node's own scope, so the
    // generic walk covers them.
    match &e.node {
        TypedExprNode::Lambda { param, body } => {
            hash_under_binder(state, scope, &param.name, &[body]);
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            hash_refinement_predicate(bound_expr, state, scope);
            hash_under_binder(state, scope, &binding.name, &[body]);
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                hash_refinement_predicate(s, state, scope);
            }
            for b in branches {
                match &b.pattern {
                    Some(p) => {
                        hash_under_binder(state, scope, &p.binding.name, &[&b.guard, &b.body]);
                    }
                    None => {
                        hash_refinement_predicate(&b.guard, state, scope);
                        hash_refinement_predicate(&b.body, state, scope);
                    }
                }
            }
        }
        _ => e.walk_children(|child| hash_refinement_predicate(child, state, scope)),
    }
}

/// Hash `children` with `binder` in scope, restoring `scope` afterwards — the
/// hashing counterpart of [`eq_under_binder`]. The binder's own name is not
/// hashed: `eq` compares it by position too, so hashing it would make the hash
/// finer than `eq` for no gain.
fn hash_under_binder<H: std::hash::Hasher>(
    state: &mut H,
    scope: &mut Vec<crate::ccl::Name>,
    binder: &crate::ccl::Name,
    children: &[&TypedExpr],
) {
    scope.push(binder.clone());
    for c in children {
        hash_refinement_predicate(c, state, scope);
    }
    scope.pop();
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
        hash_refinement_predicate(&self.predicate, state, &mut Vec::new());
    }
}

/// The refinements carried at one refined position: an **unordered set** of
/// [`Refinement`]s, deduplicated by their structural [`PartialEq`].
///
/// A refined type narrows its base by the *conjunction* of these refinements, and
/// conjunction is commutative, idempotent, and associative — so a set is the
/// honest carrier and a chain of nested `{{𝑇 | 𝑝} | 𝑞}` layers was not. That
/// chain gave one representation three incompatible readings: a *set* to
/// subtyping (the deficit machinery compares layers as a set), a *stack* to
/// planning (whichever layer sat outermost drove which restrict it built), and
/// an *identity* to `SpecKey` and the recorded-vs-recomputed walls (`Type`'s
/// derived equality is position-sensitive). Layers accumulated in constraint
/// *arrival* order, so the stack reading made typing depend on the order two
/// bounds happened to meet at a variable. Set semantics deletes the degree of
/// freedom rather than pinning it to a canonical order: there is no position to
/// read, so planning is free to apply predicates in whatever order it likes
/// (cheapest filter first, say) without changing an identity.
///
/// The invariant, maintained by [`insert`](Self::insert) and relied on by
/// [`PartialEq`]: **no two members are equal**. Given that, mutual containment
/// reduces to equal length plus one-way containment.
#[derive(Debug, Clone, Default)]
pub struct RefinementSet(Vec<Refinement>);

/// Whether to build refinement sets in reversed physical order — the
/// order-independence **stress knob**, driven by `CAMBRA_REFINEMENT_ORDER=reverse`.
///
/// Set semantics makes the backing `Vec`'s order meaningless by contract, and flipping it
/// globally is what exercises that: a consumer letting the order reach something
/// observable, or a dedup keeping the first-inserted of two `eq`-equal members whose
/// (type-blind-equal) predicate terms carry different embedded type slots.
///
/// It reaches planning too, which is the harder half. Planning fixes an order to build its
/// `restrict` chain, and where a predicate reads a value another refinement narrowed that
/// order is the program's, not planning's — so the chain has to recover it from the
/// predicates rather than from the storage this knob reverses
/// ([`application_order`]). The compiled term is expected to be identical either way.
///
/// Reading it once into a `LazyLock` keeps the check to a cached bool, and it is
/// `debug_assertions`-only so a release compiler cannot be perturbed by the
/// environment.
#[cfg(debug_assertions)]
fn stress_reversed() -> bool {
    static REVERSED: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("CAMBRA_REFINEMENT_ORDER").as_deref() == Ok("reverse")
    });
    *REVERSED
}

#[cfg(not(debug_assertions))]
fn stress_reversed() -> bool {
    false
}

impl RefinementSet {
    /// The empty set — an unrefined position.
    pub fn new() -> Self {
        RefinementSet(Vec::new())
    }

    /// The singleton set carrying one refinement.
    pub fn one(r: Refinement) -> Self {
        RefinementSet(vec![r])
    }

    /// Add a refinement, keeping the set deduplicated. Returns whether it was new.
    ///
    /// A refinement already present is dropped rather than replacing the incumbent:
    /// the two are equal as *restrictions* ([`eq_refinement_predicate`]), and
    /// keeping the incumbent preserves whatever predicate `Rc` sharing the
    /// position already had.
    pub fn insert(&mut self, r: Refinement) -> bool {
        if self.0.contains(&r) {
            return false;
        }
        if stress_reversed() {
            self.0.insert(0, r);
        } else {
            self.0.push(r);
        }
        true
    }

    /// Add every refinement of `other`.
    pub fn extend(&mut self, other: impl IntoIterator<Item = Refinement>) {
        for r in other {
            self.insert(r);
        }
    }

    /// The union of two sets — the position carries every refinement either side
    /// imposes.
    /// This is the *meet* of the refined types (a narrower value satisfies
    /// more), so it is what a negative-polarity merge performs.
    pub fn union(mut self, other: &RefinementSet) -> Self {
        self.extend(other.iter().cloned());
        self
    }

    /// The intersection — only the refinements *both* sides guarantee, which is
    /// what a value known to be one of two things reliably carries (the
    /// positive-polarity merge, and the *join* of the refined types).
    pub fn intersect(&self, other: &RefinementSet) -> Self {
        RefinementSet(
            self.0
                .iter()
                .filter(|r| other.contains(r))
                .cloned()
                .collect(),
        )
    }

    pub fn contains(&self, r: &Refinement) -> bool {
        self.0.contains(r)
    }

    pub fn as_slice(&self) -> &[Refinement] {
        &self.0
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Refinement> {
        self.0.iter()
    }

    /// Rewrite every refinement's predicate in place, then re-establish the dedup
    /// invariant.
    ///
    /// The passes that rewrite predicates — substitution forcing, predicate
    /// compilation, binder conversion, node typing — cannot change *which*
    /// positions are refined, but they can make two distinct refinements **equal**:
    /// a substitution mapping two binders onto one term, or a compilation
    /// normalizing two spellings of one predicate. The set would then hold a
    /// duplicate, and [`PartialEq`] reads cardinality, so two sets equal as sets
    /// would compare unequal — and a set is an identity at the trivial-equality
    /// short-circuit, at cache keys, and at the recorded-vs-recomputed walls.
    /// Re-deduplicating after the walk is what makes the invariant hold by
    /// construction instead of being re-argued at each of the eight rewrite sites.
    ///
    /// No program in the suite reaches a collapsing rewrite, in either physical
    /// order; the dedup is what would notice one starting to, and
    /// `a_rewrite_that_collapses_two_refinements_leaves_a_set` reaches it directly.
    ///
    /// The closure sees each refinement's **physical** index, for a caller pairing
    /// per-position context onto the walk ([`application_elem_types`]).
    pub fn rewrite_each(&mut self, mut f: impl FnMut(usize, &mut Refinement)) {
        let outcome = self.try_rewrite_each(|i, r| {
            f(i, r);
            Ok::<(), std::convert::Infallible>(())
        });
        debug_assert!(outcome.is_ok(), "an infallible rewrite cannot fail");
    }

    /// [`rewrite_each`](Self::rewrite_each) for a rewrite that can fail. The
    /// dedup runs whether or not the walk completed, so a set is never left
    /// holding a duplicate on the error path.
    pub fn try_rewrite_each<E>(
        &mut self,
        mut f: impl FnMut(usize, &mut Refinement) -> Result<(), E>,
    ) -> Result<(), E> {
        let mut outcome = Ok(());
        for (i, r) in self.0.iter_mut().enumerate() {
            if let Err(e) = f(i, r) {
                outcome = Err(e);
                break;
            }
        }
        if self.0.len() > 1 {
            let mut kept = Vec::with_capacity(self.0.len());
            for r in self.0.drain(..) {
                if !kept.contains(&r) {
                    kept.push(r);
                }
            }
            self.0 = kept;
        }
        outcome
    }

    /// The sole refinement, or `None` if the set does not hold exactly one.
    ///
    /// For the positions built with exactly one predicate by construction — a
    /// `cast` target's domain refinement, a literal singleton's pin — where
    /// "the" refinement is a real notion rather than a position in a chain.
    pub fn sole(&self) -> Option<&Refinement> {
        match self.0.as_slice() {
            [r] => Some(r),
            _ => None,
        }
    }
}

/// Walk `refinements` in **application order**: each refinement paired with the type its
/// element has at the point that refinement applies — `base` narrowed by every refinement
/// applied before it.
///
/// A refinement set is unordered as a *fact* about a value, but materializing it is a
/// pipeline — planning emits one `restrict` per refinement — and a pipeline is
/// sequential: stage 𝑘 reads elements already narrowed by stages 1..𝑘-1, so its
/// element type is not the bare base. Planning therefore *chooses* an order here.
/// Which order is free (any of them yields a well-typed pipeline for the same
/// final domain, and a cost model could pick the cheapest filter first); what is
/// not free is choosing *differently* in two places, since the types along the
/// pipeline and the predicates compiled for it must agree.
///
/// **The order is the set's own.** Going through one function is not enough on its own —
/// a *derived* order is only as stable as what it derives from, and the three sites that
/// need one (the `restrict` chain, the predicates compiled for it, and the check that
/// re-derives both) run at different points of the pipeline. Ordering by the refinements'
/// rendered predicates was therefore unstable in the one way that matters: compiling a
/// predicate rewrites its term, so a key read before compilation and one read after can
/// order two refinements differently, and predicates compiled under one order end up in a
/// pipeline typed by the other. Reading the order off the set removes the derivation, and
/// with it the chance of two answers.
///
/// Nothing in the type system may read that order back: [`RefinementSet`]'s equality is
/// order-insensitive, so what planning fixes here never reaches an identity. That split —
/// order-blind types, an order fixed once at planning — is what lets a cost model pick a
/// different one later without touching anything above.
pub fn application_order<'a>(
    refinements: &'a [Refinement],
    base: &'a Type,
) -> impl Iterator<Item = (&'a Refinement, Type)> + 'a {
    let mut narrowed = RefinementSet::new();
    dependency_order(refinements).into_iter().map(move |r| {
        let elem_ty = Type::refined(base.clone(), narrowed.clone());
        narrowed.insert(r.clone());
        (r, elem_ty)
    })
}

/// `refinements`, with each one placed after any it reads a value already narrowed by.
///
/// Most pairs are independent and are ordered by their rendered predicates, so the answer
/// is a function of the set's members and not of how they accumulated. Some are not: the
/// outer filter of `[y for y in [x for x in xs if p] if q]` reads the `p`-filtered
/// collection, so `q`'s predicate carries `{𝐷 | p}` in its own types and `q` cannot be
/// applied to elements `p` has not yet removed. That is the program's nesting rather than
/// anything planning chose, and it survives the flattening of `{{𝐷 | p} | q}` into one set
/// only inside `q`'s predicate — so it is read back from there.
///
/// TODO(widen-at-the-copy): recovery, for a dependency that need not exist. A predicate is
/// only ever asked about elements the whole set admits, and those satisfy `p` whatever order
/// the restricts ran in, so `q` reading its source at `𝐷` would answer identically and
/// nothing would order the pair at all. What makes `q` carry `{𝐷 | p}` is that its *copy of
/// the source* inherits the source's own refined type when the copy is made. Building that
/// copy at the base instead would delete this function.
///
/// Widening the predicate afterwards does not: measured at three sites (`Type::refined`, and
/// a memoized planning pass keyed on the siblings and on the base), all of which
/// desynchronize `q`'s copy from the term it mirrors, whose type still carries `p` — and the
/// producer/consumer refinement match is structural, so the two then disagree about the
/// domain.
///
/// Nor does building the copy at the base, which is the obvious reading of the paragraph
/// above and is wrong. Measured by copying the value under the source's domain-refining
/// cast — unrefined where it is built — and `q` carries `{𝐷 | p}` regardless, because the
/// copy does not *inherit* that type but **acquires** it from its use: the predicate applies
/// the copy at `__elem`, `__elem` ranges over the domain being refined, and for the outer
/// comprehension that domain is the source's own `{𝐷 | p}`. A data function's domain is
/// invariant, so the application fixes the copy's domain to it, whichever sub-term was
/// copied. Closing this needs the predicate to read a *different* collection — the
/// unfiltered source — rather than the same one at a wider type, and for a nested
/// comprehension that form is inside the inner one's lowering rather than at this site.
fn dependency_order(refinements: &[Refinement]) -> Vec<&Refinement> {
    fn reads_narrowed_by(ty: &Type, earlier: &Refinement) -> bool {
        if let Type::Refinement(_, set) = ty
            && set.contains(earlier)
        {
            return true;
        }
        let mut found = false;
        ty.walk_children(|child| found |= reads_narrowed_by(child, earlier));
        found
    }
    fn predicate_reads(pred: &TypedExpr, earlier: &Refinement) -> bool {
        let mut found = false;
        pred.walk_type_slots(|ty| found |= reads_narrowed_by(ty, earlier));
        pred.walk_children(|child| found |= predicate_reads(child, earlier));
        found
    }
    let mut remaining: Vec<&Refinement> = refinements.iter().collect();
    // **Ties break on content, never on where the set happens to hold them.** A set's
    // physical order carries no meaning, so letting it decide between two *independent*
    // predicates makes the compiled term a function of how the refinements accumulated —
    // which is exactly what `CAMBRA_REFINEMENT_ORDER=reverse` exists to catch. Sorting
    // first makes the selection below pick the content-smallest ready member, so the
    // dependency constraint decides where it applies and the rendering decides the rest.
    //
    // `sort_by_cached_key`, not `sort_by_key`: rendering a predicate walks its whole term
    // tree and allocates, and `sort_by_key` recomputes the key at every comparison.
    remaining.sort_by_cached_key(|r| symbolic::symbolic(&r.predicate));
    let mut ordered = Vec::with_capacity(remaining.len());
    while !remaining.is_empty() {
        // The first whose dependencies are all placed. A cycle is unrepresentable — a
        // predicate cannot read a narrowing it is itself part of — so the fallback is
        // unreachable and taking the head keeps this total rather than partial.
        let next = remaining
            .iter()
            .position(|r| {
                !remaining
                    .iter()
                    .any(|o| !std::ptr::eq(*o, *r) && predicate_reads(&r.predicate, o))
            })
            .unwrap_or(0);
        ordered.push(remaining.remove(next));
    }
    ordered
}

/// [`application_order`]'s element types, indexed by each refinement's position in
/// `refinements` — for a site that rewrites the set in place and so walks it in its own
/// order.
///
/// Application order is a **permutation** of that one whenever a predicate reads a value
/// another refinement narrowed ([`application_order`]), so zipping the ordered types onto a
/// positional walk pairs refinements with the wrong element type — silently, since the two
/// sequences have equal length. This does the permutation.
pub fn application_elem_types(refinements: &[Refinement], base: &Type) -> Vec<Type> {
    let mut out = vec![base.clone(); refinements.len()];
    for (r, elem_ty) in application_order(refinements, base) {
        // `application_order` borrows the very slice it was handed, so pointer identity
        // locates the refinement exactly — `PartialEq` would not, being type-blind and
        // therefore able to match a sibling.
        let idx = refinements
            .iter()
            .position(|c| std::ptr::eq(c, r))
            .expect("application_order yields borrows into `refinements`");
        out[idx] = elem_ty;
    }
    out
}

impl PartialEq for RefinementSet {
    /// Set equality. Sound as stated because both sides are deduplicated
    /// ([`insert`](RefinementSet::insert)), so equal cardinality plus one-way
    /// containment is mutual containment.
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len() && self.0.iter().all(|r| other.0.contains(r))
    }
}

impl Eq for RefinementSet {}

impl std::hash::Hash for RefinementSet {
    /// Order-insensitive, as [`PartialEq`] demands: each member's hash is
    /// folded in with a commutative operation. `wrapping_add` rather than
    /// `XOR` because XOR lets two hash-colliding members cancel to the empty
    /// set's hash; the length is mixed in for the same reason.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut combined: u64 = 0;
        for r in &self.0 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(r, &mut h);
            combined = combined.wrapping_add(std::hash::Hasher::finish(&h));
        }
        std::hash::Hash::hash(&self.0.len(), state);
        std::hash::Hash::hash(&combined, state);
    }
}

impl FromIterator<Refinement> for RefinementSet {
    fn from_iter<I: IntoIterator<Item = Refinement>>(iter: I) -> Self {
        let mut out = RefinementSet::new();
        out.extend(iter);
        out
    }
}

impl IntoIterator for RefinementSet {
    type Item = Refinement;
    type IntoIter = std::vec::IntoIter<Refinement>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a RefinementSet {
    type Item = &'a Refinement;
    type IntoIter = std::slice::Iter<'a, Refinement>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl From<Refinement> for RefinementSet {
    fn from(r: Refinement) -> Self {
        RefinementSet::one(r)
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
                    TypedExpr::new(TypedExprNode::Var(Name::elem()))
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
    /// knew. A sum knows one thing more than a plain function — that its domain is whichever
    /// candidate the witness took — and losing that is worse than losing the kind: the
    /// rebuilt domain is usually the witness itself, and a `WitnessRef` with no binder
    /// denotes nothing, so every later comparison reads it as a concrete leaf.
    #[test]
    fn fun_like_rebuilds_under_a_sum_exemplar() {
        let int = Type::Base(BaseType::Int);
        let exemplar = Type::sum_over(
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            None,
            int.clone(),
        );
        let ex = exemplar.sum().expect("built as a sum")[0].clone();
        let rebuilt = Type::fun_like(
            &exemplar,
            Type::WitnessRef(*ex.id()),
            Type::Base(BaseType::Bool),
        );
        let Some([w]) = rebuilt.sum() else {
            panic!("a sum exemplar must rebuild into a sum, got {rebuilt}");
        };
        // What a witness ranges over is **answered**, not written: its range is an index
        // variable and the candidates are recorded below it ([`Type::sum_over`]).
        assert_eq!(
            w.type_kind(),
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            "the witness's type kind carries over"
        );
        assert!(
            matches!(
                &rebuilt,
                Type::Fun {
                    fun_kind: FunKind::Data(..),
                    ..
                }
            ),
            "the body stays a data function, got {rebuilt}"
        );
        assert!(
            !has_free_witness_ref(&rebuilt, &[]),
            "the rebuilt domain's witness is bound by the rebuilt sum, got {rebuilt}"
        );
    }

    use crate::ccl::{BinOpKind, CompareKind, Name};
    use rstest::rstest;

    /// `Refinement`'s hash of `pred`, for asserting the `Eq`/`Hash` contract.
    fn refinement_hash(pred: &TypedExpr) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        Refinement::born(Rc::new(pred.clone())).hash(&mut h);
        h.finish()
    }

    /// Two predicates equal under [`eq_refinement_predicate`] must hash alike,
    /// or a refinement is two different `HashMap` keys.
    fn assert_same_restriction(a: &TypedExpr, b: &TypedExpr) {
        assert!(
            eq_refinement_predicate(a, b),
            "expected the same restriction:\n  {}\n  {}",
            symbolic::symbolic(a),
            symbolic::symbolic(b),
        );
        assert_eq!(
            refinement_hash(a),
            refinement_hash(b),
            "equal refinements must hash alike (Eq/Hash contract)",
        );
    }

    /// A reference to a binder the predicate introduces compares by position,
    /// so two lowerings of one filter are the same restriction. Each binding
    /// form `eq_refinement_predicate` handles gets its own case: a form whose
    /// binder is compared by name instead would split the refinement set and a
    /// `Data` domain would then report two domains that do not join.
    #[rstest]
    // `λ p → p > 1`, the shape a filter lowers to.
    #[case::lambda(0)]
    // `let p = 1 in p > 1`.
    #[case::let_binding(1)]
    // `match _ { `some(p) → p > 1 }` — the payload binder scopes over guard and
    // body both.
    #[case::case_pattern(2)]
    fn alpha_variant_predicates_are_one_restriction(#[case] form: usize) {
        let build = |binder: &str| {
            let b = Name::raw(binder);
            let cmp = TypedExpr::binop(
                TypedExpr::var(b.clone()),
                BinOpKind::Compare(CompareKind::Greater),
                TypedExpr::lit(Lit::Int(1)),
            );
            match form {
                0 => TypedExpr::lambda(b, Type::Base(BaseType::Int), cmp),
                1 => TypedExpr::let_bind(b, TypedExpr::lit(Lit::Int(1)), cmp),
                _ => TypedExpr::match_expr(
                    TypedExpr::lit(Lit::Unit),
                    vec![crate::ccl::Branch {
                        pattern: Some(crate::ccl::Pattern {
                            tag: "some".into(),
                            binding: crate::ccl::TypedBinding::new_annotated(
                                b,
                                Type::Base(BaseType::Int),
                            ),
                            empty_payload: false,
                        }),
                        guard: TypedExpr::lit(Lit::Bool(true)),
                        body: cmp,
                    }],
                ),
            }
        };
        assert_same_restriction(&build("p"), &build("q"));
    }

    /// Shadowing resolves innermost-first on both sides: the inner binder is
    /// what an inner reference denotes, whatever either side spells it.
    #[test]
    fn alpha_invariance_resolves_shadowing_innermost_first() {
        let nested = |outer: &str, inner: &str, referenced: &str| {
            let int = || Type::Base(BaseType::Int);
            TypedExpr::lambda(
                Name::raw(outer),
                int(),
                TypedExpr::lambda(
                    Name::raw(inner),
                    int(),
                    TypedExpr::var(Name::raw(referenced)),
                ),
            )
        };
        // Both reference the inner binder, however each side spells the pair.
        assert_same_restriction(&nested("a", "b", "b"), &nested("x", "y", "y"));
        // A predicate whose inner binder shadows the outer: the reference is the
        // inner one on both sides.
        assert_same_restriction(&nested("a", "a", "a"), &nested("x", "x", "x"));
        // Referencing the *outer* binder is a different restriction from
        // referencing the inner one.
        assert!(!eq_refinement_predicate(
            &nested("a", "b", "a"),
            &nested("x", "y", "y")
        ));
    }

    /// A reference to a binder *outside* the predicate still compares by name.
    /// That is what keeps two refinements about different enclosing binders apart,
    /// and uids make the comparison exact.
    #[test]
    fn a_free_reference_still_compares_by_name() {
        let refinement = |free: &str| {
            TypedExpr::lambda(
                Name::raw("p"),
                Type::Base(BaseType::Int),
                TypedExpr::binop(
                    TypedExpr::var(Name::raw("p")),
                    BinOpKind::Compare(CompareKind::Equals),
                    TypedExpr::var(Name::raw(free)),
                ),
            )
        };
        assert_same_restriction(&refinement("k"), &refinement("k"));
        assert!(
            !eq_refinement_predicate(&refinement("k"), &refinement("m")),
            "distinct enclosing binders must stay distinct"
        );
    }

    /// A reference the binder captures is not a free reference that happens to
    /// share its spelling. `λ p → p > 1` and `λ q → p > 1` pair `p` with `q`, so
    /// the left `p` resolves to the binder while the right `p` resolves outside
    /// it — [`paired_refs_match`]'s mixed arm, and the one that makes the
    /// relation *sound* rather than merely coarse: equating these would let a
    /// refinement mentioning an enclosing binder be deduped against one that
    /// binds the name itself, capturing the free reference.
    ///
    /// Hash is unconstrained here. The `Eq`/`Hash` contract runs one way — equal
    /// refinements hash alike — so a hash coarser than this distinction is
    /// sound, which is why only equality is asserted.
    #[test]
    fn a_captured_reference_is_not_a_free_one_of_the_same_spelling() {
        let gt_one = |referenced: &str| {
            TypedExpr::binop(
                TypedExpr::var(Name::raw(referenced)),
                BinOpKind::Compare(CompareKind::Greater),
                TypedExpr::lit(Lit::Int(1)),
            )
        };
        let binds_it = TypedExpr::lambda(Name::raw("p"), Type::Base(BaseType::Int), gt_one("p"));
        let leaves_it_free =
            TypedExpr::lambda(Name::raw("q"), Type::Base(BaseType::Int), gt_one("p"));
        assert!(
            !eq_refinement_predicate(&binds_it, &leaves_it_free),
            "a bound reference and a free one of the same spelling are two restrictions"
        );
        assert!(
            !eq_refinement_predicate(&leaves_it_free, &binds_it),
            "and the relation is symmetric, so the mirrored arm rejects too"
        );
    }

    /// Independent refinements apply in an order derived from their **content**, and each
    /// one's element type is the base narrowed by the ones before it.
    ///
    /// A set's physical order carries no meaning, so letting it decide makes the compiled
    /// term a function of how the refinements happened to accumulate — the dependence
    /// `CAMBRA_REFINEMENT_ORDER=reverse` exists to catch, and the one a content-addressed
    /// program cannot tolerate. Pinned by building one set in each storage order and
    /// checking both walks agree; following the storage would give two answers, which is
    /// the failure this guards.
    ///
    /// Content decides only where the dependency rule does not: see
    /// [`a_predicate_reading_a_narrowed_value_applies_after_that_narrowing`], which pins the
    /// half that outranks it.
    #[test]
    fn independent_refinements_order_by_content_not_by_storage() {
        let refinement = |name: &str| {
            Refinement::born(Rc::new(TypedExpr::binop(
                TypedExpr::var(name),
                BinOpKind::Compare(CompareKind::Equals),
                TypedExpr::lit(Lit::Int(1)),
            )))
        };
        let (a, b) = (refinement("a"), refinement("b"));
        let base = Type::Base(BaseType::Int);
        let narrowed_by =
            |r: &Refinement| Type::refined(base.clone(), RefinementSet::one(r.clone()));

        // `a == 1` renders below `b == 1`, so `a` applies first and sees the bare base
        // while `b` sees the base narrowed by `a` — from either storage order, which is the
        // whole claim. The vectors are *indexed by storage position*, so the same pairing
        // comes back permuted: `[a, b]` reads `[base, {base | a}]` and `[b, a]` reads
        // `[{base | a}, base]`. Comparing them elementwise would be comparing the storage
        // this test says is meaningless.
        let ab = application_elem_types(&[a.clone(), b.clone()], &base);
        let ba = application_elem_types(&[b.clone(), a.clone()], &base);
        assert_eq!(ab, vec![base.clone(), narrowed_by(&a)], "stored [a, b]");
        assert_eq!(
            ba,
            vec![narrowed_by(&a), base.clone()],
            "stored [b, a] — the same set accumulated the other way, so the same pairing \
             arrives at the other positions"
        );
    }

    /// A predicate that reads a value another refinement narrowed applies after it,
    /// whichever order the set holds them in.
    ///
    /// This ordering is the program's — the outer filter of a nested comprehension reads
    /// the inner-filtered collection — and flattening the two layers into one set records
    /// it nowhere but inside that predicate's own types
    /// ([`application_order`]). Pinned in the storage order that contradicts it, since the
    /// agreeing one passes whether or not the dependency is read at all.
    #[test]
    fn a_predicate_reading_a_narrowed_value_applies_after_that_narrowing() {
        let base = Type::Base(BaseType::Int);
        let inner = Refinement::born(Rc::new(TypedExpr::binop(
            TypedExpr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Equals),
            TypedExpr::lit(Lit::Int(1)),
        )));
        // The outer predicate reads a value typed at the inner refinement's narrowing.
        let outer = Refinement::born(Rc::new(TypedExpr::binop(
            TypedExpr::var(Name::elem()).with_ty(Type::refined(
                base.clone(),
                RefinementSet::one(inner.clone()),
            )),
            BinOpKind::Compare(CompareKind::Equals),
            TypedExpr::lit(Lit::Int(2)),
        )));

        // Stored outer-first, which is the order the dependency forbids.
        let elems = application_elem_types(&[outer.clone(), inner.clone()], &base);
        assert_eq!(
            elems,
            vec![Type::refined(base.clone(), RefinementSet::one(inner)), base],
            "the outer refinement applies second, under the narrowing it reads"
        );
    }

    fn rng(n: usize) -> Type {
        Type::UIntRange(n)
    }

    /// Refusal is a predicate on **one** type against **one** kind — the whole of what a kind
    /// decides for itself, and only the half a rejection may rest on. Containment *between*
    /// two kinds is built from membership and lives with the solver, which is where an edge
    /// can be drawn (`crate::ccl::infer::solver::constrain`, `constrain_type_kinds`).
    #[test]
    fn a_kind_refuses_only_what_it_can_be_certain_of() {
        assert!(!TypeKind::UIntRanges.refuses(&rng(3)));
        assert!(TypeKind::UIntRanges.refuses(&Type::DataSource("s".into())));
        // A refined range is not a range: a filtered collection must be refused rather than
        // handed a length witness for a domain with holes.
        let refined = Type::refined_one(
            rng(3),
            Refinement::born(Rc::new(TypedExpr::lit(Lit::Bool(true)))),
        );
        assert!(TypeKind::UIntRanges.refuses(&refined));
        // An unresolved head is the one thing the range test cannot read, so it abstains.
        assert!(!TypeKind::UIntRanges.refuses(&Type::Hole));
        // `Type` is ⊤ and refuses nothing.
        assert!(!TypeKind::Type.refuses(&Type::DataSource("s".into())));
        // **A bound refuses nothing.** Its membership question is subtyping, which constraint
        // time draws as an edge; standing in for that structurally was certain in neither
        // direction — an exact match admitted an unfixed key's every domain and refused every
        // strict subtype a fixed one accepts.
        assert!(!TypeKind::SubtypesOf(Box::new(Type::Hole)).refuses(&rng(3)));
        assert!(!TypeKind::SubtypesOf(Box::new(rng(3))).refuses(&rng(3)));
        assert!(!TypeKind::SubtypesOf(Box::new(rng(3))).refuses(&rng(2)));
        // Candidates are members, so a concrete type absent from a concrete list is refused.
        assert!(TypeKind::Enumerated(vec![rng(3)]).refuses(&rng(2)));
        assert!(!TypeKind::Enumerated(vec![rng(3)]).refuses(&rng(3)));
        // An unresolved position on either side can still be filled to match, so neither is
        // refused.
        assert!(!TypeKind::Enumerated(vec![rng(3)]).refuses(&Type::Hole));
        assert!(!TypeKind::Enumerated(vec![Type::Hole]).refuses(&rng(2)));
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
                ccl_utils::refined_data_fun(
                    Type::Hole,
                    filter(op),
                    Type::Hole,
                    FunKind::fresh_data(),
                ),
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

    /// A rewrite that makes two refinements equal leaves a *set*, not a bag.
    ///
    /// [`RefinementSet::rewrite_each`]'s callers rewrite predicates in place, and a
    /// substitution mapping two binders onto one term collapses two refinements into
    /// one. `PartialEq` reads cardinality, so a surviving duplicate would make two
    /// sets equal as sets compare unequal.
    #[test]
    fn a_rewrite_that_collapses_two_refinements_leaves_a_set() {
        let eq_to = |name: &str| {
            Refinement::born(Rc::new(TypedExpr::binop(
                TypedExpr::var(Name::elem()),
                BinOpKind::Compare(CompareKind::Equals),
                TypedExpr::var(Name::raw(name)),
            )))
        };
        let mut set = RefinementSet::new();
        set.insert(eq_to("x"));
        set.insert(eq_to("y"));
        assert_eq!(set.len(), 2, "two distinct predicates, two refinements");

        // The collapsing rewrite: both binder references become `z`.
        set.rewrite_each(|_, r| *r = eq_to("z"));

        assert_eq!(
            set.len(),
            1,
            "the collapsed pair is one refinement: {set:?}"
        );
        assert_eq!(
            set,
            RefinementSet::one(eq_to("z")),
            "and equals the set built with one insert"
        );
    }

    /// The same equality from the other side: two cast-target vintages that
    /// render identically stay two refinements.
    ///
    /// [`eq_refinement_predicate`] compares a cast's target predicate because
    /// that predicate is a semantic filter rather than inference metadata
    /// (pinned above by `refinement_eq_distinguishes_cast_target_predicates`).
    /// A resolved `ty` slot makes the rendering elide the target, so the two
    /// vintages are indistinguishable in a diagnostic — and a [`RefinementSet`]
    /// still holds both, because collapsing them would let refinement-deficit
    /// matching accept an unsatisfied demand.
    ///
    /// A pass that decides a cast's refinements from route-dependent context would
    /// mint such a pair out of *one* refinement, and dedup would then correctly refuse
    /// to collapse it — surfacing as a recorded type disagreeing with its
    /// recomputation while printing the same. No pass does: a cast's refinements are
    /// term-determined
    /// ([`ccl_utils::canonical_cast_ty`](crate::ccl::ccl_utils::canonical_cast_ty) /
    /// [`ccl_utils::canonicalize_cast_types`](crate::ccl::ccl_utils::canonicalize_cast_types)),
    /// pinned by `a_cast_target_does_not_carry_its_value_s_refinements`. Nor is the
    /// pair otherwise reachable: instrumenting [`RefinementSet::insert`] for a member
    /// rendering alike without being `eq` counts zero over the corpus in both physical
    /// orders, because a refinement's binding is its index rather than its spelling.
    /// So the hazard was in the pass, not in the equality this pins.
    #[test]
    fn cast_target_vintages_render_alike_but_do_not_dedup() {
        // Two casts of one value, differing *only* in their targets' domain
        // refinement — the shape a discharge mints at two comprehension depths.
        let vintage = |marker: i64| {
            let target = ccl_utils::refined_data_fun(
                Type::Base(BaseType::Int),
                TypedExpr::lit(Lit::Int(marker)),
                Type::Base(BaseType::Int),
                FunKind::fresh_data(),
            );
            Refinement::born(Rc::new(
                ccl_utils::make_cast(TypedExpr::lit(Lit::Int(0)), target)
                    .with_ty(Type::Base(BaseType::Int)),
            ))
        };
        let (a, b) = (vintage(1), vintage(2));
        assert_eq!(
            symbolic::symbolic(&a.predicate),
            symbolic::symbolic(&b.predicate),
            "the two vintages must be indistinguishable in the rendering"
        );
        assert_ne!(a, b, "cast-target predicates distinguish the two vintages");

        let mut set = RefinementSet::new();
        set.insert(a);
        set.insert(b);
        assert_eq!(set.len(), 2, "vintages do not dedup: {set:?}");
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
        let refine = |t: Type| Type::refined_one(t, refinement.clone());
        let int = Type::Base(BaseType::Int);
        let mut_var = Type::History {
            value: Box::new(int.clone()),
            domain: Box::new(Type::Txn),
            history_kind: HistoryKind::Overwrite,
        };
        let channel = Type::History {
            value: Box::new(int.clone()),
            domain: Box::new(Type::UIntRange(3)),
            history_kind: HistoryKind::Append,
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
                history_kind: HistoryKind::Overwrite,
            }
            .as_feed(),
            None
        );

        // A refined *non*-handle peels to a non-handle, which is the case every
        // caller of these accessors actually hits (`x = 0; x += 1`).
        assert_eq!(refine(int).mut_value_type(), None);
    }

    /// The peel reaches the head and stops. A candidate's own filter is what the
    /// caller is about to read, so it has to survive the peel.
    #[test]
    fn peel_refinements_stops_at_the_head() {
        let claim = |tag: &str| Refinement::born(Rc::new(TypedExpr::var(Name::from(tag))));
        let refine = |t: Type, tag: &str| Type::refined_one(t, claim(tag));
        let inner = Type::sum_over(
            TypeKind::Enumerated(vec![refine(Type::UIntRange(3), "p")]),
            None,
            Type::Base(BaseType::Int),
        );
        let wrapped = refine(refine(inner.clone(), "q"), "r");
        assert_eq!(wrapped.peel_refinements(), &inner);
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

    /// A dependent function's refinement *stores* an index and *reads* as the
    /// binder's name, detached from the function or not. Two spellings, two
    /// mechanisms: a rendering that holds the function reads its name slot, and one that does
    /// not falls back to the reference's own hint. Identity is the index in
    /// both cases, which is what the assertion on the term checks.
    #[test]
    fn a_dependent_arrow_renders_its_binder_by_name() {
        let k = Name::raw("k");
        let refined = Type::Refinement(
            Box::new(Type::Base(BaseType::Int)),
            Refinement::born(Rc::new(TypedExpr::binop(
                TypedExpr::var(Name::elem()),
                BinOpKind::Compare(CompareKind::Equals),
                TypedExpr::var(k.clone()),
            )))
            .into(),
        );
        let ty = Type::pi(k.clone(), Type::Base(BaseType::Int), refined);
        assert_eq!(ty.to_string(), "((k: Int) ⇒ {Int | __elem == k})");

        // Detached from the function, the reference still reads as the binder —
        // now off its own hint rather than off the function's name slot. A bare
        // `#0` in a diagnostic tells a reader nothing, and a fragment plucked
        // out of a half-assembled function is exactly what a diagnostic blames.
        let Type::Fun { codomain, .. } = &ty else {
            panic!("expected a function");
        };
        assert_eq!(codomain.to_string(), "{Int | __elem == k}");

        // Stored, though, it is the index: the spelling is metadata that
        // identity ignores, so the refinement is α-canonical.
        let Type::Refinement(_, refinements) = &**codomain else {
            panic!("expected the refinement");
        };
        let refinement = refinements.sole().expect("one refinement");
        let TypedExprNode::BinOp { right, .. } = &refinement.predicate.node else {
            panic!("expected the dependent refinement");
        };
        let TypedExprNode::Var(reference) = &right.node else {
            panic!("expected a variable reference");
        };
        assert_eq!(reference.pi_bound_index(), Some(0));
        assert_eq!(
            *reference,
            Name::pi_bound_bare(0),
            "the hint does not participate in identity"
        );
    }

    /// The index counts function crossings, so an unnamed function between the
    /// reference and its binder occupies an environment entry: dropping it
    /// would resolve the reference to the wrong binder.
    #[test]
    fn an_unnamed_crossing_still_counts_when_rendering() {
        let refined = Type::Refinement(
            Box::new(Type::Base(BaseType::Int)),
            Refinement::born(Rc::new(TypedExpr::var(Name::pi_bound_bare(1)))).into(),
        );
        // (k: Int) ⇒ (Int ⇒ {Int | #1}) — one unnamed crossing in between.
        let ty = Type::Fun {
            name: Some(Name::raw("k")),
            fun_kind: FunKind::Compute,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::fun(Type::Base(BaseType::Int), refined)),
        };
        assert_eq!(ty.to_string(), "((k: Int) ⇒ (Int ⇒ {Int | k}))");
    }
}

#[cfg(test)]
mod witness_identity_tests {
    use super::*;

    /// Deriving carries the binder — a join widens a collection's candidates without
    /// making it a different collection.
    #[test]
    fn with_kind_keeps_the_witness() {
        let w = Witness::mint(TypeKind::Enumerated(vec![Type::UIntRange(2)]));
        let wider = Witness::with_id(
            *w.id(),
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
        );
        assert_eq!(w.id().clone(), wider.id().clone());
    }

    /// Mapping the candidates is a derivation too, so it keeps the binder — this is what
    /// makes every pass's rebuild carry the identity without each one deciding to.
    #[test]
    fn map_types_keeps_the_witness() {
        let w = Witness::mint(TypeKind::Enumerated(vec![Type::UIntRange(2)]));
        let mapped = w.map_types(|_| Type::UIntRange(9));
        assert_eq!(w.id().clone(), mapped.id().clone());
        assert_eq!(
            mapped.type_kind(),
            TypeKind::Enumerated(vec![Type::UIntRange(9)])
        );
    }

    /// `fresh` is the one act of origination, so two of them are two witnesses even at an
    /// identical kind.
    #[test]
    fn fresh_witnesses_at_one_kind_stay_distinct() {
        let type_kind = TypeKind::Enumerated(vec![Type::UIntRange(2)]);
        assert_ne!(
            Witness::mint(type_kind.clone()).id(),
            Witness::mint(type_kind).id()
        );
    }

    /// α-conversion renames the body with the binder. Renaming one without the other is
    /// the stranding every constructor here exists to prevent, so the test asserts both
    /// halves moved together.
    #[test]
    fn alpha_convert_moves_the_body_with_the_binder() {
        let sum = Type::sum_over(
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            None,
            Type::Base(BaseType::Int),
        );
        let converted = sum.alpha_convert_sum();
        let old = &sum.sum().expect("a sum")[0];
        let new = converted.sum().expect("a sum")[0].clone();
        assert_ne!(old.id().clone(), new.id().clone(), "a fresh binder");
        assert_eq!(
            converted.domain(),
            Some(Type::WitnessRef(*new.id())),
            "and the domain names it, not the old one"
        );
        // The **name** is what α-conversion changes — a scheme binds its witness, so each
        // instantiation owes itself its own, asserted above. What the witness ranges over
        // is carried across unchanged: the kind lives on the binder, and renaming a binder
        // says nothing about it.
        assert_eq!(
            old.type_kind(),
            new.type_kind(),
            "ranging over the same domains"
        );
    }
}

#[cfg(test)]
mod witness_subst_tests {
    use super::*;

    fn range(n: usize) -> Type {
        Type::UIntRange(n)
    }

    /// Build a sum over a fresh witness, its body written against that witness's binder.
    fn sum(type_kind: TypeKind, body: impl FnOnce(Witness) -> Type) -> Type {
        let witness = Witness::mint(type_kind);
        let body = body(witness.clone());
        Type::sum_binding(witness, body)
    }

    /// Instantiating a witness in a type that **is** the sum binding it opens the sum: the
    /// choice is answered, so no binder is left to record it. Realization reaches this —
    /// a leg's type slot still holds the whole sum, and the leg's own domain is the answer
    /// ([`crate::ccl::ty::instantiate_witness`]). Walking through the sum instead would
    /// rebuild it around a body that no longer mentions its witness.
    #[test]
    fn instantiating_a_sum_at_its_own_binder_opens_it() {
        let elem = Type::Base(BaseType::Int);
        let whole = sum(TypeKind::Enumerated(vec![range(2)]), |w| {
            Type::data_fun(Type::WitnessRef(*w.id()), elem.clone())
        });
        let binder = whole.sum().expect("a sum")[0].id();
        assert_eq!(
            instantiate_witness(&whole, binder, &range(2)),
            Type::data_fun(range(2), elem),
            "the sum is opened at the candidate, not rebuilt around it"
        );
    }

    /// Instantiation rewrites the domain, leaving the codomain — the witness-independent
    /// residue — untouched.
    #[test]
    fn an_arrow_body_instantiates_only_its_domain() {
        let s = sum(TypeKind::UIntRanges, |w| {
            Type::data_fun(Type::WitnessRef(*w.id()), Type::Base(BaseType::Int))
        });
        assert_eq!(
            s.instantiate_sum(&range(2)),
            Type::data_fun(range(2), Type::Base(BaseType::Int))
        );
    }

    /// **Both spellings of one collection answer the same.** After `lambda_elim` the `Σ`
    /// sits at the position that binds the witness and every interior position carries the
    /// body with the witness free, so a reader testing only the slot answers `false` at
    /// every interior position — which is how a witness-indexed collection gets treated
    /// as a written domain.
    #[test]
    fn both_spellings_are_witness_indexed() {
        let int = Type::Base(BaseType::Int);
        let closed = sum(TypeKind::UIntRanges, |w| {
            Type::data_fun(Type::WitnessRef(*w.id()), int.clone())
        });
        // The open spelling: the same function with the occurrence free (no slot).
        let open = Type::data_fun(closed.domain().expect("a sum is a function"), int.clone());
        assert!(closed.is_witness_indexed(), "the closed spelling: {closed}");
        assert!(open.is_witness_indexed(), "the open spelling: {open}");
        // A written domain is neither.
        assert!(!Type::data_fun(range(2), int).is_witness_indexed());
    }

    /// A consumer's filter rides the witness, so a restricted collection is
    /// witness-indexed like an unrestricted one.
    #[test]
    fn a_restriction_does_not_hide_the_witness() {
        let inner = sum(TypeKind::UIntRanges, |w| {
            Type::data_fun(Type::WitnessRef(*w.id()), Type::Base(BaseType::Int))
        });
        let refined = Type::refined_one(
            inner,
            Refinement::born(Rc::new(
                TypedExpr::new(TypedExprNode::Lit(Lit::Bool(true)))
                    .with_ty(Type::Base(BaseType::Bool)),
            )),
        );
        assert!(refined.is_witness_indexed());
        assert!(refined.witness_kind().is_some());
    }

    /// **Only a binding position carries the kind.** A range belongs to its binder, so the
    /// body cannot report one — and the `None` it answers is not "no witness", which is
    /// why the two questions are separate accessors. A caller needing the kind after
    /// inference has to read it off a position that binds.
    #[test]
    fn only_the_binding_position_reports_the_witness_kind() {
        let int = Type::Base(BaseType::Int);
        let closed = sum(TypeKind::Enumerated(vec![range(2)]), |w| {
            Type::data_fun(Type::WitnessRef(*w.id()), int.clone())
        });
        let open = Type::data_fun(closed.domain().expect("a sum is a function"), int.clone());
        assert_eq!(
            closed.witness_kind(),
            Some(TypeKind::Enumerated(vec![range(2)]))
        );
        assert_eq!(open.witness_kind(), None, "the body has no binder: {open}");
        // ...and it is witness-indexed all the same, which is the distinction.
        assert!(open.is_witness_indexed());
    }

    /// A nested sum's body names the **inner** binder, so substituting the outer one
    /// leaves it alone. The rule is identity, not nesting position: this holds however
    /// deeply the inner sum sits, and would hold even if it did not nest at all.
    #[test]
    fn a_nested_sums_body_is_not_captured() {
        let inner = sum(TypeKind::UIntRanges, |w| {
            Type::data_fun(Type::WitnessRef(*w.id()), Type::Base(BaseType::Int))
        });
        let outer = sum(TypeKind::Enumerated(vec![range(1)]), |w| {
            Type::data_fun(Type::WitnessRef(*w.id()), inner.clone())
        });
        assert_eq!(
            outer.instantiate_sum(&range(1)),
            Type::data_fun(range(1), inner.clone()),
            "the outer binder is substituted; the inner sum's domain is untouched"
        );
    }

    /// A candidate in a nested sum's **kind** is a type in the *outer* scope, so
    /// it may name the outer witness — and substituting the outer binder rewrites it,
    /// while the inner sum's own body is untouched in the same pass.
    #[test]
    fn a_nested_sums_candidates_are_in_the_outer_scope() {
        let outer_witness = Witness::mint(TypeKind::Enumerated(vec![range(4)]));
        let inner = sum(
            TypeKind::Enumerated(vec![Type::WitnessRef(*outer_witness.id())]),
            |w| Type::data_fun(Type::WitnessRef(*w.id()), Type::Base(BaseType::Int)),
        );
        let inner_binder = *inner.sum().expect("a sum")[0].id();
        let outer = Type::sum_binding(outer_witness, inner);
        let got = outer.instantiate_sum(&range(4));
        let Some([w]) = got.sum() else {
            panic!("instantiating the outer binder keeps the inner sum, got {got}");
        };
        assert_eq!(
            w.type_kind(),
            TypeKind::Enumerated(vec![range(4)]),
            "the outer witness in the inner kind is substituted"
        );
        assert_eq!(
            got.domain(),
            Some(Type::WitnessRef(inner_binder)),
            "the inner sum's own domain still names its own binder"
        );
    }
}

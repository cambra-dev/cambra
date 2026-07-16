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

/// Whether a [`Type::Fun`]'s domain is a **capability** or an **extent** — the
/// compute-function vs data-function distinction.
///
/// - [`FunKind::Compute`] — `α ⇒ β`: the domain is a *capability*, the inputs
///   the function accepts. No data sits behind it, so shrinking the domain only
///   under-promises; the contravariant meet at a control-flow join is a sound,
///   lossy simplification.
/// - [`FunKind::Data`] — `α ⤇ β`: the domain is an *extent*, a collection's
///   index set. The domain *is* the data map, so a lossy domain is lost data;
///   joins of data functions must be lossless — they form a [`Type::Sigma`]
///   over the extents, never a meet.
///
/// Set at introduction (list literals, comprehensions, `++`, registered
/// sources, and every `History` erasure are `Data`; `lambda`/`def` are
/// `Compute`). The audit rule for a rebuilt or erased arrow: it is `Data` iff
/// `extent_of` will drive iteration off its domain. See
/// `design/type-inference.md` §4.6.
///
/// Kind is **inferred** (PR1.5, see `brainstorm/2026-07-15-kind-inference.md`):
/// where the structure fixes it (a list literal is `Data`, a scalar op is
/// `Compute`) a concrete kind is stamped; where it depends on use or on an
/// unresolved source (a map/comprehension) a [`FunKind::Var`] is minted and the
/// solver resolves it, like a type variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunKind {
    /// Capability domain (`⇒`): lossy meet at a join is fine.
    Compute,
    /// Extent domain (`⤇`): the domain is data; joins must be lossless.
    Data,
    /// An unresolved kind, pinned down by the solver at coalesce. Identity is by
    /// the variable's `uid`, so `FunKind` (and `Type`) keep deriving
    /// `PartialEq`/`Eq`/`Hash` — the [`KindVar`] impls compare by `uid` only.
    Var(Rc<KindVar>),
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

    /// A fresh inferred kind (a new [`KindVar`] with empty bounds).
    pub fn fresh_var() -> FunKind {
        FunKind::Var(KindVar::fresh())
    }
}

/// Stable identity of a [`KindVar`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KindVarId(pub(crate) u32);

static KIND_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

/// Bounds on a [`KindVar`], over the two-point kind lattice `Data ⊑ Compute`.
///
/// The lattice has only two points, so "bounds" collapse to two flags rather
/// than the polar bound *lists* an [`crate::ccl::InferVar`] carries — and no
/// [`Type`] sits inside, so a `KindVar` never forms a cycle. Resolution is a
/// flag read: `forced_compute ∧ forced_data` is the conflict (`Compute ⊑ κ ⊑
/// Data`, impossible — the `Compute <: Data` rejection); `forced_compute` alone
/// → `Compute`; `forced_data` alone → `Data`; neither → the caller's
/// domain-derived default.
#[derive(Debug, Default, Clone, Copy)]
pub struct KindBounds {
    /// A `Compute` value flows *into* this kind (`κ ⊒ Compute ⟹ κ = Compute`).
    pub forced_compute: bool,
    /// This kind is *demanded* as `Data` (`κ ⊑ Data ⟹ κ = Data`).
    pub forced_data: bool,
}

/// A kind-inference variable — an unknown [`FunKind`] the solver pins down by
/// accumulating [`KindBounds`]. Identity (`uid`) is immutable and lives outside
/// the `RefCell`, so equality/hashing is borrow-free and never inspects the
/// bounds (mirroring [`crate::ccl::InferVar`]).
pub struct KindVar {
    /// Stable, globally-unique identity.
    pub uid: KindVarId,
    /// Mutable kind bounds.
    pub bounds: RefCell<KindBounds>,
    /// Vars `u` such that `self <: u` (this kind is below them). A `Compute`
    /// force propagates *up* to them (`self = Compute ⟹ u = Compute`).
    uppers: RefCell<Vec<Rc<KindVar>>>,
    /// Vars `l` such that `l <: self` (this kind is above them). A `Data` force
    /// propagates *down* to them (`self = Data ⟹ l = Data`).
    lowers: RefCell<Vec<Rc<KindVar>>>,
}

impl KindVar {
    /// Allocate a fresh kind variable with empty bounds and no links.
    pub fn fresh() -> Rc<KindVar> {
        Rc::new(KindVar {
            uid: KindVarId(KIND_VAR_COUNTER.fetch_add(1, Ordering::Relaxed)),
            bounds: RefCell::new(KindBounds::default()),
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
    /// The dual of [`KindVar::force_compute`]; same fixpoint/termination argument.
    pub fn force_data(self: &Rc<Self>) {
        if self.bounds.borrow().forced_data {
            return;
        }
        self.bounds.borrow_mut().forced_data = true;
        for l in self.lowers.borrow().iter() {
            l.force_data();
        }
    }

    /// Record the edge `lower <: upper` and reconcile the flags already present
    /// on either end. Later forces on either var propagate through the stored
    /// link via [`KindVar::force_compute`]/[`KindVar::force_data`].
    pub fn link(lower: &Rc<KindVar>, upper: &Rc<KindVar>) {
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
impl PartialEq for KindVar {
    fn eq(&self, other: &Self) -> bool {
        self.uid == other.uid
    }
}
impl Eq for KindVar {}
impl std::hash::Hash for KindVar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.uid.hash(state);
    }
}
impl fmt::Debug for KindVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "κ{}", self.uid.0)
    }
}

/// Reset the kind-variable counter to zero (test-only, for predictable output).
#[cfg(any(test, feature = "test-helpers"))]
pub fn reset_kind_var_counter() {
    KIND_VAR_COUNTER.store(0, Ordering::Relaxed);
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
/// | `Infer(id)` | Type checker only | "Inference variable N from the coalesce pass" | End of inference for any type reachable from the program's root output (flagged as `UnresolvedInfer` by `collect_type_errors`); an induction store's *domain* is necessarily `Infer` until the unified phase resolves it (see `Strictness::PreDesugar`) |
/// | `History` (`kind: Store`) | Type checker only | "Mutable store: a `value` cell tracked over a `domain` (loop index or transaction time)" | the unified phase (`transact_phase` / `mut_elim`, which runs *before* `channelize`; a survivor downstream is a compiler bug) |
/// | `History` (`kind: Feed`) | Type checker only | "Feed channel `domain ⇒ value`: the defer binding's post-desugar stream type" | `channelize` (which runs after inference; a survivor downstream is a compiler bug) |
/// | `ChanDom(d, _)` | Type checker only | "Rigid nominal domain of feed channel `d` — its extent resolves at channel assembly" | `channelize` (substituted to the concrete channel domain; a survivor downstream is a compiler bug) |
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
        /// Whether the domain is a capability (`Compute`) or an extent
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
    /// `f = lambda x: x` that is never applied).
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
    /// extent resolves later; unlike it, it is *transient* — no pass after
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
    /// `DataSource`, it has no enumerable static extent — its positions exist only
    /// in the tile. See src/ccl/design/mutability.md.
    Txn,
    /// The type of a **history** handle: a function `domain ⇒ value` that a
    /// `:=` store or a `defer`/`<<` channel writes incrementally. One variant
    /// for both — a mutable store and a feed channel are the same object (an
    /// invariant, deref-transparent `domain ⇒ value`); they differ only in the
    /// [`HistoryKind`]:
    ///
    /// - [`HistoryKind::Overwrite`] — a **mutable store** (`:=` / `+=`). A reference
    ///   reads through to its `value` (the scalar behind `Mut[Int, D]`; `cnt + 1`
    ///   reads the `Int`), its writes may read the previous position
    ///   (`get_prev_seq` recurrence), and its trailing read is `last_or_default`
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
    /// (`transact_phase` / `mut_elim`) for `Store` histories, `channelize`
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
        /// Whether this is a mutable store or a feed channel — selects the read
        /// mode (scalar-last vs whole-stream) and, in the unified phase, whether
        /// off-path positions carry forward.
        kind: HistoryKind,
    },
    /// A dependent sum over a finite set of candidate **extents** — the
    /// lossless join of data functions at a control-flow merge:
    /// `Σ name ∈ {choices}. (pi_name: name) ⤇ codomain`.
    ///
    /// A `Σ` is always a data function (there is no `kind` field — it is
    /// `Data` by construction). Its structural shape is fixed: the witness
    /// occupies the arrow's *domain* position, so no type-level variable leaf
    /// exists. The witness `name` is referencable only by refinement predicates
    /// inside `codomain` (the same term-level `Var(name)` mechanism as a
    /// [`Type::Fun`] Pi binder), denotes the chosen extent opaquely (the
    /// `DataSource`-domain species), and is **only ever discharged, never
    /// evaluated** — see `discharge_sigma`. It is kept iff a codomain predicate
    /// references it (the Pi keep-iff-referenced filter at coalesce); until
    /// witness-referencing predicates exist it is always `None`, so the
    /// machinery is live but dormant.
    ///
    /// Formed at the compact merge (`sigma_join`) and materialized by coalesce;
    /// eliminated by the value-`Case` fan-out (PR2). See
    /// `design/type-inference.md` §4.6.
    ///
    /// The payload is boxed to keep `Type` small — a Σ is rare, but `Type` is
    /// cloned pervasively, and inlining a `Vec` + two `Option<Name>` would
    /// roughly double every `Type`'s footprint.
    Sigma(Box<SigmaType>),
    // Planned:
    // Pi { param: String, param_ty: Box<Type>, body_ty: Box<Type> }
    // Refinement { base: Box<Type>, predicate: Box<Expr> }
}

/// The payload of a [`Type::Sigma`] — a dependent sum
/// `Σ name ∈ {choices}. (pi_name: name) ⤇ codomain`. Boxed inside `Type` to
/// keep the enum small.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SigmaType {
    /// The Σ witness (the chosen extent). `Some` iff a `codomain` predicate
    /// references it; `None` in the common (and, in PR1, every) case.
    pub name: Option<crate::ccl::Name>,
    /// The candidate extents. Invariant (asserted at materialization):
    /// `len >= 2`, deduped, each domain-shaped, none itself a `Sigma`.
    pub choices: Vec<Type>,
    /// The underlying arrow's own element binder, bound in `codomain` (the
    /// `Fun`-`name` slot each choice would carry as a data function).
    pub pi_name: Option<crate::ccl::Name>,
    /// The shared element type (`τ₀ ⊔ τ₁`), covariant; may reference `name`
    /// and `pi_name` through refinement predicates.
    pub codomain: Box<Type>,
}

/// Which flavour of [`Type::History`] a handle is — a mutable store (`:=`) or a
/// feed channel (`defer` / `<<`). The two are the same object (a `domain ⇒
/// value` history) but read and materialize differently; see [`Type::History`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HistoryKind {
    /// A mutable store introduced by `:=` — deref-on-read to the scalar `value`,
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Base(b) => write!(
                f,
                "{}",
                match b {
                    BaseType::Int => "Int",
                    BaseType::UInt => "UInt",
                    BaseType::String => "String",
                    BaseType::Bool => "Bool",
                    BaseType::Unit => "Unit",
                }
            ),
            // `n == 0` means an empty range (e.g. the domain of `[]`); render
            // it as `∅` instead of computing `n - 1` and underflowing.
            Type::UIntRange(0) => write!(f, "∅"),
            Type::UIntRange(n) => write!(f, "[0, {}]", n - 1),
            // The arrow reflects the resolved `kind`: `⇒` for a compute
            // capability (and an unresolved kind var), `⤇` for a data extent
            // (see `FunKind::arrow`). Once kind inference resolves every arrow
            // (PR1.5), a data collection renders `⤇`, making the extent/capability
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
                    let parts: Vec<_> = tags
                        .iter()
                        .map(|(n, t)| {
                            if matches!(t, Type::Base(BaseType::Unit)) {
                                format!(".{n}")
                            } else {
                                format!(".{n}({t})")
                            }
                        })
                        .collect();
                    write!(f, "[{}]", parts.join(" | "))
                }
            }
            Type::Refinement(t, r) => {
                write!(f, "{{{t} | {}}}", symbolic::symbolic(&r.predicate))
            }
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
                    write!(f, "Mut[{value}, {domain}]")
                } else {
                    write!(f, "feed({domain} ⇒ {value})")
                }
            }
            Type::Sigma(s) => {
                let cs: Vec<_> = s.choices.iter().map(|t| t.to_string()).collect();
                let codomain = &s.codomain;
                match &s.name {
                    // Named witness (referenced by a codomain predicate):
                    // `(Σ n ∈ {D0, D1}. n ⤇ V)`.
                    Some(n) => write!(f, "(Σ {n} ∈ {{{}}}. {n} ⤇ {codomain})", cs.join(", ")),
                    // Anonymous (the common/dormant case): `Σ{D0, D1} ⤇ V`.
                    None => write!(f, "Σ{{{}}} ⤇ {codomain}", cs.join(", ")),
                }
            }
        }
    }
}

impl Type {
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

    /// Helper for creating a dependent (Pi) function type whose **kind is
    /// inferred** — a fresh [`FunKind::Var`]. Used by `emit_lambda`: a user
    /// lambda is a capability *or* a collection map depending on its domain and
    /// use, neither known at emit, so the kind is left to the solver (PR1.5).
    pub fn pi_inferred_kind(
        name: impl Into<crate::ccl::Name>,
        domain: Self,
        codomain: Self,
    ) -> Self {
        Type::Fun {
            name: Some(name.into()),
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

    /// Helper for creating a dependent (Pi) **data** function type
    /// `(name: domain) ⤇ codomain`.
    pub fn data_pi(name: impl Into<crate::ccl::Name>, domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: Some(name.into()),
            kind: FunKind::Data,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Rebuild a function type copying `name` and `kind` from an `exemplar`
    /// `Fun`, so a downstream rebuild (lambda elimination, inlining, planning)
    /// can never silently flip a data arrow to compute or drop its Pi binder. A
    /// non-`Fun` exemplar yields a plain `Compute` arrow with no binder — the
    /// safe default at a site with no arrow to copy from.
    pub fn fun_like(exemplar: &Type, domain: Self, codomain: Self) -> Self {
        match exemplar {
            Type::Fun { name, kind, .. } => Type::Fun {
                name: name.clone(),
                kind: kind.clone(),
                domain: Box::new(domain),
                codomain: Box::new(codomain),
            },
            _ => Type::fun(domain, codomain),
        }
    }

    /// Helper for creating a [`Type::Sigma`] over candidate extents.
    pub fn sigma(
        name: Option<crate::ccl::Name>,
        choices: Vec<Type>,
        pi_name: Option<crate::ccl::Name>,
        codomain: Type,
    ) -> Self {
        Type::Sigma(Box::new(SigmaType {
            name,
            choices,
            pi_name,
            codomain: Box::new(codomain),
        }))
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

    /// Whether this type's positions can be statically enumerated — i.e. a
    /// terminal reduction over a `Fun` of this domain converges. A live commit
    /// history (`Txn`) has **no** enumerable extent: its positions are revealed
    /// only as commits land, so a `last_or_default` over one never resolves.
    /// `transact_phase::rewrite_live_reads` uses this to detect that a broadcast
    /// read's store is a live commit log (`Txn`) and rewrite it to an as-of join
    /// instead of broadcasting a never-resolving terminal render.
    ///
    /// The match is **exhaustive on purpose** (no `_` arm): the predicate is
    /// load-bearing, so a new abstract domain whose elements live in a producer
    /// must make an explicit decision here rather than silently defaulting to
    /// enumerable. `DataSource` is enumerable-from-the-type (its extent resolves
    /// from the registered source); only `Txn` is genuinely non-enumerable.
    ///
    /// A `Fun` defers to its **domain**: iterating a function converges iff its
    /// domain does. This is what makes the predicate safe to call on a whole
    /// history function (`Txn ⇒ V` → non-enumerable), not just an extracted
    /// domain — a store history is exactly a `Fun { domain: Txn, .. }`, so a
    /// blanket `Fun ⇒ true` would have mis-answered the very case this exists to
    /// detect.
    pub fn has_enumerable_extent(&self) -> bool {
        match self {
            Type::Txn => false,
            Type::Fun { domain, .. } => domain.has_enumerable_extent(),
            // A Σ is enumerable iff every candidate extent is — each choice is
            // a real alternative the collection might turn out to be.
            Type::Sigma(s) => s.choices.iter().all(Type::has_enumerable_extent),
            Type::Tuple(ts) => ts.iter().all(Type::has_enumerable_extent),
            Type::Record(fields) => fields.iter().all(|(_, t)| t.has_enumerable_extent()),
            Type::Variant(tags) => tags.iter().all(|(_, t)| t.has_enumerable_extent()),
            Type::Refinement(inner, _) => inner.has_enumerable_extent(),
            // A store history is erased by the unified phase
            // (`mut_elim`/`transact_phase`) and a feed history by `channelize`,
            // both before planning consults this predicate; observing one here is
            // a compiler bug.
            Type::History { .. } => unreachable!("Type::History survived its erasing phase"),
            // Erased by `channelize` (before planning); a survivor here
            // is a compiler bug, same as `History`.
            Type::ChanDom(..) => unreachable!("Type::ChanDom survived channelize"),
            // Concrete or type-resolvable domains: enumerable from the type alone.
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Hole
            | Type::Infer(_) => true,
        }
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
    /// Kind is normalized for the same reason: **lambda elimination preserves a
    /// function's denotation but not its kind representation** — a data
    /// collection (`⤇`) becomes a point-free form built from compute combinators
    /// (`zip`, `apply`, `const`), so the reconstructed arrow reads `Compute`
    /// though it denotes the same collection. The kind did its work at inference
    /// (lossless Σ joins at coalesce); post-elimination it is not preserved, so
    /// the structural-equality asserts (and the feed-operand agreement check)
    /// compare modulo it. (Kind-aware subtyping, PR1.5 stage 4, therefore acts in
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
            // Normalize the Σ witness and element binder to `None` alongside Pi
            // binders — the same α-blindness downstream structural comparisons
            // rely on.
            Type::Sigma(s) => Type::sigma(
                None,
                s.choices.iter().map(|t| t.without_pi_names()).collect(),
                None,
                s.codomain.without_pi_names(),
            ),
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
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
            | Type::Infer(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
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
            // A Σ's children are its candidate extents and its codomain (the
            // witness/pi binders are names, not types).
            Type::Sigma(s) => {
                for c in &s.choices {
                    f(c);
                }
                f(&s.codomain);
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
            // A Σ's children are its candidate extents and its codomain (the
            // witness/pi binders are names, not types).
            Type::Sigma(s) => {
                for c in &mut *s.choices {
                    f(c);
                }
                f(&mut s.codomain);
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
    /// lets the post-planning `typecheck` chain the re-minted witnesses. This
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
/// denote different refinements; conflating them would let witness-deficit
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
                ccl_utils::refined_fn_type(Type::Hole, filter(op), Type::Hole),
            )
        };
        let refinement = |pred: TypedExpr| Refinement {
            predicate: Rc::new(pred),
        };

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
}

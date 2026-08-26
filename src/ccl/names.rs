//! Structured binder names. The five ways a name can come to exist are five
//! variants, so the case a site handles is a `match` arm, not a magic-value
//! check on a shared field.
//!
//! * [`Name::Raw`] — what **lowering** builds: a spelling lifted straight from
//!   source, where two distinct binders can share one spelling (Python
//!   reassignment lowers to a shadowing `let`). Identity is the string.
//! * [`Name::Unique`] — a **uniquified source binder**: a binder the user
//!   wrote, given a globally distinct `uid` by uniquification
//!   ([`crate::ccl::uniquify`]). Identity is the `uid`; the `base` is the
//!   source spelling, kept as display metadata. The convention: copies
//!   preserve the `uid`, and nothing mints a fresh `uid` on an
//!   equality-mediated path — so plain structural equality coincides with
//!   α-equivalence, and capture-avoidance can be asserted unreachable. The
//!   payoff of restricting this variant to *source* binders: `base` is always
//!   a real identifier (trustworthy in errors), and "after uniquification
//!   every binder is `Unique`" is a meaningful, checked invariant — every
//!   binder traces to source.
//! * [`Name::Synthetic`] — a **compiler-introduced binder**: a [`Uid`] for
//!   identity (like [`Name::Unique`], from the same fresh-id space) plus a
//!   provenance [`SyntheticKind`] (the tupled binder lambda elimination mints,
//!   a monomorphization specialization, the defer-plumbing names, the solver's
//!   dependent-application binder). It shares everything operational with
//!   `Unique` — globally distinct, capture-free, uid-identity — and differs
//!   only in *provenance*: minted by a pass, not written by the user, so it
//!   carries **no source spelling** (the old mangled string was noise; the
//!   `kind` stem is its whole display). That distinction keeps `Unique`'s
//!   invariant exact (a `Synthetic` at the post-uniquify checkpoint is a bug:
//!   a pass minted too early) and lets code recognize a binder's origin by its
//!   `kind` rather than by parsing a spelling.
//! * [`Name::Reserved`] — a name with **custom semantics** ([`ReservedName`]).
//!   The only one today is the refinement element binder `__elem`: every
//!   refinement implicitly binds the *same* one (see [`crate::ccl::Refinement`]),
//!   which is what makes refinement equality plain structural equality of bare
//!   predicates. Uniquification never mints it; substitution shadows it.
//! * [`Name::PiBound`] — a **bound reference to an enclosing function's Pi
//!   binder**, as a de Bruijn index ([`PiRef`]). Not a binder: nothing
//!   introduces one; a reference becomes one when function construction closes
//!   its codomain ([`crate::ccl::subst::close_pi_binder`]) and becomes a name
//!   or a term again when descent or application opens the function
//!   ([`crate::ccl::subst::open_pi_binder`]). Identity is the index, so two
//!   α-variant closed function types are structurally identical — what the solver's
//!   identity sites key on — and the binder's source spelling rides alongside
//!   it as display metadata.
//!
//! Display prints [`Name::base`] — under the convention names are distinct, so
//! the spelling is unambiguous in almost every rendering. `Debug` surfaces the
//! `uid` for [`Name::Unique`].

use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

/// A globally-fresh binder identity. Minted only via [`Uid::fresh`]; nothing
/// observes its numeric value (only `uid` *equality*), so non-determinism
/// across process runs is fine — uniqueness is all that matters.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Uid(u64);

static FRESH_UID: AtomicU64 = AtomicU64::new(1);

impl Uid {
    fn fresh() -> Self {
        Uid(FRESH_UID.fetch_add(1, Ordering::Relaxed))
    }
}

impl fmt::Debug for Uid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A name carrying semantics beyond "a binder." Each variant has a canonical
/// spelling and is constructed only through its dedicated [`Name`] constructor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReservedName {
    /// The refinement element binder, spelled `__elem`. One shared name across
    /// every refinement (see the module docs and [`crate::ccl::Refinement`]).
    Elem,
}

impl ReservedName {
    /// The canonical source-disjoint spelling.
    pub fn spelling(self) -> &'static str {
        match self {
            ReservedName::Elem => "__elem",
        }
    }
}

/// The role of a [`Name::Synthetic`] — which pass minted it and why. The tag
/// *is* the synthetic's only meaning beyond its [`Uid`]: a synthetic carries no
/// source spelling, so this is how code recognizes its provenance, and
/// [`SyntheticKind::stem`] is its whole display.
///
/// Not [`Copy`]: [`SyntheticKind::Mono`] carries the source binding's [`Name`]
/// as provenance, so a kind owns heap data. Clone where a copy is needed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntheticKind {
    /// The tupled binder lambda elimination mints merging `λx→λy→body` into
    /// `λ__pair→…`.
    Pair,
    /// A per-resolved-type specialization of a generalized `let`, from
    /// monomorphization. Carries the **source binding's name** it specializes
    /// (e.g. `f` for an `f__mono`), so a specialization's provenance is read
    /// off its `kind` rather than parsed from a mangled spelling. (Boxed: a
    /// `Name` may itself be a `Synthetic` carrying a `SyntheticKind`, so the
    /// reference must be indirected to keep the type finite-sized.)
    Mono(Box<Name>),
    /// A lambda/binding floated out during channelization.
    FloatedDefer,
    /// The fresh binder the solver mints for a dependent application's
    /// expected Pi type (`(__arg: d) ⇒ result`), discharged to the argument.
    SolverArg,
}

impl SyntheticKind {
    /// The display stem for this kind (e.g. `__pair`). A synthetic renders as
    /// just this — like a [`Name::Unique`]'s `base`, it is ambiguous across
    /// instances on purpose (the [`Uid`] disambiguates, surfaced via `Debug`).
    pub fn stem(&self) -> &'static str {
        match self {
            SyntheticKind::Pair => "__pair",
            SyntheticKind::Mono(_) => "__mono",
            SyntheticKind::FloatedDefer => "__floated",
            SyntheticKind::SolverArg => "__arg",
        }
    }
}

/// A reference to an enclosing function's Pi binder: a de Bruijn `index` plus the
/// binder's source spelling.
///
/// **`index` is the identity.** `PartialEq`/`Ord`/`Hash` read it alone, so two
/// α-variant closed types compare equal wherever the solver decides identity,
/// which is the whole point of the locally-nameless representation
/// (`src/ccl/design/type-inference.md`, "A binder reference is stored in one of
/// two forms").
///
/// **`hint` is display metadata**, stamped by the closing walk from the binder
/// it just abstracted. Its job is a type rendered *detached* from the function
/// that binds it: a diagnostic that blames a domain plucked out of a
/// half-assembled function has none to read a spelling off, and a bare `#0`
/// reaching a user says nothing. Two equal `PiRef`s may therefore carry
/// different hints and print differently — the hint never decides anything.
///
/// A rendering that *does* hold the function prefers its own name slot
/// (see [`crate::ccl::symbolic::PiBinderEnv`]): a later pass may rename the
/// binder, which leaves the hint stale and the name slot right.
#[derive(Clone, Debug)]
pub struct PiRef {
    /// Codomain crossings between the reference and the function binding it.
    pub index: u32,
    /// The binder's spelling where the closing happened. Display only.
    ///
    /// Boxed to keep [`Name`] at the width its `Unique` variant already needs:
    /// an inline `SmolStr` here fits the payload but leaves the enum no niche
    /// for its discriminant, which widens every `Name` in the IR. The
    /// allocation is per distinct closed refinement, not per comparison:
    /// [`RefinementScope`] memoizes on (predicate, enclosing binders).
    ///
    /// [`RefinementScope`]: crate::ccl::subst::RefinementScope
    pub hint: Option<Box<str>>,
}

impl PiRef {
    /// A reference to the function `index` crossings out, with no spelling. Every
    /// reference a conversion mints carries the binder it abstracted
    /// ([`Name::pi_bound`]), so this is for a test naming a reference directly, and
    /// what it exercises is that the spelling decides nothing.
    pub fn bare(index: u32) -> Self {
        PiRef { index, hint: None }
    }
}

impl PartialEq for PiRef {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl Eq for PiRef {}

impl PartialOrd for PiRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PiRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index.cmp(&other.index)
    }
}

impl std::hash::Hash for PiRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

/// A binder or variable name. See the module docs for the five variants.
///
/// Derived `Eq`/`Ord`/`Hash` compare the whole variant. For [`Name::Unique`]
/// that compares `(base, uid)` and for [`Name::Synthetic`] `(kind, uid)`,
/// both of which coincide with uid-identity under the convention (a fresh
/// `uid` is minted per binder, copies preserve it) — the other fields can
/// never disagree with the `uid`. The `uid`s of a `Unique` and a `Synthetic`
/// are drawn from one space but the two are different variants, so they never
/// collide.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Name {
    /// Lowering's output; identity is the string. See module docs.
    Raw(String),
    /// A uniquified source binder; identity is `uid`, `base` is the source
    /// spelling kept as display metadata.
    Unique { base: String, uid: Uid },
    /// A compiler-introduced binder; identity is `uid`, `kind` is its
    /// provenance and whole display (no source spelling — that was noise).
    Synthetic { kind: SyntheticKind, uid: Uid },
    /// A name with custom semantics (currently only `__elem`).
    Reserved(ReservedName),
    /// A bound reference to an enclosing function's Pi binder ([`PiRef`]): the
    /// number of `Fun` codomains crossed between the reference and the function
    /// that binds it, named and unnamed alike (so the index
    /// survives `Type::without_pi_names`), plus the binder's spelling as
    /// display metadata. Assigned at abstraction by
    /// [`crate::ccl::subst::close_pi_binder`]; converted back to a name or a
    /// term by [`crate::ccl::subst::open_pi_binder`] when descent or
    /// application opens the function. Never a binder — no binding site
    /// introduces one, uniquification never mints one, and a substitution
    /// never maps one (a [`crate::ccl::subst::Subst`] domain is free names).
    /// See `src/ccl/design/type-inference.md`, "A binder reference is stored
    /// in one of two forms".
    PiBound(PiRef),
}

impl Name {
    /// A raw lowering name (identity is the string). Reserved spellings must go
    /// through their dedicated constructor instead, or they would compare
    /// unequal to the reserved variant — the `debug_assert` catches that slip.
    pub fn raw(base: impl Into<String>) -> Self {
        let base = base.into();
        debug_assert!(
            base != ReservedName::Elem.spelling(),
            "`{base}` is a reserved spelling — construct it via its Name constructor, not raw()",
        );
        Name::Raw(base)
    }

    /// Mint a uniquified source binder: this source `base` for display, a
    /// globally fresh `uid` for identity. Uniquification's minter — the only
    /// thing that should produce a [`Name::Unique`] (a compiler-introduced
    /// binder is a [`Name::Synthetic`], not this).
    pub fn fresh(base: impl Into<String>) -> Self {
        Name::Unique {
            base: base.into(),
            uid: Uid::fresh(),
        }
    }

    /// The refinement element binder `__elem`.
    pub fn elem() -> Self {
        Name::Reserved(ReservedName::Elem)
    }

    /// Mint a compiler-introduced binder of `kind` with a globally fresh
    /// `uid`. The named wrappers below are the call-site vocabulary.
    fn synthetic(kind: SyntheticKind) -> Self {
        Name::Synthetic {
            kind,
            uid: Uid::fresh(),
        }
    }

    /// The tupled binder merging `λx→λy→…` (lambda elimination).
    pub fn pair() -> Self {
        Self::synthetic(SyntheticKind::Pair)
    }

    /// A monomorphization specialization of the generalized `let` bound to
    /// `source` — its name rides on the `kind` as provenance.
    pub fn mono(source: Name) -> Self {
        Self::synthetic(SyntheticKind::Mono(Box::new(source)))
    }

    /// A lambda/binding floated out during channelization.
    pub fn floated() -> Self {
        Self::synthetic(SyntheticKind::FloatedDefer)
    }

    /// The solver's fresh dependent-application binder
    /// (`(__arg: d) ⇒ result`, discharged to the argument).
    pub fn solver_arg() -> Self {
        Self::synthetic(SyntheticKind::SolverArg)
    }

    /// The display spelling. Total over every variant; never use it for an
    /// identity decision — that is what `Name` equality is for, and for a
    /// [`Name::PiBound`] the spelling is metadata that identity ignores
    /// outright ([`PiRef`]).
    ///
    /// A hint-less [`Name::PiBound`] has no spelling to give, and the bare `#`
    /// it falls back to reads as a name while dropping the index that carries
    /// the whole content. Every reference a conversion mints carries the binder
    /// it abstracted ([`Name::pi_bound`]), so the case is [`PiRef::bare`]'s
    /// alone — a test naming a reference directly. The assertion holds that:
    /// a caller wanting the index wants [`Display`](fmt::Display) (`#0`), which
    /// needs a formatter and so cannot be answered here.
    pub fn base(&self) -> &str {
        match self {
            Name::Raw(s) => s,
            Name::Unique { base, .. } => base,
            Name::Synthetic { kind, .. } => kind.stem(),
            Name::Reserved(r) => r.spelling(),
            Name::PiBound(r) => {
                debug_assert!(
                    r.hint.is_some(),
                    "a hint-less PiBound has no base spelling: `#` would read as a name and \
                     drops the index — render it through Display instead",
                );
                r.hint.as_deref().unwrap_or("#")
            }
        }
    }

    /// A globally-distinct string key for this name, suitable as a **mutable variable
    /// record field label** for a [`crate::ccl::TypedExprNode::Transact`] key.
    /// Unlike [`base`](Self::base) it folds the `uid` in, so two distinct
    /// binders sharing a spelling (e.g. accumulators in sibling loops) get
    /// distinct keys. A variable read of a mutable variable key projects this field of
    /// the mutable variable record (`__reg.field_key`).
    pub fn field_key(&self) -> String {
        match self {
            Name::Raw(s) => s.clone(),
            Name::Unique { base, uid } => format!("{base}#{}", uid.0),
            Name::Synthetic { kind, uid } => format!("{}#{}", kind.stem(), uid.0),
            Name::Reserved(r) => r.spelling().to_string(),
            // Not a binder, so no mutable variable is ever declared at one and
            // no record field is ever labeled by one.
            Name::PiBound(_) => {
                unreachable!("a PiBound is a reference, not a binder; it labels no field")
            }
        }
    }

    /// Is this a raw (un-uniquified) lowering name? The "still needs minting"
    /// sentinel uniquification keys on.
    pub fn is_raw(&self) -> bool {
        matches!(self, Name::Raw(_))
    }

    /// Is this the reserved refinement element binder?
    pub fn is_elem(&self) -> bool {
        matches!(self, Name::Reserved(ReservedName::Elem))
    }

    /// A reference to the enclosing function `index` crossings out, spelled by
    /// `binder` — what [`crate::ccl::subst::close_pi_binder`] mints when it
    /// abstracts `binder`.
    pub fn pi_bound(index: u32, binder: &Name) -> Self {
        Name::PiBound(PiRef {
            index,
            hint: Some(binder.base().into()),
        })
    }

    /// [`pi_bound`](Self::pi_bound) with no spelling — for a site holding no
    /// binder to read one off. Equal to any `PiBound` at the same index.
    pub fn pi_bound_bare(index: u32) -> Self {
        Name::PiBound(PiRef::bare(index))
    }

    /// The de Bruijn index if this is a [`Name::PiBound`] reference.
    pub fn pi_bound_index(&self) -> Option<u32> {
        match self {
            Name::PiBound(r) => Some(r.index),
            _ => None,
        }
    }

    /// Is this the tupled binder lambda elimination mints ([`SyntheticKind::Pair`])?
    /// Used to assert that this `Uid::fresh()`-minted binder never survives into
    /// an equality-compared predicate *term* (see [`crate::ccl::planning`]).
    pub fn is_synthetic_pair(&self) -> bool {
        matches!(
            self,
            Name::Synthetic {
                kind: SyntheticKind::Pair,
                ..
            }
        )
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Self {
        Name::raw(s)
    }
}

impl From<String> for Name {
    fn from(s: String) -> Self {
        Name::raw(s)
    }
}

impl From<&String> for Name {
    fn from(s: &String) -> Self {
        Name::raw(s.clone())
    }
}

impl From<&Name> for Name {
    fn from(n: &Name) -> Self {
        n.clone()
    }
}

/// Prints the bare base (see module docs); the `uid` surfaces only through
/// [`Debug`]. A [`Name::PiBound`] prints the binder's spelling when it carries
/// one and its index (`#0`) when it does not — the one variant whose display
/// needs a formatter.
impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::PiBound(PiRef { index, hint: None }) => write!(f, "#{index}"),
            _ => f.write_str(self.base()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_names_compare_by_string() {
        assert_eq!(Name::raw("x"), Name::raw("x"));
        assert_ne!(Name::raw("x"), Name::raw("y"));
    }

    #[test]
    fn unique_names_are_distinct_despite_shared_base() {
        let a = Name::fresh("x");
        let b = Name::fresh("x");
        assert_ne!(a, b);
        assert_ne!(a, Name::raw("x")); // a Unique is never a Raw
        assert_eq!(a, a.clone()); // copies preserve identity
    }

    #[test]
    fn reserved_is_one_shared_name() {
        assert_eq!(Name::elem(), Name::elem());
        assert!(Name::elem().is_elem());
        assert!(!Name::raw("y").is_elem());
        // A Raw spelled like the reserved name is still a different variant
        // (and only reachable in release; debug_assert guards construction).
        assert_ne!(Name::elem(), Name::Raw("__elem".to_string()));
    }

    #[test]
    fn synthetics_are_uid_identity_with_a_kind_stem() {
        // Each mint is its own binder; the stem is the whole (ambiguous)
        // display, the uid disambiguates.
        assert_ne!(Name::pair(), Name::pair());
        let p = Name::pair();
        assert_eq!(p, p.clone()); // copies preserve identity
        assert_eq!(Name::pair().base(), "__pair");
        assert_eq!(Name::mono(Name::raw("f")).base(), "__mono");
        // The `kind` carries the source binding it specializes (provenance).
        assert!(matches!(
            Name::mono(Name::raw("f")),
            Name::Synthetic {
                kind: SyntheticKind::Mono(src),
                ..
            } if *src == Name::raw("f")
        ));
        assert_eq!(Name::floated().base(), "__floated");
        assert_eq!(Name::solver_arg().base(), "__arg");
        // Different kinds never collide even if uids ever coincided.
        assert!(matches!(
            Name::solver_arg(),
            Name::Synthetic {
                kind: SyntheticKind::SolverArg,
                ..
            }
        ));
        // A source binder spelled like a stem is a different variant.
        assert_ne!(Name::solver_arg(), Name::fresh("__arg"));
    }

    #[test]
    fn display_prints_base_debug_surfaces_uid() {
        assert_eq!(Name::fresh("acc").to_string(), "acc");
        assert_eq!(Name::elem().to_string(), "__elem");
        assert_eq!(Name::pair().to_string(), "__pair");
        // Debug (derived) keeps the variant and the uid visible for diagnostics.
        assert_eq!(format!("{:?}", Name::raw("x")), "Raw(\"x\")");
        assert!(format!("{:?}", Name::fresh("x")).contains("uid"));
    }
}

//! Traits: what a polymorphic operator requires of its operands, and what that
//! determines about its result.
//!
//! # Vocabulary
//!
//! - A **trait** is a named requirement a type may satisfy — `Addable`, `Orderable`.
//!   It is **not a type**: nothing here adds a [`Type`] variant, a lattice point or a
//!   subtyping edge, and the type grammar and `constrain_go`'s rules are untouched.
//! - An **implementation** ([`TraitImpl`]) is one row of a trait's table: the types it
//!   accepts, and the types it associates with them.
//! - An **associated type** ([`Assoc`]) is a type a trait *names* — `Output`, the type
//!   an arithmetic operator's result takes. A trait is a requirement rather than a
//!   function, so it associates any number, **including none**. A type is associated
//!   only when it *depends* on the types satisfying the trait: a comparison's `Bool` is
//!   the same for every pair `Equatable` accepts, so it belongs to the operator's
//!   signature (`OperatorResult::Fixed`, in `src/ccl/infer/schemes.rs`) and
//!   `Equatable` associates nothing.
//! - An **obligation** ([`TraitObligation`]) is one recorded instance of a trait at
//!   specific type positions: one **operand position** per argument the trait takes,
//!   and one **associated position** per type it names. It is a single claim with two
//!   halves, and neither alone is "the obligation": *the operand positions are types
//!   some implementation accepts*, **and** *each associated position is what that
//!   implementation associates*. Every position is an ordinary inference variable,
//!   unrelated to the others. (`Addable(𝐴, 𝐵)` with `Output` at `𝑂` is the shape to
//!   picture, but the arity and the association count are both the trait's.)
//! - A **watch** is an obligation's attachment to an operand variable, which is how a
//!   bound landing anywhere in the program reaches it.
//!
//! An operator's signature is therefore `𝐴₁ → … → 𝐴ₙ → 𝑅` plus the obligation, for the
//! trait's arity `𝑛`, where `𝑅` is either one of the associated positions or a type
//! the operator fixes — which operator states which is `schemes.rs`'s business, not
//! this module's. Because an associated position is an
//! ordinary variable rather than a marker standing for a computation, information
//! flows *backwards* through an operator's result like any other type — which is what
//! lets a function be typechecked without consulting its call sites.
//!
//! # Refinements are transparent
//!
//! `{𝑇 | 𝑝}` satisfies a trait exactly when `𝑇` does, by construction rather than by
//! a stripping step: satisfaction is judged on each bound contribution as it arrives,
//! with refinements peeled at that moment — when the base actually exists.
//!
//! # Discharge is incremental
//!
//! An obligation is a monotone fact discharged as the graph fills in, the shape
//! [`FunKindVar`](crate::ccl::ty::FunKindVar) already uses for kinds; no phase runs
//! "once everything is known". Each operand position carries a **candidate set** of
//! implementations that only ever shrinks ([`TraitObligation::narrow`]), and each
//! associated type is deposited on its position as an ordinary lower bound as soon as
//! every surviving candidate agrees on it ([`TraitObligation::try_deposit`]).
//!
//! # What an obligation determines, and what it leaves alone
//!
//! The deposit rule is *whatever every surviving implementation agrees on*, and it is
//! applied to the **associated positions only**. Nothing is ever deposited onto an
//! operand.
//!
//! The asymmetry is not soundness — with one candidate left, its operand types are
//! implied exactly as its associated types are. It is that the obligation is an
//! associated position's **only** source of information and never an operand's: an
//! associated position is a fresh variable nothing else constrains from below, while
//! an operand always has the program's own `operandᵢ <: 𝐴ᵢ` edge. Determining an operand from the table would be recovering
//! information the program was supposed to supply, which hides an under-connected
//! lowering instead of fixing it.
//!
//! How much gets determined is therefore a property of the table, and shrinks as the
//! table grows — **for an associated type too**. Today `λ 𝑥 → 𝑥 + 1` has result `Int`,
//! because `Int` in the second position leaves only `(Int, Int) ⇝ Int`. Adding
//! `Addable(Float, Int) ⇝ Float` would leave two candidates whose outputs disagree,
//! and the result would become as open as the parameter already is. That is the type
//! honestly tracking a language that has become more permissive, and it is why the
//! deposit waits for *agreement* rather than firing on a unique candidate.

use std::cell::{Cell, RefCell};
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::ccl::{BaseType, InferVar, Type};

use super::constrain::{ConstrainCache, ConstrainError, constrain_subtype};

/// A trait: a named requirement on types, together with any types it associates
/// with them.
///
/// Closed and built-in. The set is the operators the language has, not a user
/// vocabulary — but the implementations are already *data* ([`Trait::impls`]), so a
/// user-declared trait is a table extension rather than a new mechanism.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Trait {
    /// `+` over `(𝐴, 𝐵)`, associating `Output`. The `(String, String) ⇝ String` row is
    /// why surface `+` on strings types through arithmetic; `simplify` rewrites it to
    /// `Concat` later.
    Addable,
    /// `-` over `(𝐴, 𝐵)`, associating `Output`.
    Subtractable,
    /// `*` over `(𝐴, 𝐵)`, associating `Output`.
    Multipliable,
    /// `//` over `(𝐴, 𝐵)`, associating `Output`.
    Divisible,
    /// `==` and `!=` over `(𝐴, 𝐵)`, associating **nothing** — the `Bool` is the
    /// operator's, identical for every pair the trait accepts.
    Equatable,
    /// `<`, `<=`, `>`, `>=` over `(𝐴, 𝐵)`, associating **nothing**, as [`Equatable`].
    ///
    /// [`Equatable`]: Trait::Equatable
    Orderable,
    /// Unary `-` over `(𝐴)`, associating `Output`.
    Negatable,
    /// `max`'s codomain, over `(𝐴)`, associating **nothing** — a pure requirement,
    /// since the aggregate's scheme already returns an element of what it consumes.
    Comparable,
}

/// A type a trait associates with the types satisfying it — Rust's *associated
/// type*.
///
/// A trait is a requirement, not a function, so an associated type is something it
/// happens to name rather than something it must produce. A trait may associate any
/// number, **including none**: a bare requirement (`Orderable(γ)` on an aggregate's
/// codomain) associates nothing, and saying so is better than manufacturing an
/// output no one reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Assoc {
    /// The type an operator's result takes.
    Output,
}

/// One implementation: the types it accepts, and what it associates with them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitImpl {
    /// The accepted types, positionally. A slice rather than a fixed array because
    /// arity is the trait's business — every operator trait is binary today, and an
    /// `Orderable` over one type is the obvious next one.
    pub args: &'static [BaseType],
    /// The types this implementation associates, by name. Empty for a trait that is
    /// a pure requirement.
    pub assoc: &'static [(Assoc, BaseType)],
}

impl TraitImpl {
    /// The type this implementation associates with `name`, if any.
    pub fn assoc_ty(&self, name: Assoc) -> Option<&BaseType> {
        self.assoc.iter().find(|(n, _)| *n == name).map(|(_, t)| t)
    }
}

/// `(Int, Int) ⇝ Int` and `(UInt, UInt) ⇝ UInt` — the numeric arithmetic rows every
/// arithmetic trait shares.
const NUMERIC: &[TraitImpl] = &[
    TraitImpl {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[(Assoc::Output, BaseType::Int)],
    },
    TraitImpl {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[(Assoc::Output, BaseType::UInt)],
    },
];

/// The numeric rows plus `(String, String) ⇝ String`.
const NUMERIC_OR_STRING: &[TraitImpl] = &[
    TraitImpl {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[(Assoc::Output, BaseType::Int)],
    },
    TraitImpl {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[(Assoc::Output, BaseType::UInt)],
    },
    TraitImpl {
        args: &[BaseType::String, BaseType::String],
        assoc: &[(Assoc::Output, BaseType::String)],
    },
];

/// Homogeneous comparison over every base the interpreter can compare.
///
/// **Associates nothing.** A comparison's `Bool` is fixed by the *operator's*
/// signature, not computed by the trait: it is the same `Bool` for every pair of
/// types the trait accepts, so it carries no information about them. Recording it as
/// an associated type would state that the trait determines something it does not —
/// the same mistake as an operator inheriting an operand's refinement, one level up.
const COMPARABLE: &[TraitImpl] = &[
    TraitImpl {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[],
    },
    TraitImpl {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[],
    },
    TraitImpl {
        args: &[BaseType::String, BaseType::String],
        assoc: &[],
    },
    TraitImpl {
        args: &[BaseType::Bool, BaseType::Bool],
        assoc: &[],
    },
];

/// Unary negation. One operand, and an `Output` that genuinely depends on it — the
/// arity and association shape `Addable` and `Equatable` between them do not have.
const NEGATABLE: &[TraitImpl] = &[TraitImpl {
    args: &[BaseType::Int],
    assoc: &[(Assoc::Output, BaseType::Int)],
}];

/// The bases an aggregate can order, matching `max`'s merge in `ccl/mod.rs`. Unary
/// and associating nothing — the fourth shape, and a pure requirement.
const ORDERED: &[TraitImpl] = &[
    TraitImpl {
        args: &[BaseType::Int],
        assoc: &[],
    },
    TraitImpl {
        args: &[BaseType::UInt],
        assoc: &[],
    },
    TraitImpl {
        args: &[BaseType::String],
        assoc: &[],
    },
];

impl Trait {
    /// This trait's implementations.
    ///
    /// Every table is **homogeneous** — both operand positions accept the same base
    /// — which is a fact about today's rows, not about the mechanism: nothing in
    /// narrowing or deposit assumes it. The tables mirror
    /// `interpreter::binop::apply_binop_column`, so a program this accepts is one
    /// the interpreter can actually run. In particular there is no `Unit` row (the
    /// interpreter cannot compare units) and no cross-base row, since `Int` and
    /// `UInt` are unrelated leaves in the lattice and never join.
    pub fn impls(self) -> &'static [TraitImpl] {
        match self {
            Trait::Addable => NUMERIC_OR_STRING,
            Trait::Subtractable | Trait::Multipliable | Trait::Divisible => NUMERIC,
            Trait::Equatable | Trait::Orderable => COMPARABLE,
            Trait::Negatable => NEGATABLE,
            Trait::Comparable => ORDERED,
        }
    }

    /// How many types this trait is over.
    ///
    /// Derived from the table rather than declared beside it, so the shape each
    /// variant's doc states cannot drift from the rows that implement it —
    /// `every_trait_has_a_consistent_shape` pins that every row agrees.
    pub fn arity(self) -> usize {
        self.rows_agree_on().0
    }

    /// The types this trait associates, by name. Empty for a pure requirement.
    pub fn assocs(self) -> Vec<Assoc> {
        self.rows_agree_on().1
    }

    /// The `(arity, associated names)` its first row declares.
    fn rows_agree_on(self) -> (usize, Vec<Assoc>) {
        let first = self
            .impls()
            .first()
            .expect("every trait has at least one implementation");
        (
            first.args.len(),
            first.assoc.iter().map(|(n, _)| *n).collect(),
        )
    }

    /// The trait's name, for diagnostics.
    pub fn name(self) -> &'static str {
        match self {
            Trait::Addable => "Addable",
            Trait::Subtractable => "Subtractable",
            Trait::Multipliable => "Multipliable",
            Trait::Divisible => "Divisible",
            Trait::Equatable => "Equatable",
            Trait::Orderable => "Orderable",
            Trait::Negatable => "Negatable",
            Trait::Comparable => "Comparable",
        }
    }
}

impl fmt::Display for Trait {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Stable identity of a [`TraitObligation`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TraitObligationId(pub(crate) u32);

static OBLIGATION_COUNTER: AtomicU32 = AtomicU32::new(0);

/// One recorded instance of a trait at specific type positions, carrying both halves
/// of the claim: that the operand positions are types some implementation accepts, and
/// that each associated position is what that implementation associates. Arity and
/// association count are the trait's — `Addable(𝐴, 𝐵)` with `Output` at `𝑂` is one
/// shape, `Negatable(𝐴)` with `Output` and `Equatable(𝐴, 𝐵)` with none are the others.
/// See this module's *Vocabulary*.
///
/// Held by [`Rc`] and *watched* by each operand variable ([`TraitObligation::watch`]),
/// so a bound arriving anywhere in the program reaches it without any pass having to
/// go looking for obligations.
///
/// The operand *types* are deliberately not stored: narrowing is push-based — the
/// contribution arrives at the watch — so holding them would buy nothing and only
/// add `Rc` edges for the arena to sever.
pub struct TraitObligation {
    /// Stable, globally-unique identity. Freshening clones an obligation once per
    /// instantiation and keys the copy on this.
    pub uid: TraitObligationId,
    /// The trait being required.
    pub trait_: Trait,
    /// The implementations still consistent with everything seen so far.
    /// Monotonically shrinking; empty is unrepresentable (it is the error).
    candidates: RefCell<Vec<TraitImpl>>,
    /// The type positions this obligation associates, one per name the trait
    /// declares. Empty for a trait that is a pure requirement — the mechanism then
    /// still narrows and still rejects, it simply determines nothing.
    assoc: Vec<AssocPosition>,
}

/// One associated position of an obligation: the name, the type standing in for it,
/// and whether that type has been settled yet.
struct AssocPosition {
    name: Assoc,
    /// A `RefCell` because freshening rewrites it to the instantiation's own variable
    /// after the clone exists — the obligation graph is cyclic (obligation → position
    /// → variable → watches → obligation), so the clone has to be reachable before
    /// its positions can be built.
    ty: RefCell<Type>,
    /// Set before constraining, so a re-entrant narrow cannot deposit twice.
    deposited: Cell<bool>,
}

impl TraitObligation {
    /// Record an instance of `trait_` whose associated names stand at the given type
    /// positions, with every implementation still a candidate.
    pub fn new(trait_: Trait, assoc: Vec<(Assoc, Type)>) -> Rc<TraitObligation> {
        Rc::new(TraitObligation {
            uid: TraitObligationId(OBLIGATION_COUNTER.fetch_add(1, Ordering::Relaxed)),
            trait_,
            candidates: RefCell::new(trait_.impls().to_vec()),
            assoc: assoc
                .into_iter()
                .map(|(name, ty)| AssocPosition {
                    name,
                    ty: RefCell::new(ty),
                    deposited: Cell::new(false),
                })
                .collect(),
        })
    }

    /// A per-instantiation copy of `original`, for freshening.
    ///
    /// The candidate set is copied **as narrowed**, not reset to the full table: it
    /// records what the *definition* already determined (`λ 𝑥 → 𝑥 + 1` has ruled out
    /// every row whose second operand is not `Int`), which every instantiation
    /// inherits. Narrowing past that point is what differs per use, and that is
    /// exactly what the copy makes independent.
    ///
    /// The associated positions are deliberately left pointing at the original's; the
    /// caller rewrites them once the copy is reachable (see
    /// [`set_assoc_types`](Self::set_assoc_types)). Their deposited flags copy too — a
    /// deposit already made rides the freshened bound onto the copy, so redoing it
    /// would record the same fact twice.
    pub(super) fn new_from(original: &Rc<TraitObligation>) -> Rc<TraitObligation> {
        Rc::new(TraitObligation {
            uid: TraitObligationId(OBLIGATION_COUNTER.fetch_add(1, Ordering::Relaxed)),
            trait_: original.trait_,
            candidates: RefCell::new(original.candidates()),
            assoc: original
                .assoc
                .iter()
                .map(|p| AssocPosition {
                    name: p.name,
                    ty: RefCell::new(p.ty.borrow().clone()),
                    deposited: Cell::new(p.deposited.get()),
                })
                .collect(),
        })
    }

    /// Watch `ty` at operand position `pos`, so every lower bound landing there
    /// narrows this obligation.
    ///
    /// `ty` must be an inference variable: an operator's rule mints one per operand
    /// precisely so the operand's *own* type flows in as a bound rather than being
    /// read at emission, when it is not yet known.
    pub fn watch(self: &Rc<Self>, ty: &Type, pos: u8) {
        let Type::Infer(v) = ty else {
            debug_assert!(
                false,
                "a trait obligation watches an inference variable, not {ty:?} — an \
                 operator's rule mints a fresh variable per operand",
            );
            return;
        };
        v.watches.borrow_mut().push((Rc::clone(self), pos));
        #[cfg(debug_assertions)]
        register_watch(self, pos, ty);
    }

    /// The candidates still live, for diagnostics and tests.
    pub fn candidates(&self) -> Vec<TraitImpl> {
        self.candidates.borrow().clone()
    }

    /// The type standing at each associated position, in declaration order.
    /// Freshening reads these, rewrites them, and writes them back with
    /// [`set_assoc_types`](Self::set_assoc_types).
    pub(super) fn assoc_types(&self) -> Vec<Type> {
        self.assoc.iter().map(|p| p.ty.borrow().clone()).collect()
    }

    /// Rewrite the associated positions. Freshening's second phase; see
    /// [`AssocPosition::ty`].
    pub(super) fn set_assoc_types(&self, tys: Vec<Type>) {
        debug_assert_eq!(
            tys.len(),
            self.assoc.len(),
            "an obligation's associated positions are fixed at construction",
        );
        for (position, ty) in self.assoc.iter().zip(tys) {
            *position.ty.borrow_mut() = ty;
        }
    }

    /// Reject a shape no implementation can accept at position `pos`.
    ///
    /// Distinct from [`narrow`](Self::narrow) failing: nothing is *ruled out* here,
    /// because there was never a candidate to rule out. The contribution is simply
    /// outside the vocabulary the trait is defined over.
    fn reject(self: &Rc<Self>, pos: u8, found: &Type) -> Result<(), ConstrainError> {
        Err(ConstrainError::NoTraitImpl {
            trait_: self.trait_,
            position: pos,
            found: found.clone(),
            accepted: self
                .candidates
                .borrow()
                .iter()
                .filter_map(|i| i.args.get(pos as usize).cloned())
                .collect(),
        })
    }

    /// Restrict position `pos` to implementations accepting `base`, then deposit the
    /// output if that settles it.
    ///
    /// Monotone and idempotent: narrowing by a base already consistent with every
    /// candidate is a no-op, which is what makes double delivery (the same fact
    /// reaching a variable and its extrusion proxy) harmless.
    fn narrow(
        self: &Rc<Self>,
        pos: u8,
        base: &BaseType,
        cache: &mut ConstrainCache,
    ) -> Result<(), ConstrainError> {
        {
            let mut candidates = self.candidates.borrow_mut();
            let accepted: Vec<BaseType> = candidates
                .iter()
                .filter_map(|i| i.args.get(pos as usize).cloned())
                .collect();
            // A candidate with no such position is one this trait's arity does not
            // reach; it cannot accept the contribution, so it drops out too.
            candidates.retain(|i| i.args.get(pos as usize) == Some(base));
            if candidates.is_empty() {
                return Err(ConstrainError::NoTraitImpl {
                    trait_: self.trait_,
                    position: pos,
                    found: Type::Base(base.clone()),
                    accepted,
                });
            }
        }
        self.try_deposit(cache)
    }

    /// Deposit the output type on `𝑂` if every surviving candidate agrees on it.
    ///
    /// An ordinary `constrain_subtype`, run **inline**: narrowing *reads nothing* off
    /// the bound graph — it consumes exactly the contribution being recorded — so
    /// there is no stale-read hazard and no reason to defer the write to a later
    /// phase. The [`Cell`] is set before constraining, so a re-entrant narrow reached
    /// through this very edge cannot deposit twice.
    pub fn try_deposit(self: &Rc<Self>, cache: &mut ConstrainCache) -> Result<(), ConstrainError> {
        for position in &self.assoc {
            if position.deposited.get() {
                continue;
            }
            let Some(settled) = self.agreed_assoc(position.name) else {
                continue;
            };
            position.deposited.set(true);
            let target = position.ty.borrow().clone();
            constrain_subtype(&Type::Base(settled), &target, cache)?;
        }
        Ok(())
    }

    /// The type every surviving implementation associates with `name`, or `None` if
    /// they disagree — the condition a deposit waits on.
    fn agreed_assoc(&self, name: Assoc) -> Option<BaseType> {
        let candidates = self.candidates.borrow();
        let (first, rest) = candidates
            .split_first()
            .expect("a candidate set is never empty: emptying it is the error");
        let settled = first.assoc_ty(name)?;
        rest.iter()
            .all(|i| i.assoc_ty(name) == Some(settled))
            .then(|| settled.clone())
    }
}

// Identity-based, mirroring `InferVar`/`FunKindVar`: borrow-free, so it never
// inspects the (mutable, potentially borrowed) candidate set.
impl PartialEq for TraitObligation {
    fn eq(&self, other: &Self) -> bool {
        self.uid == other.uid
    }
}
impl Eq for TraitObligation {}
impl std::hash::Hash for TraitObligation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.uid.hash(state);
    }
}
impl fmt::Debug for TraitObligation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}#{}", self.trait_, self.uid.0)
    }
}

#[cfg(debug_assertions)]
thread_local! {
    /// Every watch established during this inference run, as `(obligation, position,
    /// operand type)` — the audit trail [`verify_narrowing_is_complete`] checks.
    ///
    /// Debug-only, and deliberately *not* a field on [`TraitObligation`]: narrowing
    /// is push-based, so production code never needs an operand's type, and keeping
    /// it out of the obligation means the release build carries neither the `Rc`
    /// edges nor the temptation to read a type where a bound should have been
    /// delivered.
    static WATCH_LOG: RefCell<Vec<(Rc<TraitObligation>, u8, Type)>> =
        const { RefCell::new(Vec::new()) };
}

#[cfg(debug_assertions)]
fn register_watch(obligation: &Rc<TraitObligation>, pos: u8, ty: &Type) {
    WATCH_LOG.with(|log| {
        log.borrow_mut()
            .push((Rc::clone(obligation), pos, ty.clone()))
    });
}

/// Discard the audit trail. Called when an inference run begins, so one run's
/// obligations are never checked against another's graph.
#[cfg(debug_assertions)]
pub fn clear_watch_log() {
    WATCH_LOG.with(|log| log.borrow_mut().clear());
}

/// Check that eager narrowing saw everything the finished graph knows — the
/// invariant the whole mechanism rests on: **every concrete type reaching an operand
/// variable reaches its obligation**.
///
/// A variable's lower bounds are written in exactly four places, and delivery is
/// wired into every one: `constrain_go`'s two variable arms (`notify_lower` for a
/// concrete contribution, `link_watches` for a var-var edge), `extrude`'s proxy
/// seeding (`copy_watches`), and `freshen_above`'s clone (`freshen_watches`). Each is
/// load-bearing — `a_concrete_operand_reaches_its_obligation` has a case per
/// mechanism, confirmed by deleting the mechanism and watching only its case fail.
///
/// That the list is closed is an argument about today's code, not a property the
/// compiler enforces, and a missed delivery is quiet: an obligation that never
/// narrows leaves its output unresolved, which reads as an ordinary under-determined
/// program and can surface phases later, on an interior node, as a wall complaining
/// about a variable with no obvious connection to an operator.
///
/// So the argument is checked rather than trusted. After emission, every watched
/// operand is resolved against the completed graph, and a resolved base must already
/// have narrowed its obligation. A fifth writer added later surfaces here, on
/// whichever program exercises it, naming the operand and the stale candidate set.
///
/// `resolve` is passed in because resolution lives above this module; it must be a
/// *read* of the graph (`compact` → `simplify` → `coalesce`), never something that
/// records a bound, or the check would perturb what it is checking.
#[cfg(debug_assertions)]
pub fn verify_narrowing_is_complete(resolve: impl Fn(&Type) -> Option<Type>) {
    WATCH_LOG.with(|log| {
        for (obligation, pos, operand) in log.borrow().iter() {
            let Some(resolved) = resolve(operand) else {
                // A position the program left conflicting: coalesce reports it, and
                // there is no single base narrowing could have been offered.
                continue;
            };
            let Some(base) = offered_base(&resolved) else {
                // Not a base leaf, so nothing was owed to the obligation.
                continue;
            };
            let candidates = obligation.candidates();
            debug_assert!(
                candidates.iter().all(|i| i.args[*pos as usize] == *base),
                "trait narrowing missed a bound: operand {pos} of {obligation:?} \
                 resolves to {base:?}, but its candidate set still holds {candidates:?} \
                 — some path wrote this variable's lower bounds without delivering to \
                 its watches (see `verify_narrowing_is_complete`)",
            );
        }
    });
}

/// What a bound contribution tells a trait about the position it landed on.
///
/// The distinction between the last two variants is the whole point. Both narrow
/// nothing, but for opposite reasons: one is a position the program has not
/// determined *yet*, and one is a shape no implementation can *ever* accept.
/// Treating them alike is what let `(1, 2) == (3, 4)` type-check — a tuple narrows
/// nothing, and a trait with no associated type has nothing left unresolved for a
/// later wall to catch, so the program passed.
pub enum Offered<'a> {
    /// A base leaf, with refinements peeled — the fact narrowing consumes.
    Base(&'a BaseType),
    /// Nothing known here yet: an inference variable, a hole, or a transient handle
    /// whose payload arrives separately (a `Feed`; a `Mut` is dereferenced before the
    /// variable arms, so it never reaches a watch).
    Unknown,
    /// A concrete shape that is not a base and never will be. No implementation
    /// accepts it, so the requirement fails here rather than silently going
    /// undischarged.
    NotABase,
}

/// What `ty` offers a trait.
///
/// Refinements are peeled here and nowhere else, which is the whole of "a refinement
/// does not affect a trait": the fact is read off the base, at the moment the base
/// arrives.
pub fn offered(ty: &Type) -> Offered<'_> {
    let mut cur = ty;
    while let Type::Refinement(inner, _) = cur {
        cur = inner;
    }
    match cur {
        Type::Base(b) => Offered::Base(b),
        // Products, sums and functions are fully determined and are not bases. A
        // collection compared or added is the same mistake as a tuple.
        Type::Tuple(_) | Type::Record(_) | Type::Variant(_) | Type::Fun { .. } => Offered::NotABase,
        // Everything else is either a variable, a placeholder, or a carrier whose
        // payload reaches the watch by another route.
        _ => Offered::Unknown,
    }
}

/// The base `ty` offers, if any — for callers that only need the narrowing fact.
pub fn offered_base(ty: &Type) -> Option<&BaseType> {
    match offered(ty) {
        Offered::Base(b) => Some(b),
        _ => None,
    }
}

/// Propagate `upper`'s obligations down to `lower` when the edge `lower <: upper` is
/// recorded, and deliver what `lower` already knows.
///
/// A concrete type does **not** reliably reach a watched variable through the bound
/// closure alone, and the exception is the common case rather than a corner. When
/// `lower` and `upper` sit at different polymorphism levels — which is exactly what a
/// `let` RHS produces, since it is emitted one level deeper — the edge is recorded by
/// the arm whose closure runs against the *other* side's bounds, so a concrete type
/// already sitting on `lower` is never re-offered to `upper`, and one arriving later
/// closes against uppers that do not include it. The graph is still correct; it is
/// only *transitively* readable, which is a thing coalesce does and constraint
/// emission does not.
///
/// So the watch follows the edge, in the direction information flows: down, to the
/// variables feeding the watched one. This is [`FunKindVar::link`]'s move
/// (`crate::ccl::ty`) — a kind force propagates along stored links for the same
/// reason, and for kinds it is the only mechanism because a force is a flag rather
/// than a bound.
///
/// Recursion is bounded by the watch set only ever growing: a variable that gains
/// nothing new stops the walk, which is what makes this safe on the cyclic bound
/// graph a recurrence produces.
pub(super) fn link_watches(
    lower: &Rc<InferVar>,
    upper: &Rc<InferVar>,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    let incoming = {
        let watches = upper.watches.borrow();
        if watches.is_empty() {
            return Ok(());
        }
        watches.clone()
    };
    let added: Vec<(Rc<TraitObligation>, u8)> = {
        let mut watches = lower.watches.borrow_mut();
        incoming
            .into_iter()
            .filter(|(ob, pos)| {
                let fresh = !watches.iter().any(|(o, p)| o.uid == ob.uid && p == pos);
                if fresh {
                    watches.push((Rc::clone(ob), *pos));
                }
                fresh
            })
            .collect()
    };
    if added.is_empty() {
        return Ok(());
    }

    // Whatever `lower` already carries is information the obligation has not been
    // offered — it arrived before the edge existed.
    let (known, below) = {
        let bounds = lower.bounds.borrow();
        let known: Vec<BaseType> = bounds
            .lower
            .iter()
            .filter_map(|b| offered_base(&b.ty).cloned())
            .collect();
        let below: Vec<Rc<InferVar>> = bounds
            .lower
            .iter()
            .filter_map(|b| match &b.ty {
                Type::Infer(v) => Some(Rc::clone(v)),
                _ => None,
            })
            .collect();
        (known, below)
    };
    for (obligation, pos) in &added {
        for base in &known {
            obligation.narrow(*pos, base, cache)?;
        }
    }
    // Transitivity: anything flowing into `lower` flows into `upper` too.
    for v in below {
        link_watches(&v, lower, cache)?;
    }
    Ok(())
}

/// Deliver a lower bound to every obligation watching `var`.
///
/// Called from `constrain_go`'s lower-bound arm, with the contribution exactly as it
/// was recorded. The two side substitutions are deliberately **not** applied: a
/// substitution rewrites refinement-predicate interiors and Pi binder names, never
/// the structural skeleton, so the base leaf this reads is invariant under every
/// morphism the solver can compose. Materializing the bound into the holder's frame
/// would cost a walk and change nothing.
pub(super) fn notify_lower(
    var: &Rc<InferVar>,
    contribution: &Type,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    // Snapshot: a deposit re-enters `constrain_go`, which can append watches.
    let watches = {
        let watches = var.watches.borrow();
        if watches.is_empty() {
            return Ok(());
        }
        watches.clone()
    };
    match offered(contribution) {
        Offered::Base(base) => {
            for (obligation, pos) in watches {
                obligation.narrow(pos, base, cache)?;
            }
        }
        Offered::NotABase => {
            for (obligation, pos) in watches {
                obligation.reject(pos, contribution)?;
            }
        }
        Offered::Unknown => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::infer::solver::fresh_var;

    /// Both narrowing orders reach the same answer — the property that lets the
    /// obligation be discharged incrementally instead of by a final sweep.
    #[rstest::rstest]
    #[case(&[(0, BaseType::Int), (1, BaseType::Int)])]
    #[case(&[(1, BaseType::Int), (0, BaseType::Int)])]
    fn narrowing_is_order_independent(#[case] steps: &[(u8, BaseType)]) {
        let out = fresh_var(0);
        let ob = TraitObligation::new(Trait::Addable, vec![(Assoc::Output, out.clone())]);
        let mut cache = ConstrainCache::new();

        for (pos, base) in steps {
            ob.narrow(*pos, base, &mut cache)
                .expect("Int + Int is addable");
        }

        assert_eq!(ob.candidates().len(), 1);
        let Type::Infer(v) = &out else { unreachable!() };
        assert!(
            v.bounds
                .borrow()
                .lower
                .iter()
                .any(|b| b.ty == Type::Base(BaseType::Int)),
            "the settled output type is deposited as a lower bound on O",
        );
    }

    /// One known operand is enough to settle the output when every remaining
    /// implementation agrees on it — without concluding anything about the *other*
    /// operand, which stays open for a future heterogeneous implementation.
    #[test]
    fn one_known_operand_settles_an_agreed_output() {
        let out = fresh_var(0);
        let ob = TraitObligation::new(Trait::Addable, vec![(Assoc::Output, out.clone())]);
        let mut cache = ConstrainCache::new();

        ob.narrow(1, &BaseType::Int, &mut cache)
            .expect("Int is addable");

        assert_eq!(
            ob.agreed_assoc(Assoc::Output),
            Some(BaseType::Int),
            "(Int, Int) ⇝ Int is the only row left, so its Output is settled",
        );
        assert_eq!(
            ob.candidates(),
            vec![TraitImpl {
                args: &[BaseType::Int, BaseType::Int],
                assoc: &[(Assoc::Output, BaseType::Int)],
            }]
        );
    }

    /// A comparison associates **nothing**: its `Bool` is the operator's, not the
    /// trait's, so there is no position for the obligation to settle and the whole
    /// claim is the requirement on its operands.
    ///
    /// This is the shape that made associated types a *set* rather than one
    /// distinguished output — and it is exercised by every comparison in the suite,
    /// not just here.
    #[test]
    fn a_comparison_associates_nothing() {
        let ob = TraitObligation::new(Trait::Equatable, Vec::new());
        let mut cache = ConstrainCache::new();

        ob.try_deposit(&mut cache).expect("nothing to deposit");
        assert_eq!(ob.agreed_assoc(Assoc::Output), None);

        // The requirement half is untouched.
        ob.narrow(0, &BaseType::Int, &mut cache)
            .expect("Int is equatable");
        assert!(
            ob.narrow(1, &BaseType::String, &mut cache).is_err(),
            "nothing equates an Int to a String",
        );
    }

    /// Operands that no implementation accepts together are rejected, and the error
    /// says what the position could still have taken.
    #[test]
    fn incompatible_operands_have_no_implementation() {
        let out = fresh_var(0);
        let ob = TraitObligation::new(Trait::Orderable, vec![(Assoc::Output, out)]);
        let mut cache = ConstrainCache::new();

        ob.narrow(0, &BaseType::Int, &mut cache)
            .expect("Int is orderable");
        let err = ob
            .narrow(1, &BaseType::String, &mut cache)
            .expect_err("nothing compares an Int to a String");

        let ConstrainError::NoTraitImpl {
            trait_,
            position,
            found,
            accepted,
        } = err
        else {
            panic!("expected NoTraitImpl, got {err:?}");
        };
        assert_eq!(trait_, Trait::Orderable);
        assert_eq!(position, 1);
        assert_eq!(found, Type::Base(BaseType::String));
        assert_eq!(accepted, vec![BaseType::Int]);
    }

    /// Every implementation of a trait agrees on its **shape** — how many types it is
    /// over, and which types it associates.
    ///
    /// [`Trait::arity`] and [`Trait::assocs`] read that shape off the first row, and
    /// each variant's doc states it in prose. This is what keeps the three from
    /// drifting apart: a row added with the wrong arity, or associating a name its
    /// siblings do not, fails here rather than silently making `arity()` a lie.
    #[test]
    fn every_trait_has_a_consistent_shape() {
        for trait_ in [
            Trait::Addable,
            Trait::Subtractable,
            Trait::Multipliable,
            Trait::Divisible,
            Trait::Equatable,
            Trait::Orderable,
            Trait::Negatable,
            Trait::Comparable,
        ] {
            let (arity, assocs) = (trait_.arity(), trait_.assocs());
            for row in trait_.impls() {
                assert_eq!(
                    row.args.len(),
                    arity,
                    "{trait_} has rows of differing arity: {row:?}",
                );
                let names: Vec<Assoc> = row.assoc.iter().map(|(n, _)| *n).collect();
                assert_eq!(
                    names, assocs,
                    "{trait_} has rows associating different names: {row:?}",
                );
            }
        }
    }

    /// A refinement is transparent: `{Int | __elem == 1}` narrows exactly as `Int`
    /// does. This is the property the emit-time strip could not deliver, because at
    /// emission an operand is usually still a variable with nothing to strip.
    #[test]
    fn a_refinement_narrows_as_its_base() {
        let refined = Type::Refinement(
            Box::new(Type::Base(BaseType::String)),
            crate::ccl::Refinement::born(Rc::new(crate::ccl::TypedExpr::lit(
                crate::ccl::Lit::Bool(true),
            ))),
        );
        assert_eq!(offered_base(&refined), Some(&BaseType::String));
    }

    /// A shape the table has no row for offers nothing rather than failing — see
    /// [`offered_base`].
    #[test]
    fn a_non_base_shape_offers_nothing() {
        assert_eq!(offered_base(&Type::UIntRange(3)), None);
        assert_eq!(offered_base(&Type::Txn), None);
        assert_eq!(offered_base(&fresh_var(0)), None);
    }
}

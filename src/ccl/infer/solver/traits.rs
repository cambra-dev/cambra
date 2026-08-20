//! Traits: what a polymorphic operator requires of its operands, and what that
//! determines about its result.
//!
//! # Vocabulary
//!
//! - A **trait** ([`Trait`]) is a named requirement a *list* of types may satisfy —
//!   `Addable`, `Orderable`. It is **not a type**: nothing here adds a [`Type`]
//!   variant, a lattice point or a subtyping edge, and the type grammar and
//!   `constrain_go`'s rules are untouched.
//! - An **instance** ([`TraitInstance`]) is one row of a trait's table: the types it
//!   accepts, and the types it associates with them — written
//!   `Addable(Int, Int ⇝ Int)`, accepted types then `⇝` then associated ones.
//! - An **associated type** ([`Assoc`]) is a type a trait *names* — `Output`, the type
//!   an arithmetic operator's result takes. A trait associates any number, **including
//!   none**: only a type that *depends* on the types satisfying the trait belongs here,
//!   so `Equatable` associates nothing and its `Bool` rides the operator's signature
//!   instead (`OperatorResult::Fixed`, in `src/ccl/infer/schemes.rs`).
//! - An **obligation** ([`TraitObligation`]) is what one *use* of a trait records: the
//!   demand that some instance fit the type positions at that use — one **operand
//!   position** per argument the trait takes, and one **associated position** per type
//!   it names. `Addable(𝐴, 𝐵 ⇝ 𝑂)` is the shape to picture, though the arity and the
//!   association count are both the trait's. It is a single claim with two halves, and
//!   neither alone is "the obligation": *the operand positions are types some instance
//!   accepts*, **and** *each associated position is what that instance associates*.
//!   Every position is an ordinary inference variable, unrelated to the others.
//! - A **watch** is an obligation's attachment to an operand variable
//!   ([`TraitObligation::watch`]), which is how a bound landing anywhere in the program
//!   reaches it.
//!
//! Every position being an ordinary inference variable — not a marker standing for an
//! unreduced computation — is what lets information flow *backwards* out of an
//! operator's result, and so what lets a function be typechecked without consulting its
//! call sites.
//!
//! # Resolution is incremental
//!
//! An obligation is a monotone fact resolved as the graph fills in, the shape
//! [`FunKindVar`](crate::ccl::ty::FunKindVar) already uses for kinds; no phase runs
//! "once everything is known". Each operand position carries a **candidate set** of
//! instances that only ever shrinks ([`TraitObligation::narrow`]), and each
//! associated type is deposited on its position once every surviving candidate *agrees*
//! on it ([`TraitObligation::try_deposit`]) — agreement, not a lone survivor.
//!
//! Delivery only ever offers one contribution at a time, so it cannot see two
//! requirements that are individually satisfiable and jointly are not.
//! [`resolve_operand_requirements`] is the pass that reads a value's requirements
//! together: an empty intersection is rejected, and a singleton is deposited as an
//! **upper** bound on the operand — the polarity is what keeps that a restatement of
//! the requirement rather than an invented value.
//!
//! Its unit is a [`Place`] — one value, however many variables stand at it — rather
//! than a variable, because a multi-parameter lambda passes its parameters through a
//! tuple and so splits one value's occurrences across several variables. Currying a
//! program must not change what it means.
//!
//! A refinement narrows exactly as its base does: `{𝑇 | 𝑝}` satisfies a trait when `𝑇`
//! does, because satisfaction is judged on each bound contribution as it arrives and
//! peels refinements at that moment — when the base actually exists.
//!
//! # Where to read more
//!
//! `src/ccl/design/type-inference.md`, "Traits" is the design of record, and carries
//! the arguments this module only acts on: why the constraint lattice cannot state an
//! operator's requirement on its own, why the two deposit polarities are not the same
//! move, why the requirement sweep sits between emission and coalesce and runs to a
//! fixpoint, why refinement transparency is permanent rather than a convenience, what
//! the tables hold and what that does *not* say about resolution, and what a trait
//! would relate beyond types — associated *functions*, which the shape here allows and
//! does not yet have. Which operators state which requirement, and which take a fixed
//! result rather than an associated one, is `schemes.rs`'s business, not this module's.

use std::cell::{Cell, RefCell};
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::ccl::{BaseType, FieldKey, InferVar, InferVarId, Type};

use super::constrain::{ConstrainCache, ConstrainError, constrain_subtype};

/// A trait: a named requirement on types, together with any types it associates
/// with them.
///
/// Closed and built-in. The set is the operators the language has, not a user
/// vocabulary — but the instances are already *data* ([`Trait::instances`]), so a
/// user-declared trait is a table extension rather than a new mechanism.
/// `Ord` so a diagnostic can order the requirements it lists. Resolution does not
/// depend on it: a candidate set is a set, and the verdict is an intersection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

/// One instance: the types it accepts, and what it associates with them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitInstance {
    /// The accepted types, positionally. A slice rather than a fixed array because
    /// arity is the trait's business — every operator trait is binary today, and an
    /// `Orderable` over one type is the obvious next one.
    pub args: &'static [BaseType],
    /// The types this instance associates, by name. Empty for a trait that is
    /// a pure requirement.
    pub assoc: &'static [(Assoc, BaseType)],
}

impl TraitInstance {
    /// The type this instance associates with `name`, if any.
    pub fn assoc_ty(&self, name: Assoc) -> Option<&BaseType> {
        self.assoc.iter().find(|(n, _)| *n == name).map(|(_, t)| t)
    }
}

/// `(Int, Int) ⇝ Int` and `(UInt, UInt) ⇝ UInt` — the numeric arithmetic rows every
/// arithmetic trait shares.
const NUMERIC: &[TraitInstance] = &[
    TraitInstance {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[(Assoc::Output, BaseType::Int)],
    },
    TraitInstance {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[(Assoc::Output, BaseType::UInt)],
    },
];

/// The numeric rows plus `(String, String) ⇝ String`.
const NUMERIC_OR_STRING: &[TraitInstance] = &[
    TraitInstance {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[(Assoc::Output, BaseType::Int)],
    },
    TraitInstance {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[(Assoc::Output, BaseType::UInt)],
    },
    TraitInstance {
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
const COMPARABLE: &[TraitInstance] = &[
    TraitInstance {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[],
    },
    TraitInstance {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[],
    },
    TraitInstance {
        args: &[BaseType::String, BaseType::String],
        assoc: &[],
    },
    TraitInstance {
        args: &[BaseType::Bool, BaseType::Bool],
        assoc: &[],
    },
];

/// Unary negation. One operand, and an `Output` that genuinely depends on it — the
/// arity and association shape `Addable` and `Equatable` between them do not have.
const NEGATABLE: &[TraitInstance] = &[TraitInstance {
    args: &[BaseType::Int],
    assoc: &[(Assoc::Output, BaseType::Int)],
}];

/// The bases an aggregate can order, matching `max`'s merge in `ccl/mod.rs`. Unary
/// and associating nothing — the fourth shape, and a pure requirement.
const ORDERED: &[TraitInstance] = &[
    TraitInstance {
        args: &[BaseType::Int],
        assoc: &[],
    },
    TraitInstance {
        args: &[BaseType::UInt],
        assoc: &[],
    },
    TraitInstance {
        args: &[BaseType::String],
        assoc: &[],
    },
];

impl Trait {
    /// This trait's instances.
    ///
    /// Every table holds base types only, and every row is **homogeneous** — both
    /// operand positions accept the same base. Nothing in narrowing or deposit
    /// assumes either, and both are answerable to
    /// `interpreter::binop::apply_binop_column`, which these tables mirror so that a
    /// program inference accepts is one the interpreter can run: hence no `Unit` row
    /// (it cannot compare units) and no cross-base row (`Int` and `UInt` are
    /// unrelated leaves that never join). What that does and does not say about the
    /// mechanism is `src/ccl/design/type-inference.md`, "What the tables hold".
    pub fn instances(self) -> &'static [TraitInstance] {
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
            .instances()
            .first()
            .expect("every trait has at least one instance");
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

/// What one use of a trait records: the demand that some instance fit the type
/// positions at that use. It carries both halves of the claim — that the operand
/// positions are types some instance accepts, and that each associated position is
/// what that same instance associates. Arity and
/// association count are the trait's — `Addable(𝐴, 𝐵 ⇝ 𝑂)` is one shape,
/// `Negatable(𝐴 ⇝ 𝑂)` and `Equatable(𝐴, 𝐵)` are the others.
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
    /// The instances still consistent with everything seen so far.
    /// Monotonically shrinking; empty is unrepresentable (it is the error).
    candidates: RefCell<Vec<TraitInstance>>,
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
    /// positions, with every instance still a candidate.
    pub fn new(trait_: Trait, assoc: Vec<(Assoc, Type)>) -> Rc<TraitObligation> {
        Rc::new(TraitObligation {
            uid: TraitObligationId(OBLIGATION_COUNTER.fetch_add(1, Ordering::Relaxed)),
            trait_,
            candidates: RefCell::new(trait_.instances().to_vec()),
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
    pub fn candidates(&self) -> Vec<TraitInstance> {
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

    /// Reject a shape no instance can accept at position `pos`.
    ///
    /// Distinct from [`narrow`](Self::narrow) failing: nothing is *ruled out* here,
    /// because there was never a candidate to rule out. The contribution is simply
    /// outside the vocabulary the trait is defined over.
    fn reject(self: &Rc<Self>, pos: u8, found: &Type) -> Result<(), ConstrainError> {
        Err(ConstrainError::NoTraitInstance {
            trait_: self.trait_,
            position: pos,
            found: found.clone(),
            accepted: self.accepted_at(pos),
        })
    }

    /// The trait's operand positions *other* than `pos`, with what each still accepts.
    ///
    /// Arity is read off a surviving row rather than stored: every row of a trait has
    /// a type at every position that trait declares, which is the same invariant
    /// [`accepted_at`](Self::accepted_at) rests on.
    fn siblings_of(&self, pos: u8) -> Vec<(u8, Vec<BaseType>)> {
        let arity = self.candidates.borrow().first().map_or(0, |i| i.args.len());
        (0..arity as u8)
            .filter(|i| *i != pos)
            .map(|i| (i, self.accepted_at(i)))
            .collect()
    }

    /// Restrict position `pos` to instances accepting `base`, then deposit the
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
        // Read before the mutable borrow: "what this position could have accepted" is
        // only meaningful before the contribution rules rows out.
        let accepted = self.accepted_at(pos);
        {
            let mut candidates = self.candidates.borrow_mut();
            #[cfg(debug_assertions)]
            let before = candidates.len();
            // A candidate with no such position is one this trait's arity does not
            // reach; it cannot accept the contribution, so it drops out too.
            candidates.retain(|i| i.args.get(pos as usize) == Some(base));
            // Re-delivery of a fact already recorded is the common case and changes
            // nothing; only an actual shrink can move the verdict this obligation
            // contributes, so only a shrink is worth policing.
            #[cfg(debug_assertions)]
            if candidates.len() < before {
                assert_post_emission_narrowing_selects(self, pos, base, &accepted);
            }
            if candidates.is_empty() {
                return Err(ConstrainError::NoTraitInstance {
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

    /// The types the surviving instances still accept at operand position `pos`.
    ///
    /// The operand-side reading of [`agreed_assoc`](Self::agreed_assoc), and
    /// deliberately a *set* rather than an `Option`: an associated position is
    /// deposited only once the candidates agree, because depositing a guess would
    /// constrain a live program. Nothing here is deposited — the caller is choosing
    /// a type for an operand no bound will ever reach, so what it needs is the
    /// choices, not a verdict that there is exactly one.
    ///
    /// Order follows the instance table, so a caller that picks positionally picks
    /// reproducibly.
    ///
    /// Never empty for a position the trait's arity reaches: a candidate set is
    /// non-empty by invariant (emptying it is the error), and every instance of a
    /// trait carries a type at every position that trait declares.
    pub fn accepted_at(&self, pos: u8) -> Vec<BaseType> {
        self.candidates
            .borrow()
            .iter()
            .filter_map(|i| i.args.get(pos as usize).cloned())
            .collect()
    }

    /// The type every surviving instance associates with `name`, or `None` if
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

#[cfg(debug_assertions)]
thread_local! {
    /// The obligation-counter high-water mark at the moment the requirement sweep
    /// finished, or `None` before it runs.
    ///
    /// [`resolve_operand_requirements`] reads candidate sets as final. They are, *for
    /// the obligations that matter*: a generalized definition's subtree is never
    /// coalesced in place, so its variables take no new bounds afterwards, and the
    /// narrowing that does continue during coalesce acts on the per-instantiation
    /// clones `freshen_watches` mints — obligations that did not exist when the sweep
    /// ran, and the one pass that does narrow an emission-era obligation afterwards only
    /// ever *selects* from a set the sweep read. The mark is what makes that checkable
    /// rather than merely argued: see [`assert_post_emission_narrowing_selects`].
    static EMISSION_MARK: Cell<Option<u32>> = const { Cell::new(None) };
}

/// Open the narrowing window, discarding any previous run's mark.
///
/// Called from [`InferArena::new`](crate::ccl::infer::InferArena::new), which is the
/// construct whose lifetime this state shares: the mark is per-run for the same reason
/// the variable capture is. Resetting it is not optional bookkeeping. The mark is a
/// high-water mark of a *process-global* counter, so a stale one left by an earlier run
/// on this thread sits below every obligation the current run mints, and
/// [`assert_post_emission_narrowing_selects`] would pass vacuously instead of being inert —
/// checking nothing, and silently, which is the failure mode it exists to prevent.
#[cfg(debug_assertions)]
pub fn unseal_emission() {
    EMISSION_MARK.with(|m| m.set(None));
}

/// Close it, recording which obligations existed at that point.
///
/// Asserts the window was open, so the pairing with [`unseal_emission`] is checked
/// rather than remembered: a run that reached here without opening one is a run whose
/// mark belongs to a different run.
#[cfg(debug_assertions)]
pub fn seal_emission() {
    EMISSION_MARK.with(|m| {
        debug_assert!(
            m.get().is_none(),
            "sealing a window that was never opened — this run inherited mark {:?} from \
             an earlier run on this thread, so `unseal_emission` did not run at arena \
             entry",
            m.get(),
        );
        m.set(Some(OBLIGATION_COUNTER.load(Ordering::Relaxed)));
    });
}

/// After emission, a narrowing may only **select**: an obligation minted during
/// emission may still be narrowed, but only by delivering a base its position already
/// accepted.
///
/// This is the timing assumption [`resolve_operand_requirements`] rests on, and it
/// fails silently. The sweep's verdict is joint non-emptiness of the accepted sets it
/// reads at end of emission, so a later write that **restricts** a position past what
/// the sweep saw leaves that verdict stale. A write that picks a base from inside the
/// swept set records a choice the sweep already licensed, and re-running the sweep
/// reaches the same verdict.
///
/// One pass narrows after emission and it is of the second kind:
/// `pin_unobservable_arm_payload` (`src/ccl/infer/solve.rs`) types an unreachable arm's
/// payload. No value reaches that position, so its type comes from a demand recorded on
/// it or from the arm body's own reads, and both are sets this sweep read.
///
/// An obligation minted since the mark is unconstrained: a freshened clone is a
/// per-instantiation copy the sweep never read, and one that goes unsatisfiable fails
/// by delivery.
///
/// **The sibling positions are not re-read.** Delivering to one position tightens what
/// this obligation's other positions accept (`Addable` narrowed to `Int` at position 0
/// accepts only `Int` at 1), and nothing compares that against the requirements a
/// variable standing there carries. What bounds the exposure is what a pin can deliver
/// — see `src/ccl/design/type-inference.md`, "Requirements are read together, once".
#[cfg(debug_assertions)]
fn assert_post_emission_narrowing_selects(
    obligation: &Rc<TraitObligation>,
    pos: u8,
    base: &BaseType,
    accepted: &[BaseType],
) {
    EMISSION_MARK.with(|m| {
        let Some(mark) = m.get() else {
            return;
        };
        debug_assert!(
            obligation.uid.0 >= mark || accepted.contains(base),
            "{obligation:?} was minted during emission, and narrowing it at position \
             {pos} to `{base}` restricts a set `resolve_operand_requirements` already \
             read as final ({accepted:?} did not accept it), so the sweep's verdict is \
             now stale. Either the check has to move later, or this write belongs in \
             emission.",
        );
    });
}

/// One requirement a single operand carries: which trait asked, at which of its
/// positions, and what that position can still accept.
///
/// Several on one variable is the ordinary case — `𝑥 + 1 > 2` requires `Addable` and
/// `Orderable` of `𝑥` — and they compose exactly when some type satisfies them all.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OperandRequirement {
    /// The trait that placed the requirement.
    pub trait_: Trait,
    /// Which of its operand positions this variable stands at.
    pub position: u8,
    /// The bases still accepted there.
    pub accepted: Vec<BaseType>,
    /// The trait's *other* operand positions and what each still accepts.
    ///
    /// A requirement on its own reads as an unexplained demand — "only `Int` here" is
    /// a consequence, not a premise. What narrowed the position is the type that
    /// reached the operand beside it, so carrying the siblings lets a diagnostic say
    /// where the demand came from without any provenance being recorded: they are read
    /// off the same candidate set. Empty for a unary trait, which has no beside.
    pub siblings: Vec<(u8, Vec<BaseType>)>,
}

/// Find an operand no type can satisfy: two or more requirements on one variable
/// whose accepted sets have nothing in common.
///
/// **The one check narrowing cannot make.** Narrowing is push-based, so an obligation
/// learns only what is *delivered*, and in `λ 𝑎 → (𝑎 + 1, 𝑎 + "s")` each of the two
/// obligations was narrowed through its **other** operand — one to `{Int}`, the other
/// to `{String}`. Neither set is empty, so neither failed; nothing compared them, and
/// the definition type-checked despite being ill-typed for every possible argument.
/// Delivery cannot close this, because the hole *is* the case where no type arrives.
///
/// So the requirements are read together — the move coalesce makes on a variable's
/// bounds, applied to its obligations. `vars` is every variable minted during the run,
/// which is the only enumeration that reaches a definition: a generalized definition's
/// subtree is deliberately never coalesced in place, so walking the tree would see
/// only use-site clones, and a clone that goes unsatisfiable already fails by delivery.
///
/// Returns the offending variable alongside its requirements; the caller supplies
/// blame, because node identity belongs to the tree and not to the solver.
pub fn resolve_operand_requirements(cache: &mut ConstrainCache) -> Result<(), OperandFailure> {
    // A deposit is an ordinary `constrain_subtype`, so it can deliver a base to another
    // variable's watches and shrink *their* candidate sets — which can determine a
    // value that was open when this pass looked at it. So the sweep runs to a fixpoint
    // rather than once. It terminates because candidate sets only shrink and the base
    // vocabulary is finite; `deposited` is what makes "nothing new happened" cheap to
    // decide, since re-depositing a bound the graph already carries is not progress.
    let mut deposited: std::collections::HashSet<(InferVarId, BaseType)> =
        std::collections::HashSet::new();
    loop {
        let before = deposited.len();
        // Re-read the arena every pass rather than snapshotting once. Every variable
        // being a root is what makes the sweep complete — it is why a function's domain
        // needs no traversal of its own — and a deposit is an ordinary
        // `constrain_subtype`, which is entitled to mint variables (an extrusion proxy,
        // which `copy_watches` gives the original's requirements). Measured, the arena
        // does not currently grow here; re-reading makes that irrelevant instead of
        // load-bearing.
        resolve_pass(&crate::ccl::infer_var::arena_vars(), cache, &mut deposited)?;
        if deposited.len() == before {
            return Ok(());
        }
    }
}

/// One step into a value: how a sub-place is reached from the place above it.
///
/// Distinguished rather than collapsed onto [`FieldKey`] because a record field and a
/// variant arm of the same name are different positions, and a function's result is
/// neither. Merging any two of them would intersect requirements that constrain
/// different values, which is how a sweep like this produces a *false* rejection.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Step {
    /// A tuple position or a record field.
    Field(FieldKey),
    /// A variant arm's payload.
    Arm(FieldKey),
    /// A function's result. Its *domain* is deliberately not a step — see
    /// [`places_under`].
    Result,
    /// A history's value (the cell or element a `Mut`/`Feed` handle carries).
    HistoryValue,
}

/// The descent that reaches one place from the root of a sweep: the path of [`Step`]s
/// taken, empty at the root itself.
///
/// Only ever a **key**, and only within one [`places_under`] call — two roots' paths
/// name unrelated values and are never compared. Nothing reads it back; it exists so
/// that variables reached by different routes land in the same bucket iff they stand
/// for the same value.
type StepPath = Vec<Step>;

/// A **place**: one value, as the set of variables standing at it and every requirement
/// landing on them.
///
/// The unit a requirement actually constrains, and the reason it is not the variable:
/// `λ 𝑎 𝑏 → …` uncurries to a lambda over a tuple and rewrites each occurrence of
/// `𝑎` to a projection of it, so each occurrence has its own variable and none carries
/// both of `𝑎`'s requirements, even though both constrain one value. Curried, `𝑎` is a
/// binder its occurrences share and one variable carries both — so a place holds
/// however many variables the spelling happens to split the value across, and the
/// intersection is taken over the whole set.
#[derive(Default)]
struct Place {
    vars: Vec<Rc<InferVar>>,
    reqs: Vec<(Rc<TraitObligation>, u8)>,
}

/// Strip every refinement layer, as [`offered`] does: `{𝑇 | 𝑝}` constrains a place
/// exactly as `𝑇` does, so structure underneath a refinement is still structure.
fn peel_refinements(ty: &Type) -> &Type {
    let mut cur = ty;
    while let Type::Refinement(inner, _) = cur {
        cur = inner;
    }
    cur
}

/// Group everything reachable from `root` into the [`Place`] it constrains, keyed by
/// the [`StepPath`] that reaches it.
///
/// Follows **upper** bounds, because `𝑣 <: 𝑈` means `𝑣`'s value reaches `𝑈` and so a
/// requirement on `𝑈` is a requirement on `𝑣`. A variable upper bound stays at the
/// same place; a *structural* one descends — `𝑣 <: (𝑈₀, 𝑈₁)` says `𝑣`'s component 0
/// reaches `𝑈₀`, so `𝑈₀`'s requirements belong to the place one field deeper, never to
/// `𝑣` itself.
///
/// Why this reads the graph once at the end rather than reusing `link_watches`, and
/// why the grouping is what licenses each step, are in
/// `src/ccl/design/type-inference.md`, "The unit is a place, not a variable". The arms
/// below carry the per-former reason; the design doc does not repeat them.
///
/// The match on a bound's type is **exhaustive on purpose**. What the sweep reaches is
/// what "every requirement is read" means, so a new [`Type`] variant that can hold a
/// type has to fail this build and be classified deliberately — a wildcard arm would
/// let the grammar grow while the sweep quietly stopped covering it, and nothing would
/// fail. Peeling refinements at every step is the same concern one level down: matching
/// a bound's type directly would let a refined structural bound fall through to the
/// leaf arm, and the walk would stop at a place it should have descended past.
///
/// `seen` is keyed on the *pair*, so a variable revisited at a different place is
/// revisited — which is correct, and which means a cycle through a **structural** upper
/// bound (`𝑣 <: (𝑢)`, `𝑢 <: (𝑣)`) would lengthen the path forever rather than being
/// absorbed. A variable cycle is fine: the path does not grow, so `seen` closes it.
/// Nothing builds the structural kind today — source-level recursion does not reach
/// inference (a self-call is an unbound variable) and `LetRec` is born after it — so
/// this is a precondition to re-check when recursive definitions arrive, not a live
/// hazard.
fn places_under(root: &Rc<InferVar>) -> std::collections::BTreeMap<StepPath, Place> {
    let mut out: std::collections::BTreeMap<StepPath, Place> = Default::default();
    let mut seen: std::collections::HashSet<(InferVarId, StepPath)> = Default::default();
    let mut frontier = vec![(Rc::clone(root), StepPath::new())];
    while let Some((var, path)) = frontier.pop() {
        if !seen.insert((var.uid, path.clone())) {
            continue;
        }
        let entry = out.entry(path.clone()).or_default();
        entry.vars.push(Rc::clone(&var));
        for (obligation, pos) in var.watches.borrow().iter() {
            if !entry
                .reqs
                .iter()
                .any(|(o, p)| o.uid == obligation.uid && p == pos)
            {
                entry.reqs.push((Rc::clone(obligation), *pos));
            }
        }
        for bound in var.bounds.borrow().upper().iter() {
            // Refinements are peeled at every step, for the same reason `offered` peels
            // them: `{𝑇 | 𝑝}` constrains a place exactly as `𝑇` does, so a refined
            // bound must not hide the structure underneath it.
            match peel_refinements(&bound.ty) {
                Type::Infer(up) => frontier.push((Rc::clone(up), path.clone())),
                Type::Tuple(elems) => {
                    for (i, elem) in elems.iter().enumerate() {
                        descend(elem, &path, Step::Field(FieldKey::Index(i)), &mut frontier);
                    }
                }
                Type::Record(fields) => {
                    for (name, ty) in fields {
                        let key = FieldKey::Name(name.as_str().into());
                        descend(ty, &path, Step::Field(key), &mut frontier);
                    }
                }
                Type::Variant(arms, _) => {
                    for (tag, payload) in arms {
                        descend(payload, &path, Step::Arm(tag.clone()), &mut frontier);
                    }
                }
                // The result only. Two codomains consume one value and group; two
                // domains are two arguments and must not — the argument is in
                // `src/ccl/design/type-inference.md`, "The unit is a place, not a
                // variable".
                //
                // Measured, so the exclusion is not read as a known counterexample:
                // descending into the domain as well changes no test outcome. Two
                // incompatible sources for one monomorphic domain are already an
                // `IncompatibleBounds`, and a polymorphic one freshens per use. It stays
                // out because grouping distinct values is unlicensed, not because a
                // program distinguishes the two traversals.
                Type::Fun {
                    domain: _,
                    codomain,
                    ..
                } => descend(codomain, &path, Step::Result, &mut frontier),
                // The value a mutable variable or channel carries is a component of it in the
                // same sense a field is; the domain beside it is an index, not a value
                // this place holds.
                Type::History { value, .. } => {
                    descend(value, &path, Step::HistoryValue, &mut frontier)
                }
                // Leaves: nothing inside to constrain. `Base`/`UIntRange` are concrete,
                // and the rest are placeholders or nullary carriers.
                Type::Base(_)
                | Type::UIntRange(_)
                | Type::Hole
                | Type::SharedHole(_)
                | Type::DataSource(_)
                | Type::ChanDom(_, _)
                | Type::Txn => {}
                // `peel_refinements` returns a non-refinement by construction.
                Type::Refinement(_, _) => unreachable!("refinements are peeled above"),
                // `BoundedHole` is a *pre-inference* annotation marker:
                // `normalize_annotation` erases it into a bounded variable before any
                // constraint is emitted, so it is never a recorded bound.
                Type::BoundedHole(_) => unreachable!(
                    "Type::BoundedHole reached the solver; `normalize_annotation` must erase it"
                ),
            }
        }
    }
    out
}

/// A concrete base already on `var` that `required` contradicts, if there is one.
///
/// Both directions are read, and neither is redundant. A **lower** bound is a value
/// that already reaches the variable — an exact annotation, a literal — and it must be
/// *below* `required`, which for two distinct bases it is not. An **upper** bound is
/// another ceiling — a monomorphic operator's operand, a bounded annotation — and two
/// distinct base ceilings have no common value under them. Either way the requirement
/// cannot be satisfied, and one of the two is what the lattice would have reported.
///
/// Bases only. A structural bound is a different mistake (a tuple where a trait wants a
/// base) and belongs to `Offered::NotABase`, which narrowing already rejects on arrival.
fn conflicting_base(var: &Rc<InferVar>, required: &BaseType) -> Option<BaseType> {
    let bounds = var.bounds.borrow();
    bounds
        .lower()
        .iter()
        .chain(bounds.upper().iter())
        .filter_map(|b| offered_base(&b.ty))
        .find(|base| *base != required)
        .cloned()
}

/// Queue `ty` one `step` below `path`, if it is a variable once refinements are peeled.
fn descend(ty: &Type, path: &StepPath, step: Step, frontier: &mut Vec<(Rc<InferVar>, StepPath)>) {
    if let Type::Infer(up) = peel_refinements(ty) {
        let mut deeper = path.clone();
        deeper.push(step);
        frontier.push((Rc::clone(up), deeper));
    }
}

fn resolve_pass(
    vars: &[Rc<InferVar>],
    cache: &mut ConstrainCache,
    deposited: &mut std::collections::HashSet<(InferVarId, BaseType)>,
) -> Result<(), OperandFailure> {
    for root in vars {
        for place in places_under(root).into_values() {
            if place.reqs.is_empty() {
                continue;
            }
            let mut requirements: Vec<OperandRequirement> = place
                .reqs
                .iter()
                .map(|(obligation, pos)| OperandRequirement {
                    trait_: obligation.trait_,
                    position: *pos,
                    accepted: obligation.accepted_at(*pos),
                    siblings: obligation.siblings_of(*pos),
                })
                .collect();
            // Sorted so a diagnostic lists them the same way for programs that differ
            // only in spelling. `place.reqs` is in traversal order, which currying
            // changes; the verdict does not depend on it, and the message should not
            // either.
            requirements.sort();
            debug_assert!(
                requirements.iter().all(|r| !r.accepted.is_empty()),
                "a live obligation accepts something at every position its trait \
                 declares, but {requirements:?} has an empty set — either a candidate \
                 set was emptied without raising, or a watch was placed past its \
                 trait's arity",
            );
            // The intersection: bases every requirement at this place accepts.
            // Commutative, so the verdict does not depend on traversal order.
            // Owned rather than borrowed from `requirements`, which the failure arms
            // below move into the diagnostic.
            let common: Vec<BaseType> = requirements[0]
                .accepted
                .iter()
                .filter(|base| requirements[1..].iter().all(|r| r.accepted.contains(base)))
                .cloned()
                .collect();
            match common.as_slice() {
                // Nothing satisfies every requirement, so no argument ever could.
                [] => {
                    // Narrowest first, then the variable the walk reached them from.
                    // An *interior* place is reached only through a bound, and blame
                    // deliberately does not follow bounds, so no node's type can ever
                    // name a variable standing there — without the root as a candidate
                    // the walk finds nothing and lands on the tree root, which is a
                    // different statement entirely rather than a wider one.
                    let blame = place
                        .vars
                        .iter()
                        .map(|v| v.uid)
                        .chain(std::iter::once(root.uid))
                        .collect();
                    return Err(OperandFailure::Unsatisfiable {
                        vars: blame,
                        requirements,
                    });
                }
                // Exactly one base left: the requirements *determine* this value, so say
                // so on the lattice rather than keeping it to ourselves. This is the
                // write-back that makes `λ 𝑥 → 𝑥 + 1` infer `Int ⇒ Int` instead of
                // leaving the parameter open, and it is what lets a requirement collide
                // with an ordinary bound — an annotation, or a monomorphic operator's
                // operand — which comparing requirements against each other cannot do.
                //
                // An **upper** bound, and the polarity is the whole argument for why
                // this is not "recovering information the program should have supplied":
                // it states what may flow in, which is exactly what the requirement
                // says. It adds no lower bound, so a genuinely under-connected value is
                // still under-determined afterwards.
                [only] => {
                    for var in &place.vars {
                        // Read the lattice before writing to it. `constrain_subtype`
                        // *records* a bound rather than checking it against the ones
                        // already there, so a requirement contradicting an annotation or
                        // a monomorphic operator's operand would otherwise surface at
                        // coalesce as a bare `IncompatibleBounds` — twice, once per
                        // direction, and with no mention of the trait that demanded it.
                        // The facts are all here, so the diagnostic is made here.
                        if let Some(found) = conflicting_base(var, only) {
                            return Err(OperandFailure::ContradictsBound {
                                vars: place
                                    .vars
                                    .iter()
                                    .map(|v| v.uid)
                                    .chain(std::iter::once(root.uid))
                                    .collect(),
                                requirements,
                                required: (*only).clone(),
                                found,
                            });
                        }
                        if !deposited.insert((var.uid, (*only).clone())) {
                            continue;
                        }
                        let deposit = Type::Base((*only).clone());
                        constrain_subtype(&Type::Infer(Rc::clone(var)), &deposit, cache)
                            .map_err(|error| OperandFailure::Conflict { error })?;
                    }
                    // The bound alone does not reach the obligations at this place: it
                    // is an *upper* bound and narrowing consumes lower ones. So tell
                    // them directly. This is not new information — the intersection just
                    // proved the place accepts nothing else — but recording it is what
                    // lets the fact travel: pinning `𝑎` to `Int` leaves `Addable(𝑎, 𝑏)`
                    // with one row, which determines `𝑏` next round.
                    for (obligation, pos) in &place.reqs {
                        obligation.narrow(*pos, only, cache).map_err(|error| {
                            debug_assert!(
                                false,
                                "narrowing by a base the intersection just proved \
                                 acceptable emptied {obligation:?} at operand {pos}",
                            );
                            OperandFailure::Conflict { error }
                        })?;
                    }
                }
                // Several bases still satisfy everything: the requirements genuinely do
                // not pin the value, and leaving it open is the honest answer.
                _ => {}
            }
        }
    }
    Ok(())
}

/// Why [`resolve_operand_requirements`] rejected a value.
pub enum OperandFailure {
    /// No type satisfies every requirement on it — ill-typed for every argument.
    ///
    /// Raised for the first such place found, matching emission next door (also
    /// fail-fast, also at most one error). *Whether* a program is rejected does not
    /// depend on order — the intersection is commutative — but *which* place is named,
    /// when a program has several, follows the order variables were minted in.
    Unsatisfiable {
        /// Blame candidates, narrowest first: the variables standing at the offending
        /// place, then the variable the walk reached them from. The caller takes the
        /// first one the expression tree actually mentions.
        ///
        /// The root is on the list because it is the only candidate an *interior* place
        /// has. Such a place is reached through a bound, and blame is structural —
        /// deliberately not following bounds — so no node's type ever names a variable
        /// standing there, and a list of those alone would always come up empty.
        vars: Vec<InferVarId>,
        /// Every requirement landing on that place.
        requirements: Vec<OperandRequirement>,
    },
    /// The requirements determine one base, and the value already carries a different
    /// one — from an annotation, a literal, or a monomorphic operator's operand.
    ///
    /// Distinct from [`Unsatisfiable`](Self::Unsatisfiable): there the requirements
    /// contradict *each other*, and no bound need exist at all. Here each requirement
    /// is satisfiable and they agree with one another; what they agree on is what the
    /// program has already ruled out. Both are "no argument could work", found by
    /// different comparisons, and only this one has a type to point at.
    ContradictsBound {
        /// Blame candidates, as [`Unsatisfiable::vars`](Self::Unsatisfiable).
        vars: Vec<InferVarId>,
        /// The requirements, which together determined `required`.
        requirements: Vec<OperandRequirement>,
        /// The base they determine.
        required: BaseType,
        /// The base already on the value.
        found: BaseType,
    },
    /// The lattice refused the deposit.
    ///
    /// **Not known to be reachable.** `constrain_subtype` *records* a bound rather than
    /// checking it against those already present, so the contradiction this would name
    /// is caught one step earlier, by reading the bounds directly
    /// ([`ContradictsBound`](Self::ContradictsBound)). Kept because the call is
    /// fallible and swallowing its error would be worse than carrying an arm for it.
    Conflict {
        /// Whatever the lattice objected to.
        error: ConstrainError,
    },
}

/// What a bound contribution tells a trait about the position it landed on.
///
/// The distinction between the last two variants is the whole point. Both narrow
/// nothing, but for opposite reasons: one is a position the program has not
/// determined *yet*, and one is determined, at a type no instance accepts.
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
    /// A determined type that is not a base leaf — a tuple, record, variant or
    /// function.
    ///
    /// Every instance is keyed on a base ([`TraitInstance::args`]), so nothing in
    /// any table accepts it and the requirement fails here rather than silently
    /// going unresolved. That the tables hold only bases is their *content*, not a
    /// property of resolution: giving `Equatable` a variant would add rows, and
    /// would split this variant into the shapes a row can key on — it would not
    /// change how narrowing works.
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
        Type::Tuple(_) | Type::Record(_) | Type::Variant(_, _) | Type::Fun { .. } => {
            Offered::NotABase
        }
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
            .lower()
            .iter()
            .filter_map(|b| offered_base(&b.ty).cloned())
            .collect();
        let below: Vec<Rc<InferVar>> = bounds
            .lower()
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
    /// obligation be resolved incrementally instead of by a final sweep.
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
                .lower()
                .iter()
                .any(|b| b.ty == Type::Base(BaseType::Int)),
            "the settled output type is deposited as a lower bound on O",
        );
    }

    /// One known operand is enough to settle the output when every remaining
    /// instance agrees on it — without concluding anything about the *other*
    /// operand, which stays open for a future heterogeneous instance.
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
            vec![TraitInstance {
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

    /// Operands that no instance accepts together are rejected, and the error
    /// says what the position could still have taken.
    #[test]
    fn incompatible_operands_have_no_instance() {
        let out = fresh_var(0);
        let ob = TraitObligation::new(Trait::Orderable, vec![(Assoc::Output, out)]);
        let mut cache = ConstrainCache::new();

        ob.narrow(0, &BaseType::Int, &mut cache)
            .expect("Int is orderable");
        let err = ob
            .narrow(1, &BaseType::String, &mut cache)
            .expect_err("nothing compares an Int to a String");

        let ConstrainError::NoTraitInstance {
            trait_,
            position,
            found,
            accepted,
        } = err
        else {
            panic!("expected NoTraitInstance, got {err:?}");
        };
        assert_eq!(trait_, Trait::Orderable);
        assert_eq!(position, 1);
        assert_eq!(found, Type::Base(BaseType::String));
        assert_eq!(accepted, vec![BaseType::Int]);
    }

    /// Every instance of a trait agrees on its **shape** — how many types it is
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
            for row in trait_.instances() {
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

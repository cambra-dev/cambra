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

use crate::ccl::ty::TraitRequirement;
use std::cell::{Cell, RefCell};
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::ccl::{
    ArithmeticKind, BaseType, BinOpKind, CompareKind, FieldKey, InferVar, InferVarId, Name,
    Refinement, RefinementSet, RefinementTemplate, Type, TypedExpr, provenance,
};

use super::constrain::{ConstrainCache, ConstrainError, constrain_subtype};
use super::prim;

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
    /// `^+` over `(𝐴, 𝐵)`, associating `Output`.
    ///
    /// This is an experimental version of Addable that gives the
    /// output type an input-dependent refinement.
    AddableRefined,
    /// `-` over `(𝐴, 𝐵)`, associating `Output`.
    Subtractable,
    /// `*` over `(𝐴, 𝐵)`, associating `Output`.
    Multipliable,
    /// `//` over `(𝐴, 𝐵)`, associating `Output`.
    Divisible,
    /// `**` over `(𝐴, 𝐵)`, associating `Output`, where `𝐵` is the exponent.
    ///
    /// The rows relate the two *bases*. That the exponent is **non-negative** is stated
    /// where it can be discharged — as a refinement on the exponent's own binding
    /// (`src/ccl/lower/exprs.rs`'s `pow_with_checked_exponent`) — because a row admits a
    /// base and not a predicate over its values. The refinement names `Int`, so the `UInt`
    /// row these share is unreachable for `**` while that holds.
    Exponentiable,
    /// `==` and `!=` over `(𝐴, 𝐵)`, associating **nothing** — the `Bool` is the
    /// operator's, identical for every pair the trait accepts.
    Equatable,
    /// `<`, `<=`, `>`, `>=` over `(𝐴, 𝐵)`, associating **nothing**, as [`Equatable`].
    /// `max` places it on its codomain twice, `(γ, γ)`: a pure requirement, since the
    /// aggregate's scheme already returns an element of what it consumes.
    ///
    /// [`Equatable`]: Trait::Equatable
    Orderable,
    /// Unary `-` over `(𝐴)`, associating `Output`.
    Negatable,
}

/// A type a trait associates with the types satisfying it — Rust's *associated
/// type*.
///
/// A trait is a requirement, not a function, so an associated type is something it
/// happens to name rather than something it must produce. A trait may associate any
/// number, **including none**: a bare requirement (`Orderable(γ, γ)` on an aggregate's
/// codomain) associates nothing, and saying so is better than manufacturing an
/// output no one reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Assoc {
    /// The type an operator's result takes.
    Output,
}

impl Assoc {
    /// The associated type a `requires` clause names by `name`, as in `Output=O`.
    pub fn from_surface_name(name: &str) -> Option<Assoc> {
        match name {
            "Output" => Some(Assoc::Output),
            _ => None,
        }
    }
}

impl fmt::Display for Assoc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Assoc::Output => f.write_str("Output"),
        }
    }
}

/// One instance: the types it accepts, and what it associates with them.
#[derive(Debug, Clone)]
pub struct TraitInstance {
    /// The accepted types, positionally. A slice rather than a fixed array because
    /// arity is the trait's business — every operator trait is binary today, and an
    /// `Orderable` over one type is the obvious next one.
    pub args: &'static [BaseType],
    /// The types this instance associates, by name. Empty for a trait
    /// that is a pure requirement. Each associated type has an
    /// optional RefinementTemplate, which builds a refinement from
    /// operator's input argument expressions.
    pub assoc: &'static [(Assoc, BaseType, Option<RefinementTemplate>)],
}

impl TraitInstance {
    /// The type this instance associates with `name`, if any.
    pub fn assoc_ty(&self, name: Assoc) -> Option<(&BaseType, Option<RefinementTemplate>)> {
        self.assoc
            .iter()
            .find(|(n, _, _)| *n == name)
            .map(|(_, t, r)| (t, *r))
    }
}

/// `(Int, Int) ⇝ Int` and `(UInt, UInt) ⇝ UInt` — the numeric arithmetic rows every
/// arithmetic trait shares.
const NUMERIC: &[TraitInstance] = &[
    TraitInstance {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[(Assoc::Output, BaseType::Int, None)],
    },
    TraitInstance {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[(Assoc::Output, BaseType::UInt, None)],
    },
];

/// The bare predicate `__elem == a1 ^+ a2` for the `AddableRefined(Int, Int ⇝ Int)`
/// row: the result is the sum of the operands the instance accepted.
///
/// Bare in the sense of [`crate::ccl::ccl_utils::refine_with_bare`] — [`Name::elem`] is
/// free, and the refinement it lands in is what binds it. Every node is typed at
/// construction because the row fixes both operand bases and the associated base at
/// `Int`, leaving nothing for inference to resolve, the same reason
/// [`crate::ccl::infer::singleton_predicate`]'s term is ground.
fn refinement_for_add(args: &[TypedExpr]) -> TypedExpr {
    let [a1, a2] = args else {
        panic!("AddableRefined is binary, so its instance's refinement receives two operands");
    };
    let int = prim(BaseType::Int);
    TypedExpr::binop(
        TypedExpr::var(Name::elem()).with_ty(int.clone()),
        BinOpKind::Compare(CompareKind::Equals),
        TypedExpr::binop(
            a1.clone(),
            BinOpKind::Arithmetic(ArithmeticKind::AddRefined),
            a2.clone(),
        )
        .with_ty(int),
    )
    .with_ty(prim(BaseType::Bool))
}

/// `(Int, Int) ⇝ {Int | __elem == 𝑎₁ ^+ 𝑎₂}` — the one row of `^+`.
const ADDITION_REFINED: &[TraitInstance] = &[
    TraitInstance {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[(Assoc::Output, BaseType::Int, Some(refinement_for_add))],
    },
    TraitInstance {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[(Assoc::Output, BaseType::UInt, Some(refinement_for_add))],
    },
];

/// The numeric rows plus `(String, String) ⇝ String`.
const NUMERIC_OR_STRING: &[TraitInstance] = &[
    TraitInstance {
        args: &[BaseType::Int, BaseType::Int],
        assoc: &[(Assoc::Output, BaseType::Int, None)],
    },
    TraitInstance {
        args: &[BaseType::UInt, BaseType::UInt],
        assoc: &[(Assoc::Output, BaseType::UInt, None)],
    },
    TraitInstance {
        args: &[BaseType::String, BaseType::String],
        assoc: &[(Assoc::Output, BaseType::String, None)],
    },
];

/// Homogeneous comparison over every base the interpreter can compare, which is also
/// every base `max` folds (`ccl/aggregate.rs`).
///
/// **Associates nothing.** A comparison's `Bool` is fixed by the *operator's*
/// signature, not computed by the trait: it is the same `Bool` for every pair of
/// types the trait accepts, so it carries no information about them. Recording it as
/// an associated type would state that the trait determines something it does not —
/// the same mistake as an operator inheriting an operand's refinement, one level up.
const COMPARISON: &[TraitInstance] = &[
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
    assoc: &[(Assoc::Output, BaseType::Int, None)],
}];

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
            Trait::AddableRefined => ADDITION_REFINED,
            Trait::Subtractable | Trait::Multipliable | Trait::Divisible | Trait::Exponentiable => {
                NUMERIC
            }
            Trait::Equatable | Trait::Orderable => COMPARISON,
            Trait::Negatable => NEGATABLE,
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
            first.assoc.iter().map(|(n, _, _)| *n).collect(),
        )
    }

    /// Whether a **product** satisfies this trait when its components do.
    ///
    /// Equality only. It is defined componentwise on any product, which is what makes the
    /// decomposition a reading of the trait rather than a new relation. Ordering is not:
    /// comparing two products needs an order on their components, and a record's fields
    /// carry none, so `Orderable` stays what its rows say it is.
    /// Arithmetic has no product reading at all.
    pub fn is_structural(self) -> bool {
        matches!(self, Trait::Equatable)
    }

    /// The trait a `requires` clause names by `name`, or `None` for a name that is no
    /// trait. `AddableRefined` has no surface name (`docs/chl-spec.md`, "Trait
    /// requirements").
    pub fn from_surface_name(name: &str) -> Option<Trait> {
        Some(match name {
            "Addable" => Trait::Addable,
            "Subtractable" => Trait::Subtractable,
            "Multipliable" => Trait::Multipliable,
            "Divisible" => Trait::Divisible,
            "Exponentiable" => Trait::Exponentiable,
            "Equatable" => Trait::Equatable,
            "Orderable" => Trait::Orderable,
            "Negatable" => Trait::Negatable,
            _ => return None,
        })
    }

    /// The trait's name, for diagnostics.
    pub fn name(self) -> &'static str {
        match self {
            Trait::Addable => "Addable",
            Trait::AddableRefined => "AddableRefined",
            Trait::Subtractable => "Subtractable",
            Trait::Multipliable => "Multipliable",
            Trait::Divisible => "Divisible",
            Trait::Exponentiable => "Exponentiable",
            Trait::Equatable => "Equatable",
            Trait::Orderable => "Orderable",
            Trait::Negatable => "Negatable",
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
/// A **base** contribution needs no operand type held: narrowing is push-based, so it
/// arrives at the watch and is consumed there. A **product** does, because answering one
/// means saying what the positions beside it hold, so the type at each position is
/// recorded ([`operands`](TraitObligation::operands)).
pub struct TraitObligation {
    /// Stable, globally-unique identity. Freshening clones an obligation once per
    /// instantiation and keys the copy on this.
    pub uid: TraitObligationId,
    /// The trait being required.
    pub trait_: Trait,
    /// The instances still consistent with everything seen so far.
    /// Monotonically shrinking; empty is unrepresentable (it is the error).
    candidates: RefCell<Vec<TraitInstance>>,
    /// The **assumptions** still consistent with everything seen so far: the
    /// requirements of the `requires` clauses in scope where the obligation was
    /// minted, read as further rows beside [`candidates`](Self::candidates)
    /// (`src/ccl/design/type-parameters.md`, "Obligations under assumptions").
    /// Shrinks as `candidates` does; the obligation fails only when both are empty.
    assumptions: RefCell<Vec<Rc<TraitRequirement>>>,
    /// Every assumption in scope at minting, before any narrowing: what an
    /// obligation this one mints for a product's component starts from
    /// ([`narrow_product`](Self::narrow_product)).
    in_scope: RefCell<Rc<Vec<Rc<TraitRequirement>>>>,
    /// The type standing at each operand position, indexed by position.
    ///
    /// Recorded by [`watch`](Self::watch), which is the one place a position is bound to a
    /// variable — at emission and again per instantiation, so a freshened copy records the
    /// instantiation's own variables as the walk reaches them. Narrowing needs none of this:
    /// a base contribution arrives at the watch and is consumed there. A **product** does,
    /// because the product rule bounds every operand by the product's shape
    /// ([`apply_product_rule`](Self::apply_product_rule)).
    operands: RefCell<Vec<Option<Type>>>,
    /// Where the trait's **product rule** stands: the candidate beside the rows that
    /// answers a tuple or record ([`ProductRule`]).
    ///
    /// Two things read it besides narrowing: a diagnostic, which names the product the
    /// rule was applied at, and the requirement sweep, which has no base intersection to
    /// take once an obligation is answered by the rule.
    product_rule: RefCell<ProductRule>,
    /// The type positions this obligation associates, one per name the trait
    /// declares. Empty for a trait that is a pure requirement — the mechanism then
    /// still narrows and still rejects, it simply determines nothing.
    assoc: Vec<AssocPosition>,
    /// The input arguments' actual expressions, to be substituted
    /// into the output type if it has a refinement template.
    ///
    /// A `RefCell`, as [`AssocPosition::ty`] is: freshening rewrites these to the
    /// instantiation's own variables after the clone exists (see
    /// [`set_input_exprs`](Self::set_input_exprs)).
    input_exprs: RefCell<Vec<TypedExpr>>,
    /// The ID of the operator node that spawned this obligation, to
    /// be used as provenance for any resulting refinement body.
    operator_node_id: provenance::NodeId,
    /// Where the requirement was stated: the operator that needs it, or the
    /// requirement of a `requires` clause it was instantiated from at a use. A failure
    /// to satisfy it labels this position as its demand.
    required_at: crate::ccl::infer_var::Origin,
}

/// The state of an obligation's product rule, the candidate that answers a product
/// contribution (`src/ccl/design/type-inference.md`, "A product is answered off the
/// table").
///
/// The rows accept bases only, so a contribution decides between them and the rule: a
/// base rules the rule out, and a product leaves the rule the one candidate. Only a
/// trait with a product reading has the rule ([`Trait::is_structural`]).
#[derive(Clone, Debug)]
enum ProductRule {
    /// The trait has no product reading.
    Absent,
    /// No contribution has arrived to decide between the rows and the rule.
    Open,
    /// A base arrived, so only the rows can answer.
    RuledOut,
    /// A product arrived, recorded here with its components' refinements peeled, while an
    /// assumption stating that product still answers the obligation. The rule waits: its
    /// conditions would demand that every operand be a product, which an assumption
    /// relating the product to a type parameter does not state
    /// (`src/ccl/design/type-parameters.md`, "Obligations under assumptions").
    Pending(Type),
    /// A product arrived, recorded here with its components' refinements peeled, and the
    /// rule's conditions are minted ([`TraitObligation::apply_product_rule`]).
    Applied(Type),
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
    pub fn new(
        trait_: Trait,
        assoc: Vec<(Assoc, Type)>,
        operator_node_id: provenance::NodeId,
        input_exprs: Vec<TypedExpr>,
        required_at: crate::ccl::infer_var::Origin,
    ) -> Rc<TraitObligation> {
        Rc::new(TraitObligation {
            uid: TraitObligationId(OBLIGATION_COUNTER.fetch_add(1, Ordering::Relaxed)),
            trait_,
            candidates: RefCell::new(trait_.instances().to_vec()),
            assumptions: RefCell::new(Vec::new()),
            in_scope: RefCell::new(Rc::new(Vec::new())),
            operands: RefCell::new(Vec::new()),
            product_rule: RefCell::new(if trait_.is_structural() {
                ProductRule::Open
            } else {
                ProductRule::Absent
            }),
            assoc: assoc
                .into_iter()
                .map(|(name, ty)| AssocPosition {
                    name,
                    ty: RefCell::new(ty),
                    deposited: Cell::new(false),
                })
                .collect(),
            input_exprs: RefCell::new(input_exprs),
            operator_node_id,
            required_at,
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
        // We need a provenance recording here for the cloning of
        // input_exprs into the new obligation.
        let _f = provenance::copy_frame("infer.freshen_obligation");
        Rc::new(TraitObligation {
            uid: TraitObligationId(OBLIGATION_COUNTER.fetch_add(1, Ordering::Relaxed)),
            trait_: original.trait_,
            candidates: RefCell::new(original.candidates()),
            assumptions: RefCell::new(original.assumptions.borrow().clone()),
            in_scope: RefCell::new(Rc::clone(&original.in_scope.borrow())),
            operands: RefCell::new(Vec::new()),
            product_rule: RefCell::new(original.product_rule.borrow().clone()),
            assoc: original
                .assoc
                .iter()
                .map(|p| AssocPosition {
                    name: p.name,
                    ty: RefCell::new(p.ty.borrow().clone()),
                    deposited: Cell::new(p.deposited.get()),
                })
                .collect(),
            input_exprs: RefCell::new(original.input_exprs.borrow().clone()),
            operator_node_id: original.operator_node_id,
            required_at: original.required_at,
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
        {
            let mut operands = self.operands.borrow_mut();
            if operands.len() <= pos as usize {
                operands.resize(pos as usize + 1, None);
            }
            operands[pos as usize] = Some(ty.clone());
        }
        #[cfg(debug_assertions)]
        register_watch(self, pos, ty);
    }

    /// Where this requirement was stated: the operator that needs it, or the
    /// `requires` clause it was instantiated from.
    pub fn required_at(&self) -> crate::ccl::infer_var::Origin {
        self.required_at
    }

    /// The candidates still live, for diagnostics and tests.
    pub fn candidates(&self) -> Vec<TraitInstance> {
        self.candidates.borrow().clone()
    }

    /// Add the assumptions in scope where this obligation was minted, as rows beside
    /// its trait's instances. Only those about this obligation's trait are kept.
    pub fn assume(&self, in_scope: &[Rc<TraitRequirement>]) {
        let rows: Vec<Rc<TraitRequirement>> = in_scope
            .iter()
            .filter(|a| a.trait_ == self.trait_)
            .cloned()
            .collect();
        *self.assumptions.borrow_mut() = rows.clone();
        *self.in_scope.borrow_mut() = Rc::new(rows);
    }

    /// Rewrite every type its assumptions state through `f`: a specialization clone
    /// re-mints the type parameters of the definitions nested in it, and its copy of
    /// an obligation must name the clone's parameters, not the original's.
    pub(crate) fn map_assumptions(&self, mut f: impl FnMut(&Type) -> Type) {
        let mut map = |rows: &[Rc<TraitRequirement>]| -> Vec<Rc<TraitRequirement>> {
            rows.iter().map(|r| Rc::new(r.map_types(&mut f))).collect()
        };
        let assumptions = map(&self.assumptions.borrow());
        let in_scope = map(&self.in_scope.borrow());
        *self.assumptions.borrow_mut() = assumptions;
        *self.in_scope.borrow_mut() = Rc::new(in_scope);
    }

    /// Replace each variable an assumption of a reset copy states with what `resolve`
    /// settles it to, once the pin has tied it to the use's types.
    ///
    /// The variables are a specialized binding's own parameters, which a kept row
    /// ([`reset_for_specialization`](Self::reset_for_specialization)) names beside a
    /// nested definition's. An assumption is matched by equality, so it states a base
    /// rather than a variable standing for one.
    pub(crate) fn settle_assumptions(&self, mut resolve: impl FnMut(&Type) -> Option<Type>) {
        self.map_assumptions(|t| match t {
            Type::Infer(_) => resolve(t).unwrap_or_else(|| t.clone()),
            _ => t.clone(),
        });
    }

    /// Add `more` to the assumptions this obligation is answered by, keeping those
    /// about its trait that it does not hold yet.
    pub(crate) fn assume_more(&self, more: &[Rc<TraitRequirement>]) {
        let mut assumptions = self.assumptions.borrow_mut();
        let mut in_scope = (**self.in_scope.borrow()).clone();
        for a in more.iter().filter(|a| a.trait_ == self.trait_) {
            if !in_scope.contains(a) {
                in_scope.push(Rc::clone(a));
                assumptions.push(Rc::clone(a));
            }
        }
        *self.in_scope.borrow_mut() = Rc::new(in_scope);
    }

    /// Reset a specialization's copy whose rows assume one of the specialized
    /// binding's own type parameters, `own`.
    ///
    /// The copy stands where the parameter is a concrete type, so an assumption
    /// about the parameter alone no longer describes it: the copy goes back to its
    /// trait's instances and the assumptions it still needs, and nothing it had
    /// deposited stands. An assumption that also names another parameter, one of a
    /// definition nested in the clone, is the only row answering that parameter, so it
    /// is kept, its own parameters becoming the clone's variables and then the use's
    /// types ([`settle_assumptions`](Self::settle_assumptions)). Returns whether it was
    /// reset; a reset copy is [redelivered](Self::redeliver) once the clone is pinned
    /// (`src/ccl/design/type-parameters.md`, "Specialization").
    pub(super) fn reset_for_specialization(&self, own: &[crate::ccl::ty::TypeParamId]) -> bool {
        let names_own = |a: &Rc<TraitRequirement>| a.mentions_any(own);
        if !self.assumptions.borrow().iter().any(names_own) {
            return false;
        }
        let only_own = |a: &&Rc<TraitRequirement>| names_own(a) && !a.mentions_other_than(own);
        *self.candidates.borrow_mut() = self.trait_.instances().to_vec();
        *self.product_rule.borrow_mut() = if self.trait_.is_structural() {
            ProductRule::Open
        } else {
            ProductRule::Absent
        };
        let kept: Vec<Rc<TraitRequirement>> = self
            .in_scope
            .borrow()
            .iter()
            .filter(|a| !only_own(a))
            .cloned()
            .collect();
        *self.assumptions.borrow_mut() = kept.clone();
        *self.in_scope.borrow_mut() = Rc::new(kept);
        for position in &self.assoc {
            position.deposited.set(false);
        }
        true
    }

    /// Offer this obligation everything its operand variables already carry, read
    /// transitively through variable bounds.
    ///
    /// For a specialization's [reset](Self::reset_for_specialization) copy: the
    /// copy's bounds were written directly, so they were never delivered, and the
    /// pin that ties the copy to its use's types reaches the operands only through
    /// those bounds.
    pub(crate) fn redeliver(
        self: &Rc<Self>,
        cache: &mut ConstrainCache,
    ) -> Result<(), ConstrainError> {
        let operands = self.operands.borrow().clone();
        for (pos, operand) in operands.iter().enumerate() {
            let Some(Type::Infer(var)) = operand else {
                continue;
            };
            let mut stack = vec![Rc::clone(var)];
            let mut seen = std::collections::HashSet::new();
            let mut contributions = Vec::new();
            while let Some(v) = stack.pop() {
                if !seen.insert(v.uid) {
                    continue;
                }
                for bound in v.bounds.borrow().lower().iter() {
                    match &bound.ty {
                        Type::Infer(below) => stack.push(Rc::clone(below)),
                        other => contributions.push((other.clone(), bound.origin)),
                    }
                }
            }
            for (contribution, origin) in contributions {
                deliver(self, pos as u8, &contribution, origin, cache)?;
            }
        }
        Ok(())
    }

    /// Narrow by a type parameter arriving at `pos`, inside the definition that
    /// declares it.
    ///
    /// An assumption naming the parameter there is what answers it. The instances accept
    /// bases only and the product rule products only, so both drop out. With no such
    /// assumption, the parameter offers its bound in its place, and an unbounded
    /// parameter supports nothing (`src/ccl/design/type-parameters.md`, "Obligations
    /// under assumptions").
    fn narrow_param(
        self: &Rc<Self>,
        pos: u8,
        param: &Rc<crate::ccl::ty::TypeParam>,
        cache: &mut ConstrainCache,
    ) -> Result<(), ConstrainError> {
        let stated = Type::Param(Rc::clone(param));
        let assumed = self
            .assumptions
            .borrow()
            .iter()
            .any(|a| a.args.get(pos as usize) == Some(&stated));
        if assumed {
            self.candidates.borrow_mut().clear();
            self.rule_out_product_rule();
            self.assumptions
                .borrow_mut()
                .retain(|a| a.args.get(pos as usize) == Some(&stated));
            return self.try_deposit(cache);
        }
        match &param.bound {
            // The operand is this parameter, so a requirement missing further up its bound
            // chain is missing of it.
            Some(bound) => deliver(self, pos, bound, None, cache).map_err(|e| match e {
                ConstrainError::MissingRequirement {
                    trait_, position, ..
                } => ConstrainError::MissingRequirement {
                    trait_,
                    position,
                    param: Rc::clone(param),
                },
                other => other,
            }),
            None => Err(ConstrainError::MissingRequirement {
                trait_: self.trait_,
                position: pos,
                param: Rc::clone(param),
            }),
        }
    }

    /// Rule the product rule out, unless it is absent or already applied.
    fn rule_out_product_rule(&self) {
        let mut rule = self.product_rule.borrow_mut();
        if matches!(*rule, ProductRule::Open | ProductRule::Pending(_)) {
            *rule = ProductRule::RuledOut;
        }
    }

    /// Whether every candidate is gone: no row, no assumption, and no product rule
    /// that could still answer.
    fn exhausted(&self) -> bool {
        self.candidates.borrow().is_empty()
            && self.assumptions.borrow().is_empty()
            && !matches!(
                *self.product_rule.borrow(),
                ProductRule::Open | ProductRule::Pending(_) | ProductRule::Applied(_)
            )
    }

    /// What position `pos` still accepts, from the instances and the assumptions
    /// alike, for a diagnostic.
    fn accepted_types_at(&self, pos: u8) -> Vec<Type> {
        let mut out: Vec<Type> = self.accepted_at(pos).into_iter().map(Type::Base).collect();
        for a in self.assumptions.borrow().iter() {
            if let Some(arg) = a.args.get(pos as usize)
                && !out.contains(arg)
            {
                out.push(arg.clone());
            }
        }
        out
    }

    /// The type standing at each associated position, in declaration order.
    /// Freshening reads these, rewrites them, and writes them back with
    /// [`set_assoc_types`](Self::set_assoc_types).
    pub(super) fn assoc_types(&self) -> Vec<Type> {
        self.assoc.iter().map(|p| p.ty.borrow().clone()).collect()
    }

    /// The requirement this obligation states, as its operand and associated
    /// positions: `None` before every operand is watched, and for an obligation a
    /// product answered, whose conditions state it instead
    /// ([`narrow_product`](Self::narrow_product)).
    pub(super) fn stated_requirement(&self) -> Option<TraitRequirement> {
        if self.answered_by_product().is_some() {
            return None;
        }
        let operands = self.operands();
        if operands.len() != self.trait_.arity() {
            return None;
        }
        let args = operands.into_iter().collect::<Option<Vec<Type>>>()?;
        let assoc = self
            .assoc
            .iter()
            .map(|p| (p.name, p.ty.borrow().clone()))
            .collect();
        Some(TraitRequirement {
            trait_: self.trait_,
            args,
            assoc,
            at: None,
        })
    }

    /// The type standing at each operand position, `None` where none is yet.
    pub(super) fn operands(&self) -> Vec<Option<Type>> {
        self.operands.borrow().clone()
    }

    /// The variables watched at the operand positions, which belong to this
    /// obligation's own instantiation.
    pub(super) fn watched_operands(&self) -> Vec<Type> {
        self.operands.borrow().iter().flatten().cloned().collect()
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

    /// The input expressions, in argument order. Freshening reads these, freshens
    /// their type slots, and writes them back with
    /// [`set_input_exprs`](Self::set_input_exprs).
    pub(super) fn input_exprs(&self) -> Vec<TypedExpr> {
        self.input_exprs.borrow().clone()
    }

    /// Rewrite the input expressions. Freshening's second phase; see the
    /// `input_exprs` field.
    pub(super) fn set_input_exprs(&self, exprs: Vec<TypedExpr>) {
        *self.input_exprs.borrow_mut() = exprs;
    }

    /// Reject a shape no instance can accept at position `pos`.
    ///
    /// Distinct from [`narrow`](Self::narrow) failing: nothing is *ruled out* here,
    /// because there was never a candidate to rule out. The contribution is simply
    /// outside the vocabulary the trait is defined over — or beside the product the trait
    /// has already been answered at, which is the one thing the position then accepts.
    fn reject(self: &Rc<Self>, pos: u8, found: &Type) -> Result<(), ConstrainError> {
        let accepted = match self.answered_by_product() {
            Some(product) => vec![product],
            None => self.accepted_at(pos).into_iter().map(Type::Base).collect(),
        };
        Err(ConstrainError::NoTraitInstance {
            trait_: self.trait_,
            position: pos,
            found: found.clone(),
            accepted,
        })
    }

    /// The trait's operand positions *other* than `pos`, with what each still accepts.
    ///
    /// Arity is read off a surviving row rather than stored: every row of a trait has
    /// a type at every position that trait declares, which is the same invariant
    /// [`accepted_at`](Self::accepted_at) rests on.
    fn siblings_of(&self, pos: u8) -> Vec<(u8, Vec<BaseType>)> {
        let arity = self.trait_.arity();
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
        // The product rule answers this obligation, which leaves the rows no part in it, so
        // a base at any position contradicts the product rather than narrowing anything.
        // Before any product, a base rules the rule out.
        {
            let mut rule = self.product_rule.borrow_mut();
            match &*rule {
                ProductRule::Applied(_) => {
                    drop(rule);
                    return self.reject(pos, &Type::Base(base.clone()));
                }
                ProductRule::Open | ProductRule::Pending(_) => *rule = ProductRule::RuledOut,
                ProductRule::Absent | ProductRule::RuledOut => {}
            }
        }
        // Read before the mutable borrow: "what this position could have accepted" is
        // only meaningful before the contribution rules rows out.
        #[cfg(debug_assertions)]
        let accepted = self.accepted_at(pos);
        let accepted_types = self.accepted_types_at(pos);
        // An assumption accepts a base where it states that base.
        self.assumptions
            .borrow_mut()
            .retain(|a| matches!(a.args.get(pos as usize), Some(Type::Base(b)) if b == base));
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
            drop(candidates);
            if self.exhausted() {
                return Err(ConstrainError::NoTraitInstance {
                    trait_: self.trait_,
                    position: pos,
                    found: Type::Base(base.clone()),
                    accepted: accepted_types,
                });
            }
        }
        self.try_deposit(cache)
    }

    /// Answer a **product** contribution at `pos`: by an assumption stating that product
    /// there, or by the trait's product rule.
    ///
    /// The rule relates two products of the same shape when each field's components are
    /// related in turn: for `Equatable`, `{𝑎₁ … 𝑎ₙ}` and `{𝑏₁ … 𝑏ₙ}` when each pair `𝑎ᵢ`,
    /// `𝑏ᵢ` is `Equatable`. A product is no row's operand, so the rows drop out. The first
    /// product to arrive applies the rule ([`apply_product_rule`]), unless an assumption
    /// stating that product still answers the obligation; the rule then waits, and applies
    /// once none does. A product arriving after it has to have the same shape. A base
    /// already delivered has ruled the rule out, and a trait with no product reading has
    /// none.
    ///
    /// [`apply_product_rule`]: Self::apply_product_rule
    fn narrow_product(
        self: &Rc<Self>,
        pos: u8,
        product: &Type,
        cache: &mut ConstrainCache,
    ) -> Result<(), ConstrainError> {
        let peeled = peel_components(product);
        let mut stated = canonical_type(&peeled);
        let mut assumed = self
            .assumptions
            .borrow()
            .iter()
            .any(|a| a.args.get(pos as usize) == Some(&stated));
        if !assumed && let Some(arg) = self.sole_assumption_it_can_become(pos, &stated) {
            // A product of a generic use's variables arrives before its components do, so
            // it states no assumption by equality yet. Where one assumption alone states a
            // product it can become, the variables are that product's components.
            for (component, stated_component) in product_components(&stated)
                .iter()
                .zip(product_components(&arg))
            {
                if matches!(component, Type::Infer(_)) {
                    constrain_subtype(component, &stated_component, cache)?;
                    constrain_subtype(&stated_component, component, cache)?;
                }
            }
            stated = arg;
            assumed = true;
        }
        // Nothing that could answer a product: reported against what the rows accept.
        if !assumed
            && matches!(
                *self.product_rule.borrow(),
                ProductRule::Absent | ProductRule::RuledOut
            )
        {
            return self.reject(pos, product);
        }
        self.assumptions
            .borrow_mut()
            .retain(|a| a.args.get(pos as usize) == Some(&stated));
        self.candidates.borrow_mut().clear();
        let any_assumed = !self.assumptions.borrow().is_empty();
        let current = self.product_rule.borrow().clone();
        let (next, apply) = match current {
            ProductRule::Absent | ProductRule::RuledOut => (current, None),
            ProductRule::Applied(settled) => {
                if product_shape(&settled) != product_shape(&peeled) {
                    return self.reject(pos, product);
                }
                (ProductRule::Applied(settled), None)
            }
            ProductRule::Pending(settled) => {
                if product_shape(&settled) != product_shape(&peeled) {
                    (ProductRule::RuledOut, None)
                } else if any_assumed {
                    (ProductRule::Pending(settled), None)
                } else {
                    (ProductRule::Applied(settled.clone()), Some(settled))
                }
            }
            ProductRule::Open => {
                if any_assumed {
                    (ProductRule::Pending(peeled), None)
                } else {
                    (ProductRule::Applied(peeled.clone()), Some(peeled))
                }
            }
        };
        *self.product_rule.borrow_mut() = next;
        if self.exhausted() {
            return self.reject(pos, product);
        }
        if let Some(at) = apply {
            self.apply_product_rule(&at, cache)?;
        }
        self.try_deposit(cache)
    }

    /// The one assumption stating, at `pos`, a product of `stated`'s shape whose every
    /// component is `stated`'s, or one a variable component of `stated` can become.
    /// `None` when no assumption or more than one does.
    fn sole_assumption_it_can_become(&self, pos: u8, stated: &Type) -> Option<Type> {
        let fields = product_shape(stated);
        let components = product_components(stated);
        let assumptions = self.assumptions.borrow();
        let mut fitting = assumptions.iter().filter_map(|a| {
            let arg = canonical_type(a.args.get(pos as usize)?);
            let fits = matches!(arg, Type::Tuple(_) | Type::Record(_))
                && product_shape(&arg) == fields
                && components
                    .iter()
                    .zip(product_components(&arg))
                    .all(|(c, a)| matches!(c, Type::Infer(_)) || *c == a);
            fits.then_some(arg)
        });
        let first = fitting.next()?;
        fitting.next().is_none().then_some(first)
    }

    /// Mint the product rule's conditions for `product`'s shape: one obligation of this
    /// trait per field, over a variable per operand position that holds that operand's
    /// component at the field.
    ///
    /// Each operand is then bounded **above** by a product of the shape with those
    /// variables as its components. The bound states the shape every operand must have and
    /// carries each operand's components, whenever they arrive, into its own position of
    /// each field's condition. That is how the components pair: by field, one position per
    /// operand, so `𝑎ᵢ` and `𝑏ᵢ` stand at different positions of one condition and need
    /// not be one type. An upper bound states what may flow in and adds no lower bound
    /// ([`resolve_operand_requirements`]), so it decides nothing an operand does not
    /// supply. A component that is itself a product re-enters [`narrow_product`] on its
    /// condition.
    ///
    /// A variable sits at its operand's level: a component flowing in from the operand must
    /// not be carried below the level it was introduced at.
    ///
    /// [`narrow_product`]: Self::narrow_product
    fn apply_product_rule(
        self: &Rc<Self>,
        product: &Type,
        cache: &mut ConstrainCache,
    ) -> Result<(), ConstrainError> {
        let operands = self.operands.borrow().clone();
        let _f = provenance::enter(
            self.operator_node_id,
            "infer.apply_product_rule",
            provenance::Nature::Machinery,
        );
        // `slots[f][p]`: the component operand `p` holds at the product's `f`th field, in
        // its own order ([`product_fields`]).
        let slots: Vec<Vec<Type>> = product_fields(product)
            .iter()
            .map(|_| {
                operands
                    .iter()
                    .map(|operand| {
                        crate::ccl::infer::solver::fresh_var(
                            operand.as_ref().map_or(0, super::type_level),
                        )
                    })
                    .collect()
            })
            .collect();
        for at_field in &slots {
            let condition = TraitObligation::new(
                self.trait_,
                Vec::new(),
                self.operator_node_id,
                self.input_exprs(),
                self.required_at,
            );
            // A condition is answered by the same `requires` clauses as the product:
            // `Equatable({T, U}, {V, W})` is stated through its components too.
            condition.assume(&self.in_scope.borrow());
            for (pos, slot) in at_field.iter().enumerate() {
                condition.watch(slot, pos as u8);
            }
        }
        for (pos, operand) in operands.iter().enumerate() {
            let Some(operand) = operand else {
                continue;
            };
            let shape = with_components(product, slots.iter().map(|at| at[pos].clone()));
            constrain_subtype(operand, &shape, cache)?;
        }
        Ok(())
    }

    /// The product the product rule was applied at, if a product has arrived.
    pub(super) fn answered_by_product(&self) -> Option<Type> {
        match &*self.product_rule.borrow() {
            ProductRule::Applied(product) | ProductRule::Pending(product) => Some(product.clone()),
            _ => None,
        }
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
            let Some((settled, maybe_refinement)) = self.agreed_assoc(position.name) else {
                continue;
            };
            position.deposited.set(true);
            let _f = provenance::enter(
                self.operator_node_id,
                "infer.try_deposit",
                provenance::Nature::Machinery,
            );
            let target = position.ty.borrow().clone();
            let ty_base = settled;
            let ty = match maybe_refinement {
                Some(template) => Type::Refinement(
                    Box::new(ty_base),
                    RefinementSet::one(Refinement::born_from_template(
                        template,
                        &self.input_exprs.borrow(),
                    )),
                ),
                None => ty_base,
            };
            constrain_subtype(&ty, &target, cache)?;
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
    ///
    /// Instances and assumptions are read alike: an assumption associates the type
    /// its `requires` clause names, and one that names none leaves the position
    /// open. A refinement template is an instance's alone.
    fn agreed_assoc(&self, name: Assoc) -> Option<(Type, Option<RefinementTemplate>)> {
        let mut settled: Option<(Type, Option<RefinementTemplate>)> = None;
        let mut agree = |ty: Type, template: Option<RefinementTemplate>| match &settled {
            None => {
                settled = Some((ty, template));
                true
            }
            Some((s, _)) => *s == ty,
        };
        for instance in self.candidates.borrow().iter() {
            let (ty, template) = instance.assoc_ty(name)?;
            if !agree(Type::Base(ty.clone()), template) {
                return None;
            }
        }
        for assumption in self.assumptions.borrow().iter() {
            let ty = assumption.assoc_ty(name)?;
            if !agree(ty.clone(), None) {
                return None;
            }
        }
        settled
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
    /// Debug-only, and wider than [`TraitObligation::operands`], which holds the current
    /// type at each position because answering a product needs it. This keeps the whole
    /// history — every contribution at every position, in arrival order — which is what a
    /// delivery question is asked of, and which no production path may read.
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
                // Not a base leaf. A product owes `narrow_product`, which answers it by
                // the product rule — it bounds every operand by the shape and mints a
                // condition per field — rather than shrinking the candidate set this walk
                // reads. So there is no narrowing here to check against.
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

/// Strip every refinement, as [`offered`] does: `{𝑇 | 𝑝}` constrains a place
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
            // An obligation answered by a product is answered off the table, so its
            // `accepted_at` is the untouched row set and intersecting it would deposit a
            // base at a place holding a product ([`TraitObligation::narrow_product`]).
            //
            // An obligation that still holds assumptions is about a type parameter its
            // `requires` clause states, which the sweep's base intersection cannot read.
            if obligation.answered_by_product().is_some()
                || !obligation.assumptions.borrow().is_empty()
            {
                continue;
            }
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
                Type::DepTuple(components) => {
                    for (i, (_, elem)) in components.iter().enumerate() {
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
                history @ Type::History { .. } => {
                    let (_, value, _) = history.history_parts().expect("matched a history");
                    descend(value, &path, Step::HistoryValue, &mut frontier)
                }
                // Leaves: nothing inside to constrain. `Base`/`UIntRange` are concrete,
                // and the rest are placeholders or nullary carriers. A witness reference
                // names a binder and holds no type.
                Type::WitnessRef(_)
                | Type::Base(_)
                | Type::UIntRange(_)
                | Type::Hole
                | Type::SharedHole(_)
                | Type::DataSource(_)
                | Type::ChanDom(_, _)
                | Type::Param(_)
                | Type::Txn => {}
                Type::Poly(_) => unreachable!("a polymorphic type is never a recorded bound"),
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
    /// Raised for the first such place found. *Whether* a program is rejected does not
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
    /// A determined **product** — a tuple or a record.
    ///
    /// No row keys on one ([`TraitInstance::args`] holds bases), so a product is
    /// answered structurally or not at all: a
    /// [structural](Trait::is_structural) trait decomposes it into one obligation per
    /// component, and every other trait rejects it as [`NotABase`](Self::NotABase) does.
    Product(&'a Type),
    /// A determined type that is neither a base leaf nor a product — a variant or a
    /// function.
    ///
    /// Every instance is keyed on a base ([`TraitInstance::args`]), so nothing in
    /// any table accepts it and the requirement fails here rather than silently
    /// going unresolved. That the tables hold only bases is their *content*, not a
    /// property of resolution: giving `Equatable` a variant would add rows, and
    /// would split this variant into the shapes a row can key on — it would not
    /// change how narrowing works.
    NotABase,
    /// A type parameter, inside the definition that declares it. It supports what
    /// its bound supports, and nothing if it has none
    /// (`src/ccl/design/type-parameters.md`, "Obligations under assumptions").
    Param(&'a Rc<crate::ccl::ty::TypeParam>),
}

/// `product` with every component's refinements peeled, recursively through nested products.
///
/// A refinement does not affect a trait, so what a product contribution says about the
/// positions beside it is its shape and their bases — never `(Int@1, Int@2)`, which would
/// hold the sibling to one pair of literals. [`offered`] peels the base case for the same
/// reason; a product's components are where the same peel belongs.
fn peel_components(product: &Type) -> Type {
    fn peeled(ty: &Type) -> Type {
        let bare = {
            let mut cur = ty;
            while let Type::Refinement(inner, _) = cur {
                cur = inner;
            }
            cur
        };
        match bare {
            Type::Tuple(_) | Type::Record(_) => peel_components(bare),
            other => other.clone(),
        }
    }
    match product {
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(peeled).collect()),
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), peeled(ty)))
                .collect(),
        ),
        other => unreachable!("`peel_components` is reached only for a product, got {other:?}"),
    }
}

/// A product's field keys, which is what makes two products the same shape.
pub(crate) fn product_fields(product: &Type) -> Vec<FieldKey> {
    match product {
        Type::Tuple(elems) => (0..elems.len()).map(FieldKey::Index).collect(),
        Type::Record(fields) => fields
            .iter()
            .map(|(name, _)| FieldKey::Name(name.as_str().into()))
            .collect(),
        other => unreachable!("`product_fields` is reached only for a product, got {other:?}"),
    }
}

/// `ty` with every record's fields in a canonical order, recursively: the form two
/// spellings of one type share, which an assumption is matched in
/// ([`TraitObligation::narrow_product`]).
pub(crate) fn canonical_type(ty: &Type) -> Type {
    let mut out = ty.clone();
    fn go(ty: &mut Type) {
        if let Type::Record(fields) = ty {
            fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        }
        ty.walk_children_mut(go);
    }
    go(&mut out);
    out
}

/// A product's fields in a canonical order, for deciding whether two products are the same
/// shape.
///
/// `Type::Record` holds a `Vec` that no construction site orders, so two spellings of one
/// record shape reach here with their fields in different orders.
pub(crate) fn product_shape(product: &Type) -> Vec<FieldKey> {
    let mut fields = product_fields(product);
    fields.sort();
    fields
}

/// `product` with its components replaced by `components`, given in its own field order
/// ([`product_fields`]).
fn with_components(product: &Type, components: impl IntoIterator<Item = Type>) -> Type {
    let mut components = components.into_iter();
    let mut next = || {
        components
            .next()
            .expect("one component per field of the product")
    };
    match product {
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(|_| next()).collect()),
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(name, _)| (name.clone(), next()))
                .collect(),
        ),
        other => unreachable!("`with_components` is reached only for a product, got {other:?}"),
    }
}

/// A product's component types, in the product's own field order: the order
/// [`product_fields`] lists the fields in.
pub(crate) fn product_components(product: &Type) -> Vec<Type> {
    match product {
        Type::Tuple(elems) => elems.clone(),
        Type::Record(fields) => fields.iter().map(|(_, ty)| ty.clone()).collect(),
        other => unreachable!("`product_components` is reached only for a product, got {other:?}"),
    }
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
        // A product is determined and is not a base, but it has components a
        // structural trait can be asked of ([`Trait::is_structural`]).
        Type::Tuple(_) | Type::Record(_) => Offered::Product(cur),
        // Sums and functions are fully determined and are not bases. A collection
        // compared or added is the same mistake as a variant.
        Type::Variant(_, _) | Type::Fun { .. } => Offered::NotABase,
        Type::Param(param) => Offered::Param(param),
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
/// variables feeding the watched one. This is what a var-var kind edge does
/// (`constrain_fun_kind`, recorded on both sides) — a kind force propagates along stored
/// links for the same
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
    // offered — it arrived before the edge existed. A type parameter is replayed
    // with the bases: missing one would leave an operator on an unbounded parameter
    // unchecked.
    let (known, params, below) = {
        let bounds = lower.bounds.borrow();
        let known: Vec<(BaseType, Option<crate::ccl::infer_var::Origin>)> = bounds
            .lower()
            .iter()
            .filter_map(|b| offered_base(&b.ty).map(|base| (base.clone(), b.origin)))
            .collect();
        let params: Vec<(Type, Option<crate::ccl::infer_var::Origin>)> = bounds
            .lower()
            .iter()
            .filter(|b| matches!(offered(&b.ty), Offered::Param(_)))
            .map(|b| (b.ty.clone(), b.origin))
            .collect();
        let below: Vec<Rc<InferVar>> = bounds
            .lower()
            .iter()
            .filter_map(|b| match &b.ty {
                Type::Infer(v) => Some(Rc::clone(v)),
                _ => None,
            })
            .collect();
        (known, params, below)
    };
    for (obligation, pos) in &added {
        for (base, origin) in &known {
            if let Err(e) = obligation.narrow(*pos, base, cache) {
                cache.note_failure_with(*origin, Some(obligation.required_at()));
                return Err(e);
            }
        }
        for (param, origin) in &params {
            deliver(obligation, *pos, param, *origin, cache)?;
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
    for (obligation, pos) in watches {
        deliver(&obligation, pos, contribution, None, cache)?;
    }
    Ok(())
}

/// Offer `contribution` to `obligation` at position `pos`.
///
/// A type parameter offers its bound: a value of a bounded parameter's type is a
/// value of its bound's type. An unbounded parameter supports no trait.
fn deliver(
    obligation: &Rc<TraitObligation>,
    pos: u8,
    contribution: &Type,
    value: Option<crate::ccl::infer_var::Origin>,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    let delivered = match offered(contribution) {
        Offered::Base(base) => obligation.narrow(pos, base, cache),
        Offered::Product(product) => obligation.narrow_product(pos, product, cache),
        Offered::NotABase => obligation.reject(pos, contribution),
        Offered::Param(param) => obligation.narrow_param(pos, param, cache),
        Offered::Unknown => Ok(()),
    };
    // The obligation is the demand a contribution failed: an edge a deposit drew
    // further in, failing first, has already recorded its own.
    if delivered.is_err() {
        cache.note_failure_with(value, Some(obligation.required_at()));
    }
    delivered
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::infer::solver::fresh_var;

    /// The operand expressions an obligation substitutes into an instance's
    /// refinement template.
    fn operands() -> Vec<TypedExpr> {
        vec![
            TypedExpr::lit(crate::ccl::Lit::Int(1)),
            TypedExpr::lit(crate::ccl::Lit::Int(2)),
        ]
    }

    /// Both narrowing orders reach the same answer — the property that lets the
    /// obligation be resolved incrementally instead of by a final sweep.
    #[rstest::rstest]
    #[case(&[(0, BaseType::Int), (1, BaseType::Int)])]
    #[case(&[(1, BaseType::Int), (0, BaseType::Int)])]
    fn narrowing_is_order_independent(#[case] steps: &[(u8, BaseType)]) {
        let node_id = provenance::NodeId::fresh();
        let out = fresh_var(0);
        let ob = TraitObligation::new(
            Trait::Addable,
            vec![(Assoc::Output, out.clone())],
            node_id,
            operands(),
            crate::ccl::infer_var::Origin::Node(node_id),
        );
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
                .any(|b| b.ty.peel_refinements() == &Type::Base(BaseType::Int)),
            "the settled output type is deposited as a lower bound on O",
        );
    }

    /// One known operand is enough to settle the output when every remaining
    /// instance agrees on it — without concluding anything about the *other*
    /// operand, which stays open for a future heterogeneous instance.
    #[test]
    fn one_known_operand_settles_an_agreed_output() {
        let node_id = provenance::NodeId::fresh();
        let out = fresh_var(0);
        let ob = TraitObligation::new(
            Trait::Addable,
            vec![(Assoc::Output, out.clone())],
            node_id,
            operands(),
            crate::ccl::infer_var::Origin::Node(node_id),
        );
        let mut cache = ConstrainCache::new();

        ob.narrow(1, &BaseType::Int, &mut cache)
            .expect("Int is addable");

        assert!(
            matches!(
                ob.agreed_assoc(Assoc::Output),
                Some((Type::Base(BaseType::Int), None))
            ),
            "(Int, Int) ⇝ Int is the only row left, so its Output is settled, and \
             `+` leaves that output unrefined",
        );
        let candidates = ob.candidates();
        let [only] = candidates.as_slice() else {
            panic!("(Int, Int) ⇝ Int is the only Addable row left, got {candidates:?}");
        };
        assert_eq!(only.args, &[BaseType::Int, BaseType::Int]);
        assert!(matches!(only.assoc, [(Assoc::Output, BaseType::Int, None)]));
    }

    /// `^+` deposits the sum on its output; `+` deposits a bare `Int`. The two
    /// traits differ in exactly this, so one obligation of each pins it.
    #[test]
    fn only_the_refining_addition_carries_a_predicate() {
        let deposited = |trait_| {
            let node_id = provenance::NodeId::fresh();
            let out = fresh_var(0);
            let ob = TraitObligation::new(
                trait_,
                vec![(Assoc::Output, out.clone())],
                node_id,
                operands(),
                crate::ccl::infer_var::Origin::Node(node_id),
            );
            ob.narrow(0, &BaseType::Int, &mut ConstrainCache::new())
                .expect("Int adds to Int under either trait");
            let Type::Infer(v) = &out else { unreachable!() };
            let bounds = v.bounds.borrow();
            bounds
                .lower()
                .iter()
                .map(|b| b.ty.to_string())
                .collect::<Vec<_>>()
        };

        assert_eq!(deposited(Trait::Addable), vec!["Int"]);
        assert_eq!(
            deposited(Trait::AddableRefined),
            vec!["{Int | __elem == 1 ^+ 2}"],
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
        let node_id = provenance::NodeId::fresh();
        let ob = TraitObligation::new(
            Trait::Equatable,
            Vec::new(),
            node_id,
            operands(),
            crate::ccl::infer_var::Origin::Node(node_id),
        );
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
        let node_id = provenance::NodeId::fresh();
        let out = fresh_var(0);
        let ob = TraitObligation::new(
            Trait::Orderable,
            vec![(Assoc::Output, out)],
            node_id,
            operands(),
            crate::ccl::infer_var::Origin::Node(node_id),
        );
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
        assert_eq!(accepted, vec![Type::Base(BaseType::Int)]);
    }

    /// The product rule pairs components by field, one condition position per operand:
    /// each operand is bounded above by the shape over variables of its own, and the
    /// variables at one field stand at different positions of the same condition.
    #[test]
    fn the_product_rule_pairs_components_by_field() {
        use crate::ccl::infer::solver::constrain_subtype;
        let node_id = provenance::NodeId::fresh();
        let ob = TraitObligation::new(
            Trait::Equatable,
            Vec::new(),
            node_id,
            operands(),
            crate::ccl::infer_var::Origin::Node(node_id),
        );
        let (a, b) = (fresh_var(1), fresh_var(1));
        ob.watch(&a, 0);
        ob.watch(&b, 1);
        let mut cache = ConstrainCache::new();
        let pair = |x: BaseType, y: BaseType| Type::Tuple(vec![Type::Base(x), Type::Base(y)]);
        constrain_subtype(&pair(BaseType::Int, BaseType::String), &a, &mut cache)
            .expect("a pair of equatable bases is a product the rule answers");
        constrain_subtype(&pair(BaseType::Int, BaseType::String), &b, &mut cache)
            .expect("the same shape over the same bases");

        // The variables each operand's upper bound holds, by field.
        let slots = |v: &Type| -> Vec<Rc<InferVar>> {
            let Type::Infer(v) = v else { unreachable!() };
            let upper = Rc::clone(v.bounds.borrow().upper());
            let tuples: Vec<Vec<Rc<InferVar>>> = upper
                .iter()
                .filter_map(|bound| match &bound.ty {
                    Type::Tuple(elems) => Some(
                        elems
                            .iter()
                            .map(|e| match e {
                                Type::Infer(s) => Rc::clone(s),
                                other => panic!("a slot is a variable, got {other:?}"),
                            })
                            .collect(),
                    ),
                    _ => None,
                })
                .collect();
            let [only] = tuples.as_slice() else {
                panic!("one shape bound per operand, got {tuples:?}");
            };
            only.clone()
        };
        let (a_slots, b_slots) = (slots(&a), slots(&b));
        for (field, (sa, sb)) in a_slots.iter().zip(&b_slots).enumerate() {
            assert_ne!(
                sa.uid, sb.uid,
                "field {field}: each operand has its own slot"
            );
            let watched = |s: &Rc<InferVar>| -> Vec<(TraitObligationId, u8)> {
                s.watches
                    .borrow()
                    .iter()
                    .map(|(o, p)| (o.uid, *p))
                    .collect()
            };
            let (wa, wb) = (watched(sa), watched(sb));
            let [(ca, 0)] = wa.as_slice() else {
                panic!(
                    "field {field}: operand 0's slot is position 0 of one condition, got {wa:?}"
                );
            };
            let [(cb, 1)] = wb.as_slice() else {
                panic!(
                    "field {field}: operand 1's slot is position 1 of one condition, got {wb:?}"
                );
            };
            assert_eq!(ca, cb, "field {field}: both slots belong to one condition");
        }
        assert_ne!(
            ob.answered_by_product(),
            None,
            "the rule was applied at the first product"
        );
    }

    /// A base after a product, and a product after a base, each contradict the candidate
    /// the first contribution left.
    #[rstest::rstest]
    #[case::base_then_product(true)]
    #[case::product_then_base(false)]
    fn a_base_and_a_product_exclude_each_other(#[case] base_first: bool) {
        let node_id = provenance::NodeId::fresh();
        let ob = TraitObligation::new(
            Trait::Equatable,
            Vec::new(),
            node_id,
            operands(),
            crate::ccl::infer_var::Origin::Node(node_id),
        );
        let (a, b) = (fresh_var(1), fresh_var(1));
        ob.watch(&a, 0);
        ob.watch(&b, 1);
        let mut cache = ConstrainCache::new();
        let product = Type::Tuple(vec![Type::Base(BaseType::Int)]);
        let result = if base_first {
            ob.narrow(0, &BaseType::Int, &mut cache)
                .expect("Int is equatable");
            ob.narrow_product(1, &product, &mut cache)
        } else {
            ob.narrow_product(0, &product, &mut cache)
                .expect("a tuple of Int is equatable");
            ob.narrow(1, &BaseType::Int, &mut cache)
        };
        assert!(
            matches!(result, Err(ConstrainError::NoTraitInstance { .. })),
            "got {result:?}"
        );
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
            Trait::AddableRefined,
            Trait::Subtractable,
            Trait::Multipliable,
            Trait::Divisible,
            Trait::Exponentiable,
            Trait::Equatable,
            Trait::Orderable,
            Trait::Negatable,
        ] {
            let (arity, assocs) = (trait_.arity(), trait_.assocs());
            for row in trait_.instances() {
                assert_eq!(
                    row.args.len(),
                    arity,
                    "{trait_} has rows of differing arity: {row:?}",
                );
                let names: Vec<Assoc> = row.assoc.iter().map(|(n, _, _)| *n).collect();
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
        let refined = Type::refined_one(
            Type::Base(BaseType::String),
            Refinement::born(Rc::new(TypedExpr::lit(crate::ccl::Lit::Bool(true)))),
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

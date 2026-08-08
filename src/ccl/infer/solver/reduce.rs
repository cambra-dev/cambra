//! Reduction of [`Type::App`] — running a [`TypeFn`] on resolved argument types.
//!
//! # What a type function is
//!
//! A type function **denotes** a type; it does not construct one. `Add(Int, Int)`
//! is not a new type sitting beside `Int` in the lattice — it is `Int`, written in
//! a form that does not yet know it. Reduction is therefore *normalization*, not a
//! computation step that could be observed: [`Type::App`] is transient in exactly
//! the sense [`Type::Infer`] is, and every `Type` that escapes inference is
//! `App`-free.
//!
//! That is what keeps type functions out of the lattice's way. They add no
//! inhabitants and no subtyping edges, so [`constrain`](super::constrain) never has
//! to decide `Add(α, β) <: Add(γ, δ)` structurally — it decides the reduced types
//! instead, once the arguments are known.
//!
//! # The laws a rule must satisfy
//!
//! Adding a [`TypeFn`] variant means writing a rule in [`reduce`], and the rule is
//! only sound if it obeys all four. Each is a property of the reduction
//! *mechanism*, checkable by reading the rule, and each buys a specific guarantee
//! for inference.
//!
//! What is deliberately **not** here is a law about refinements. Whether a rule may
//! carry an argument's refinement into its result is not a property of reduction —
//! it is a question about what the operator *means*, and the answer differs per
//! operator: a rule that **selects** one of its arguments (`Max`, and `FieldOf` when
//! it lands) must carry it, because the result really is that value, while a rule
//! that **computes** a new one must not. That distinction is stated where it can be
//! decided, in `src/ccl/design/type-inference.md`, "Which operators need one". A
//! blanket prohibition here would forbid the selecting rules outright, and would
//! still not catch the failure that actually threatens soundness — a rule that
//! *invents* a claim its arguments do not support, which is monotone (law 2) and
//! inherits nothing.
//!
//! 1. **Pure.** A rule is a function of `(fun, args)` and nothing else: no
//!    inference context, no bound graph, no fresh variables, no recorded
//!    constraints. *Buys:* reduction can run at any point in any walk, so it can be
//!    demand-driven rather than scheduled into a phase.
//!
//! 2. **Monotone** in the subtype order: if `aᵢ <: bᵢ` for every `i`, then
//!    `f(a⃗) <: f(b⃗)`. *Buys:* an argument only ever gets more precise as the graph
//!    fills in, so a later reduction refines an earlier one rather than
//!    contradicting it.
//!
//! 3. **Declares a [`CycleTolerance`].** A rule states whether it can answer while
//!    an argument is [`Arg::Cyclic`], and [`reduce`] enforces it. *Buys:* a rule
//!    that cannot answer reports the cycle instead of guessing, and one that can is
//!    never asked to. See "Cycles" below — this is a property of the *program*, not
//!    an edge case.
//!
//! 4. **Normalizing.** The result contains no [`Type::App`]. *Buys:* one `reduce`
//!    call terminates without a fixpoint, because the rule set is closed and no
//!    rule feeds itself.
//!
//! # Cycles
//!
//! An argument arrives [`Cyclic`](Arg::Cyclic) when resolving it would re-enter the
//! resolution *already computing it*. This is not an edge case and not a scheduling
//! artifact — it is a **recurrence in the program**.
//!
//! A register that reads itself in its own write makes one. `x += 1` gives the
//! register's value type as the join over its seed and its writes, and one write is
//! `x + 1`, typed `Add(value(x), 1)` — so `value(x)` satisfies
//!
//! ```text
//! value(x)  =  join(seed, Add(value(x), 1))
//! ```
//!
//! a fixpoint equation, because an accumulator *is* one. Measured: 1,910 cyclic
//! arguments across the test suite, and adding a self-read is exactly what creates
//! them (`x := 7; x` has none, `x := 7; x += 1; x` has ten).
//!
//! [`compact.rs`](super::compact)'s in-flight set cuts the recursion — without it a
//! program that small overflows the stack — and the [`CycleTolerance`] a rule
//! declares is what decides whether the cut-off is usable or fatal *for that rule*.
//!
//! **Answering at a cycle is one step of a fixpoint iteration from ⊥**, and it is
//! exact only because the base sublattice is flat: `Add(⊥, Int)` is `Int`, and
//! re-substituting gives `Int` again, so one step saturates. A rule over a lattice
//! with infinite ascending chains would not saturate — a range-aware `Arithmetic`
//! on `x := 0; x += 1` walks `[0,0] → [0,1] → [0,2] → …` and needs *widening*, not
//! one step. That rule cannot land on this machinery unchanged, which is worth
//! knowing before writing it.
//!
//! For a tolerant rule the imprecision does not escape: the frame that materializes
//! the node runs the same rule again with every argument known, which is where
//! operands that genuinely disagree are caught.
//!
//! Every rule today satisfies law 3, so a missing argument is never itself a
//! failure. A future function that cannot — `FieldOf(ρ, 𝑘)` has nothing to say
//! without `ρ` — is a rule that *violates* law 3 and must therefore report the
//! cycle, as a new [`ReduceError`] variant introduced with it. It is deliberately
//! not here yet: today nothing could construct it, so nothing could test it.

use crate::ccl::ccl_utils::strip_refinements;
use crate::ccl::{Type, TypeFn};

/// One resolved argument, or the fact that resolving it re-entered the resolution
/// **already computing it**.
///
/// Named rather than an `Option` because the distinction a rule has to reason about
/// is not "absent" but *cyclic*: the argument is not unknown-for-now, it is being
/// defined in terms of this very application, and there is no later point at which
/// more is known. See the module docs, "Cycles".
#[derive(Debug, Clone)]
pub enum Arg {
    /// Resolved to a type.
    Known(Type),
    /// Resolving this argument would re-enter the resolution computing it.
    Cyclic,
}

/// Whether a rule can answer while some of its arguments are [`Arg::Cyclic`].
///
/// Deliberately **not** per-position. Every rule's condition is a statement about
/// *how many* arguments are cyclic, not which — arithmetic's operands are
/// interchangeable to its rule, and a rule that needs one argument needs it whether
/// it is written first or second. Today every rule sits at one extreme or the
/// other; a rule that needed "at least `n` of them" would generalize this to a
/// count, and nothing yet does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CycleTolerance {
    /// Answers from whatever is known. A cyclic argument costs **precision**, never
    /// the answer — and for a rule constant on its domain, not even that.
    Any,
    /// Cannot answer unless every argument is known, so a cyclic one is reported
    /// rather than guessed.
    AllKnown,
}

/// Reject a cyclic argument on behalf of a rule that cannot answer through one.
///
/// Checked here, once, rather than by each rule: the obligation belongs to the
/// rules that *cannot* answer, and those are exactly the rules whose author is most
/// likely to reach for a plausible guess instead. Declaring the tolerance and
/// enforcing it centrally is what makes forgetting impossible rather than merely
/// discouraged.
fn check_cycle_tolerance(
    tolerance: CycleTolerance,
    args: &[Arg],
    fun: &str,
) -> Result<(), ReduceError> {
    if tolerance == CycleTolerance::AllKnown && args.iter().any(|a| matches!(a, Arg::Cyclic)) {
        return Err(ReduceError::CyclicArgument {
            fun: fun.to_string(),
        });
    }
    Ok(())
}

/// Why a reduction could not produce a type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReduceError {
    /// The arguments' bases have no join below `⊤` — `1 + "a"`. A genuine type
    /// error in the program.
    NoCommonBase {
        /// The type function that could not reduce, as it is spelled in a type.
        fun: String,
        /// The conflicting bases, rendered, in argument order.
        bases: Vec<String>,
    },
    /// An argument of a [`CycleTolerance::AllKnown`] rule was [`Arg::Cyclic`].
    ///
    /// The program defined something in terms of itself in a way this rule cannot
    /// answer through — a projection whose record is its own field type, say. Not a
    /// conflict between types: a genuine cycle, reported rather than guessed at.
    CyclicArgument {
        /// The type function that could not answer, as it is spelled in a type.
        fun: String,
    },
}

/// Run `fun` on `args`, where `None` marks an argument whose resolution is already
/// in flight (see the module docs).
///
/// Returns `Err` only for a real conflict, which the caller that materialized the
/// type reports. A missing argument is not one: every rule today satisfies law 3.
pub fn reduce(fun: &TypeFn, args: &[Arg]) -> Result<Type, ReduceError> {
    check_cycle_tolerance(fun.cycle_tolerance(), args, fun.name())?;
    let available: Vec<&Type> = args
        .iter()
        .filter_map(|a| match a {
            Arg::Known(t) => Some(t),
            Arg::Cyclic => None,
        })
        .collect();
    match fun {
        // Arithmetic's result *is* the operands' shared base today, so deciding
        // what is addable and computing the result are one step. The kind is kept
        // because a range-aware rule needs it (`+` and `*` map operand ranges
        // differently), which is also where the two stop coinciding.
        TypeFn::Arithmetic(_) => shared_base(fun, &available),
        // A comparison **checks and then discards**: its result is `Bool` for any
        // operands that share a base and undefined for any that do not, so the rule
        // is constant on its domain and the whole of its content is the domain.
        //
        // That is not a rule contorted to force a check — it is what comparison
        // means — but the check is the reason the result is `Compare(α, β)` rather
        // than a bare `Bool`. A bare `Bool` mentions neither operand, so nothing
        // would ever materialize them and nothing would ever run this rule; see
        // `OperatorSchemes`'s "An operand requirement must be reachable from the
        // result type".
        //
        // Unavailable arguments weaken the check, not the answer: `Bool` is the
        // result whether or not the operands have resolved.
        TypeFn::Compare(_) => {
            shared_base(fun, &available)?;
            Ok(Type::Base(crate::ccl::BaseType::Bool))
        }
    }
}

/// `⊔ᵢ base(argᵢ)` — the join of the arguments' bases, defined only where it is not
/// `⊤` (see the module docs, "What \"the operands share a base\" is, and is not").
///
/// Stripping refinements is not an approximation to be improved on — it is what
/// makes this the *base* join. A refinement is a fact about a value, and neither
/// the join of several types nor the result of computing with them is any of the
/// values the arguments described. (A range-aware arithmetic rule would *derive* a
/// new claim rather than inherit one, which is a different operation and belongs to
/// that rule, not here.)
///
/// The `debug_assert` below is this function's **postcondition**, not a rule every
/// reduction obeys: a join taken in the base sublattice lands in the base
/// sublattice. It is asserted because the strip and the join are separate steps, so
/// a refinement surviving one of them would otherwise be silent. A rule that
/// *selects* an argument (`Max`, `FieldOf`) is supposed to carry that argument's
/// refinement through and must not reuse this postcondition — see
/// `src/ccl/design/type-inference.md`, "Which operators need one".
///
/// Missing and unresolved arguments are skipped rather than treated as `⊥`, which
/// is law 3: the join over a subset is a supertype of the join over all of them. With
/// nothing available at all the answer is `Hole`, the "nothing is known here" type —
/// reachable only for a fully cyclic application, and it lets the enclosing
/// resolution fall back to whatever else it can see rather than failing outright.
///
/// **The join is computed with `==`, which is only right for leaf arguments.** In a
/// discrete sublattice the join of two types is either one of them or `⊤`, so `==`
/// decides it — but only when the arguments have no *interior*. Two bases differing
/// solely in an unresolved position inside them — `(?1, Int)` and `(?2, Int)` —
/// compare unequal and would be reported as a conflict, which is a claim about
/// placeholder identity rather than about types. Nothing can reach that today: every
/// operand of an arithmetic or comparison operator that the runtime accepts is a
/// scalar, so a stripped argument is a leaf or a bare `Infer`, and a bare `Infer` is
/// skipped. A compound-argument type function — `FieldOf(ρ, 𝑘)` and
/// `CollectionUnion` are the named next clients — must not reuse this test; it needs
/// agreement *modulo* unresolved positions, the way the lattice itself compares.
fn shared_base(fun: &TypeFn, args: &[&Type]) -> Result<Type, ReduceError> {
    let mut bases = args.iter().map(|t| strip_refinements(t));
    let Some(first) = bases.next() else {
        return Ok(Type::Hole);
    };
    let mut result = first;
    for base in bases {
        // An unresolved argument contributes no constraint on the base: it is a
        // position nothing concrete reached, not a conflicting one.
        if matches!(result, Type::Hole | Type::Infer(_)) {
            result = base;
            continue;
        }
        if matches!(base, Type::Hole | Type::Infer(_)) || base == result {
            continue;
        }
        return Err(ReduceError::NoCommonBase {
            fun: fun.name().to_string(),
            bases: args
                .iter()
                .map(|t| strip_refinements(t).to_string())
                .collect(),
        });
    }
    debug_assert!(
        !matches!(result, Type::Refinement(..)),
        "{fun} reduced to a refined type ({result}) — a computed type must carry no \
         value-level claim of its own"
    );
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::infer::lit_singleton;
    use crate::ccl::{ArithmeticKind, BaseType, Lit};

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }
    fn add() -> TypeFn {
        TypeFn::Arithmetic(ArithmeticKind::Add)
    }

    /// The reported bug, at the level of the rule: two operands that are each the
    /// *same* singleton must still compute to the base. Sharing a lattice position
    /// intersects refinement sets, and intersecting a set with itself returns it —
    /// which is how `1 + 1` came to claim it was `1`.
    #[test]
    fn arithmetic_on_identical_singletons_is_the_base() {
        let one = lit_singleton(&Lit::Int(1));
        let out = reduce(&add(), &[Arg::Known(one.clone()), Arg::Known(one)]).expect("reduces");
        assert_eq!(out, int());
    }

    #[test]
    fn arithmetic_drops_refinements_and_keeps_the_base() {
        let out = reduce(
            &add(),
            &[
                Arg::Known(lit_singleton(&Lit::Int(1))),
                Arg::Known(lit_singleton(&Lit::Int(5))),
            ],
        )
        .expect("reduces");
        assert_eq!(out, int());
    }

    #[test]
    fn conflicting_bases_are_an_error() {
        let err = reduce(
            &add(),
            &[Arg::Known(int()), Arg::Known(Type::Base(BaseType::String))],
        )
        .expect_err("Int and String share no base");
        assert!(matches!(err, ReduceError::NoCommonBase { .. }), "{err:?}");
    }

    /// Law 3: an argument the program has not determined weakens the check, not
    /// the answer. `\x -> x > 1` still has result type `Bool` with its operand
    /// undetermined, and `\x -> x + 1` still has result type `Int`.
    #[test]
    fn a_missing_argument_answers_from_the_rest() {
        let out = reduce(
            &add(),
            &[Arg::Cyclic, Arg::Known(lit_singleton(&Lit::Int(1)))],
        )
        .expect("coarsens");
        assert_eq!(out, int());
    }

    /// And with nothing available it is the empty answer, not an error — the
    /// enclosing resolution may still have another way to see the position.
    #[test]
    fn all_arguments_missing_is_the_empty_answer() {
        let out = reduce(&add(), &[Arg::Cyclic, Arg::Cyclic]).expect("coarsens");
        assert_eq!(out, Type::Hole);
    }

    /// The two tolerances are different in kind, and the dispatch between them is
    /// checked directly — no rule reports `AllKnown` yet, so going through
    /// [`reduce`] would only ever exercise one arm.
    ///
    /// [`CycleTolerance::Any`] is what lets an accumulator have a type at all: a
    /// register that reads itself in its own write makes `Add(value(x), 1)` where
    /// `value(x)` is what is being computed, and a rule that refused to answer
    /// would reject every `x += 1`.
    ///
    /// [`CycleTolerance::AllKnown`] is the case `FieldOf(ρ, 𝑘)` will be: no answer
    /// exists without `ρ`, so the cycle is reported rather than guessed at.
    #[test]
    fn a_rule_that_cannot_answer_through_a_cycle_reports_it() {
        let cyclic = [Arg::Cyclic, Arg::Known(int())];
        let known = [Arg::Known(int()), Arg::Known(int())];

        assert!(check_cycle_tolerance(CycleTolerance::AllKnown, &cyclic, "FieldOf").is_err());
        assert!(check_cycle_tolerance(CycleTolerance::AllKnown, &known, "FieldOf").is_ok());
        assert!(check_cycle_tolerance(CycleTolerance::Any, &cyclic, "Add").is_ok());
    }

    /// Today's rules both tolerate a cycle, for reasons worth keeping apart: a
    /// comparison is *constant on its domain* so a cyclic operand costs nothing,
    /// while arithmetic answers from the operand it can see and loses only the
    /// agreement check.
    #[test]
    fn todays_rules_tolerate_a_cycle() {
        assert_eq!(add().cycle_tolerance(), CycleTolerance::Any);
        assert_eq!(
            TypeFn::Compare(crate::ccl::CompareKind::Equals).cycle_tolerance(),
            CycleTolerance::Any
        );
        assert_eq!(
            reduce(&add(), &[Arg::Cyclic, Arg::Known(int())]).expect("answers"),
            int()
        );
        assert_eq!(
            reduce(
                &TypeFn::Compare(crate::ccl::CompareKind::Equals),
                &[Arg::Cyclic, Arg::Cyclic]
            )
            .expect("constant on its domain"),
            Type::Base(BaseType::Bool)
        );
    }
}

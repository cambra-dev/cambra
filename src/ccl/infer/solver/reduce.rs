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
//! 3. **Coarsening on a missing argument.** Dropping arguments only weakens the
//!    answer — never errors, and never claims more than the full argument list
//!    would. *Buys:* a rule reached before its arguments are known gives a usable
//!    answer instead of a wrong one; an unapplied `λ x → x > 1` still has result
//!    type `Bool`.
//!
//! 4. **Normalizing.** The result contains no [`Type::App`]. *Buys:* one `reduce`
//!    call terminates without a fixpoint, because the rule set is closed and no
//!    rule feeds itself.
//!
//! # What "the operands share a base" is, and is not
//!
//! [`shared_base`] is `⊔ᵢ base(argᵢ)` — the join of the arguments' bases, defined
//! only where that join is not `⊤`. It is a **rule body**, used by both arithmetic
//! and comparison, and not a type function in its own right.
//!
//! It once was one, as a `CommonBase` bound each operand carried, so that resolving
//! one operand pulled the other's base. That is gone. As a *guard* it duplicated
//! what the result rule already does — a node's type is an `App` over both
//! operands, so materializing it runs the rule and rejects `1 + "a"` — and as a
//! *pull* it was compensating for defects elsewhere, since fixed.
//!
//! More importantly, "the operands share a base" is not what makes two values
//! addable; it is an artifact of a lattice with one numeric type. Under an
//! `Int + Float → Float` widening it is wrong in both directions: it rejects a
//! legal addition, and it names a result that is neither operand. Keeping the
//! decision *inside* [`TypeFn::Arithmetic`]'s rule is what lets it change without
//! touching anything else — the base sublattice being discrete is the only reason
//! a failed join is an error today rather than a widening.
//!
//! # Missing arguments
//!
//! An argument arrives as `None` when resolving it would re-enter the resolution
//! that is *already computing it*. That is not a scheduling artifact: resolution
//! pulls, so the only unavailable argument is a cyclic one, and a cycle has no
//! "later" at which more is known.
//!
//! Law 3 is what makes that a usable answer rather than a failure: reduced with an
//! argument missing, a rule answers from the rest and cannot claim more than it
//! would have with all of them. That is what keeps an unapplied `λ x → x > 1` at
//! result type `Bool` even though its operand is undetermined.
//!
//! Resolution being re-entrant is not something the retired `CommonBase` bound
//! introduced, and retiring it did not make the in-flight set idle: an argument is
//! resolved through the ordinary pipeline, which reaches other applications, so a
//! chain of them nests. `compact.rs`'s in-flight set and resolution memo are what
//! keep that bounded — removing the memo overflows the stack on a program as small
//! as `x := 7; for i in []: x += 1; x`.
//!
//! Every rule today satisfies law 3, so a missing argument is never itself a
//! failure. A future function that cannot — `FieldOf(ρ, 𝑘)` has nothing to say
//! without `ρ` — is a rule that *violates* law 3 and must therefore report the
//! cycle, as a new [`ReduceError`] variant introduced with it. It is deliberately
//! not here yet: today nothing could construct it, so nothing could test it.

use crate::ccl::ccl_utils::strip_refinements;
use crate::ccl::{Type, TypeFn};

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
}

/// Run `fun` on `args`, where `None` marks an argument whose resolution is already
/// in flight (see the module docs).
///
/// Returns `Err` only for a real conflict, which the caller that materialized the
/// type reports. A missing argument is not one: every rule today satisfies law 3.
pub fn reduce(fun: &TypeFn, args: &[Option<Type>]) -> Result<Type, ReduceError> {
    let available: Vec<&Type> = args.iter().flatten().collect();
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
        let out = reduce(&add(), &[Some(one.clone()), Some(one)]).expect("reduces");
        assert_eq!(out, int());
    }

    #[test]
    fn arithmetic_drops_refinements_and_keeps_the_base() {
        let out = reduce(
            &add(),
            &[
                Some(lit_singleton(&Lit::Int(1))),
                Some(lit_singleton(&Lit::Int(5))),
            ],
        )
        .expect("reduces");
        assert_eq!(out, int());
    }

    #[test]
    fn conflicting_bases_are_an_error() {
        let err = reduce(&add(), &[Some(int()), Some(Type::Base(BaseType::String))])
            .expect_err("Int and String share no base");
        assert!(matches!(err, ReduceError::NoCommonBase { .. }), "{err:?}");
    }

    /// Law 3: an argument the program has not determined weakens the check, not
    /// the answer. `\x -> x > 1` still has result type `Bool` with its operand
    /// undetermined, and `\x -> x + 1` still has result type `Int`.
    #[test]
    fn a_missing_argument_answers_from_the_rest() {
        let out = reduce(&add(), &[None, Some(lit_singleton(&Lit::Int(1)))]).expect("coarsens");
        assert_eq!(out, int());
    }

    /// And with nothing available it is the empty answer, not an error — the
    /// enclosing resolution may still have another way to see the position.
    #[test]
    fn all_arguments_missing_is_the_empty_answer() {
        let out = reduce(&add(), &[None, None]).expect("coarsens");
        assert_eq!(out, Type::Hole);
    }
}

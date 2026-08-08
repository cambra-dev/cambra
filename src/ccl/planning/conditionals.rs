//! Realizing a conditional collection: `Case{gᵢ → collᵢ}` → the gated union.
//!
//! The finite-Σ ≡ gated-union isomorphism, **performed**. Each arm is restricted by
//! its first-match path condition `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ` — a predicate constant in the
//! element, so it compiles through the ordinary `Restrict` path with no new operator
//! (`src/interpreter/design-operators.md`, "Constant-in-element predicates") — and the
//! restricted arms are unioned. Exactly one leg is non-empty, so the union's extent *is*
//! the selected domain.
//!
//! This lives in planning rather than `lambda_elim` for two reasons, and they are the
//! same reason twice. It is a logical-to-executable rewrite, which is what this pass is
//! for. And it *changes the representation*: a `Case` typed `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉` becomes a
//! union typed `Variant({𝑖: {𝐷ᵢ | π̂ᵢ}}) ⤇ 𝑉`, a tagged union. Those are different types —
//! the sum picks one branch, the tagged union has rows from every leg — and only the gates
//! make them agree, which no typing rule can check. Performing it *after* the type system
//! is done is what lets the two coexist without a `Fun(Data) <: Σ` bridge to relate them
//! (`src/ccl/design/type-inference.md`, "Only a term builds a sum").
//!
//! Only a **listing** witness kind can be realized here: the legs are the candidates, so
//! there have to be finitely many, named. A described kind (`Collection(𝑇)`, `List(𝑇)`)
//! reaches op-conversion still a Σ, and fails there — which is the correct signal, since
//! that is the case needing a runtime witness rather than a static realization
//! (`src/ccl/design/collections.md`, "Future work").

use crate::ccl::ccl_utils::{
    apply_primitive, flatten_trailing_value_case, peel_refinements, refine_with,
    synthesize_arm_predicate,
};
use crate::ccl::{BaseType, Builtin, Expr, FieldKey, Type, TypedExprNode, lambda_elim};

/// Rewrite every collection-valued value-`Case` in `expr` into its gated union.
pub(super) fn realize_conditional_collections(expr: &mut Expr) {
    // **Top-down.** An `elif` chain is a `Case` whose trailing arm is another `Case`, and
    // `flatten_trailing_value_case` collapses the chain into one N-choice partition —
    // which it can only do while the inner one is still a `Case`. Realizing children
    // first turns it into a union, the flatten silently no-ops, and the outer fan-out
    // ends up with a leg that is already a fan-out.
    realize_here(expr);
    expr.walk_children_mut(realize_conditional_collections);
    // A `box` whose **witness is determined** is erased here, not only the ones a
    // realized `Case` consumed. Left in place, the `Apply(_, Box)` hides its argument
    // from the rest of planning, so a `box`ed list literal never gets its `iterate`
    // marker and reaches op-conversion bare.
    //
    // Determined means the kind lists exactly *one* candidate: one possible witness is no
    // information, so nothing has to carry it — the same reading [`arm_domain`] takes. A
    // sum with two or more candidates that reaches here was **not** realized by a fan-out
    // above, so its witness is real and has to exist at runtime; erasing it would drop the
    // discriminant and silently compile the wrong program. Nothing can represent such a
    // witness yet (`src/ccl/design/collections.md`, "Future work"), so it is left standing
    // to be rejected by name at op-conversion — which is the correct failure, and the
    // signal that the runtime witness is what the program needs.
    *expr = unbox(std::mem::replace(expr, Expr::lit(crate::ccl::Lit::Unit)));
    repair_unboxed_argument(expr);
}

fn realize_here(expr: &mut Expr) {
    let TypedExprNode::Case {
        scrutinee: None,
        branches,
    } = &expr.node
    else {
        return;
    };
    if !branches.iter().all(|b| b.pattern.is_none()) {
        return;
    }
    let Some(value_ty) = collection_value_ty(&expr.ty) else {
        return;
    };
    let TypedExprNode::Case { branches, .. } =
        std::mem::replace(&mut expr.node, TypedExprNode::Lit(crate::ccl::Lit::Unit))
    else {
        unreachable!("matched a Case above")
    };
    // Flatten `elif` chains first, so a nested conditional collapses into one N-choice
    // fan-out rather than a union of unions.
    let branches = flatten_trailing_value_case(branches);

    let bool_ty = Type::Base(BaseType::Bool);
    let mut prior_guards: Vec<Expr> = Vec::new();
    let mut arms: Vec<Expr> = Vec::new();
    let mut tags: Vec<(FieldKey, Type)> = Vec::new();
    for b in branches {
        let Some(arm_dom) = arm_domain(&b.body.ty) else {
            // A multi-candidate arm is a genuinely nested conditional collection, and a
            // described one needs the runtime witness. Either way this rewrite does not
            // apply; leave the `Case` for op-conversion to reject by name.
            return;
        };
        let gate = synthesize_arm_predicate(&b.guard, &prior_guards);
        prior_guards.push(b.guard);
        let Ok(gate_pf) = lambda_elim::run(gate) else {
            return;
        };
        let gate_fn = apply_primitive(
            gate_pf,
            Builtin::Const,
            Type::fun(arm_dom.clone(), bool_ty.clone()),
        );
        let refined = refine_with(arm_dom, &gate_fn);
        tags.push((FieldKey::Index(tags.len()), refined.clone()));
        arms.push(unbox(b.body).with_ty(Type::data_fun(refined, value_ty.clone())));
    }

    // One branch denotes just that arm's collection — no union, and no witness left to
    // discriminate on.
    let realized = if arms.len() == 1 {
        arms.pop().expect("len == 1")
    } else {
        Expr::collection_union(arms).with_ty(Type::data_fun(Type::Variant(tags), value_ty))
    };
    // **Assert the pre-realization type.** The union is the executable form of a term the
    // rest of the tree still refers to as a sum, and every one of those mentions would
    // otherwise have to be rewritten — a chain that does not terminate, since the mentions
    // reach through composes, products and projections and are not all sums by the end.
    // Asserting the original type here means nothing above changes.
    //
    // [`TypedExprNode::Realize`] rather than [`TypedExprNode::Cast`] because the relation
    // is not a subtype one: the sum picks a branch, the tagged union has rows from every leg,
    // and only the gates reconcile them. A cast would be claiming an obligation that does
    // not hold; this asserts an isomorphism the rules cannot see, which is what it is for.
    //
    // Only where the `Case` *mentioned a witness*. A same-domain conditional types as a
    // plain collection, so its realization changes no mention and needs no assertion.
    //
    // A sum is the usual such type but not the only one: by the time a `Case` reaches here
    // inside a **predicate** it has been lambda-eliminated to its arrow view `𝑤 ⤇ 𝑉` — the
    // sum opened, the witness still named — and realizing that without an assertion shifts
    // the enclosing composition's domain from the witness to the union. The condition is
    // therefore about what the type *says*, not which constructor says it.
    let original = expr.ty.clone();
    let mentions_witness = matches!(peel_refinements(&original), Type::Sigma(_))
        || crate::ccl::ty::has_free_witness_ref(&original, &[]);
    *expr = if mentions_witness {
        Expr::new(TypedExprNode::Realize(Box::new(realized))).with_ty(original)
    } else {
        realized
    };
}

/// The shared element type of a collection-valued `Case`, or `None` when the `Case` is
/// not collection-valued (a scalar one, which `lambda_elim`'s C-form already handled).
fn collection_value_ty(ty: &Type) -> Option<Type> {
    match peel_refinements(ty) {
        Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
        Type::Sigma(s) => match &*s.body {
            // Factored: the body is the data function `w ⤇ 𝑉`, and `𝑉` is shared across
            // the fibers.
            Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
            // Unfactored — what `box`ing each arm builds, and what survives when nothing
            // consumes the collection (a conditional as the program's own result). Each
            // candidate carries its own element type, so realization needs them to agree;
            // the union it emits has one codomain. Element types that disagree — including
            // by a refinement, which is a fact true of one leg's elements and not the
            // other's — leave no one codomain to give the union, so realization declines
            // and op-conversion rejects the `Case` by name.
            Type::WitnessRef(_) => {
                let listed = s.kind().listed()?;
                let mut cods = listed.iter().map(|c| match peel_refinements(c) {
                    Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
                    _ => None,
                });
                let first = cods.next()??;
                cods.all(|c| c.as_ref() == Some(&first)).then_some(first)
            }
            _ => None,
        },
        _ => None,
    }
}

/// The domain a value-`Case` arm iterates — seeing through a **boxed** arm.
///
/// `box` is a type-level introduction with no runtime content: a Σ value is a witness
/// paired with a value, and for a one-candidate kind the witness is determined, so the
/// arm's runtime form is exactly its single candidate. Which arm the witness names is
/// decided by the fan-out being built here, not carried in the value.
///
/// This is *not* the singleton collapse readmitted. That collapse was a subtyping
/// equation, and removing it is what makes `box([1]) if c else box([2])` distinguishable
/// from `[1] if c else [2]`; the two types stay distinct. What is read here is the
/// **representation**, where a determined witness is no information at all.
///
/// The domain is returned with its refinements intact. They are the arm's own filters,
/// and this is the last place they can be read: the gate is layered on top of what comes
/// back here, and whatever that stack holds is what compiles to `Restrict`s. Peeling to
/// the head — never [`strip_refinements`](crate::ccl::ccl_utils), which erases at depth
/// and so reaches inside the sum's candidates — is what keeps them.
fn arm_domain(ty: &Type) -> Option<Type> {
    match peel_refinements(ty) {
        Type::Sigma(s) => match s.kind().listed() {
            Some([sole]) => peel_refinements(&s.instantiate_body(sole)).domain(),
            _ => None,
        },
        other => other.domain(),
    }
}

/// An arm with its `box` removed.
///
/// Realization erases the sum, so it must erase the term that introduced it: `box` is a
/// type-level introduction with no runtime content, and what the fan-out unions is the
/// underlying collection. Leaving the `Apply(_, Box)` in place would leave a node whose
/// own scheme still says `Σ`, disagreeing with the data-function type the realized arm
/// carries.
fn unbox(e: Expr) -> Expr {
    let TypedExprNode::Apply { function, argument } = &e.node else {
        return e;
    };
    if !matches!(function.node, TypedExprNode::Builtin(Builtin::Box)) {
        return e;
    }
    // Only a determined witness — one candidate — is erasable.
    match peel_refinements(&e.ty) {
        Type::Sigma(s) if matches!(s.kind().listed(), Some([_])) => (**argument).clone(),
        _ => e,
    }
}

/// Repair a consumer's parameter type after [`unbox`] erased its argument's `box`.
///
/// Only **unboxing** needs this, not realization: [`TypedExprNode::Realize`] keeps the
/// pre-realization type on the node, so a realized `Case` changes no mention above it.
/// Erasing a `box` does change one — the term drops from `Σ 𝑇 ∈ {𝑇ₓ}. 𝑇` to `𝑇ₓ` — and an
/// `Apply` names its argument's type a second time, in the function's own domain. A
/// consumer of a conditional collection is monomorphized at inference to *that*
/// collection, so `sum` over one carries `(Σ 𝑇 ∈ {𝑇ₓ}. 𝑇) ⇒ 𝑉`; the parameter follows the
/// argument or the tree stops type-checking.
///
/// Inert everywhere else: it fires only where the domain is still a sum and the argument
/// is not.
fn repair_unboxed_argument(expr: &mut Expr) {
    let TypedExprNode::Apply { function, argument } = &mut expr.node else {
        return;
    };
    if matches!(argument.ty, Type::Sigma(_)) {
        return;
    }
    if let Type::Fun { domain, .. } = &mut function.ty
        && matches!(**domain, Type::Sigma(_))
    {
        **domain = argument.ty.clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::infer_var::fresh_witness_binder_id;
    use crate::ccl::{Branch, Lit, Name};

    /// **Realization never changes a type that names the witness.** `Realize` asserts the
    /// pre-realization type precisely so that nothing above a realized `Case` has to be
    /// rewritten, and the mentions that would need rewriting are exactly the ones naming
    /// the witness — whether the naming type is the sum itself or the arrow view
    /// `𝑤 ⤇ 𝑉` a lambda-eliminated `Case` carries inside a predicate.
    ///
    /// Pinned as a unit test because the assertion is unobservable end-to-end today: the
    /// arrow-view shape reaches realization from a *passing* program (the mapping
    /// comprehension over a conditional), but nothing above it reads the type there yet.
    /// The consumer that does is the filtered comprehension, and it is blocked on
    /// per-leg restriction (`a_filter_over_a_conditional_source_is_dropped`). Without
    /// this, that path silently shifts the enclosing composition's domain from the
    /// witness to the realized union.
    #[test]
    fn realizing_an_arrow_view_case_keeps_the_witness_in_its_type() {
        let int = Type::Base(BaseType::Int);
        let w = fresh_witness_binder_id();
        let witness = Type::WitnessRef(w);
        // Two guarded arms, each a concrete collection — the shape a conditional
        // collection has once `box` is gone and the sum has been opened.
        let arm = |dom: usize| {
            Expr::new(TypedExprNode::Var(Name::from("xs")))
                .with_ty(Type::data_fun(Type::UIntRange(dom), int.clone()))
        };
        let guard = |b: bool| Expr::lit(Lit::Bool(b)).with_ty(Type::Base(BaseType::Bool));
        let case = TypedExprNode::Case {
            scrutinee: None,
            branches: vec![
                Branch {
                    pattern: None,
                    guard: guard(true),
                    body: arm(2),
                },
                Branch {
                    pattern: None,
                    guard: guard(true),
                    body: arm(3),
                },
            ],
        };
        // The **arrow view**: the sum opened, the witness still named. Not a `Type::Sigma`,
        // which is the whole point — the old condition tested the constructor.
        let arrow_view = Type::data_fun(witness.clone(), int.clone());
        let mut expr = Expr::new(case).with_ty(arrow_view.clone());

        realize_conditional_collections(&mut expr);

        assert_eq!(
            expr.ty, arrow_view,
            "realization must assert the pre-realization type, not the union's: {}",
            expr.ty
        );
        assert!(
            matches!(expr.node, TypedExprNode::Realize(_)),
            "the assertion is carried by a `Realize` node, got {:?}",
            expr.node
        );
    }
}

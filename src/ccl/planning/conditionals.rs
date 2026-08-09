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
    PredMemo, apply_primitive, flatten_trailing_value_case, peel_refinements, refine_with,
    synthesize_arm_predicate, walk_refined_predicates_mut,
};
use crate::ccl::{BaseType, Builtin, Expr, FieldKey, Type, TypedExprNode, lambda_elim};

/// Rewrite every collection-valued value-`Case` in `expr` into its gated union, and erase
/// every sum whose witness is **determined** — from the types as well as the terms.
pub(super) fn realize_conditional_collections(
    expr: &mut Expr,
) -> std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId> {
    let mut erased = std::collections::HashSet::new();
    let mut discharged = std::collections::HashSet::new();
    realize_and_unbox(
        expr,
        &mut erased,
        &PredMemo::new(),
        &mut std::collections::HashMap::new(),
        false,
        &mut discharged,
    );
    // **The other half of the erasure.** `unbox` removed the introduction from the *term*;
    // every type still says `Σ`. A type asserting an indeterminacy the term no longer has
    // is not a harmless leftover: the domain it presents at a consuming site is a witness,
    // which has no extent, so `planning::iterate` cannot build an iteration source for it
    // and drops the site's refinements with it (`tests/compilation_pipeline/sums.rs`).
    //
    // Safe under exactly the precondition `unbox` already checks — one candidate, so the
    // witness stands for a domain that is *known* — and applied to exactly the binders it
    // erased. That last part is what keeps a **realized** sum out of it: realization
    // consumes its arms' boxes without recording them, because the union it built has a
    // `Variant` domain and `Realize` asserts the sum over it deliberately. A same-domain
    // conditional is the case that proves the distinction is needed — one candidate, two
    // legs — and instantiating its assertion breaks it.
    if !erased.is_empty() {
        instantiate_erased_witnesses(expr, &erased, &PredMemo::new());
    }
    discharged
}

/// `owed` carries, per witness binder, the restriction a *consuming site above* placed on
/// that witness — `Σ σ ∈ 𝐾. ({σ | 𝑝} ⤇ 𝑉)`, the shape a filtered comprehension over a
/// conditional collection has. Realization is what materializes the witness, so it is what
/// discharges the restriction: [`realize_here`] gates each leg by `𝑝` rewritten to read
/// *that leg's arm*. Gathered on the way down, which is why the walk stays top-down.
///
/// `in_predicate` records that this subtree *is* a refinement predicate. A predicate may
/// carry no realized collection (`debug_assert_no_iteration_markers_in_type`: a gated union
/// needs the `iterate`/`restrict` a predicate is forbidden), so realization does not fire
/// there — the `Case` stays, and the per-leg discharge above is what replaces it, with a
/// plain arm rather than a union. Unboxing still runs: erasing a determined `box` adds
/// nothing to iterate.
fn realize_and_unbox(
    expr: &mut Expr,
    erased: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
    memo: &PredMemo<()>,
    owed: &mut std::collections::HashMap<
        crate::ccl::infer_var::WitnessBinderId,
        crate::ccl::Refinement,
    >,
    in_predicate: bool,
    discharged: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) -> bool {
    let mut changed = false;
    if let Some((binder, restriction)) = restriction_on_a_witness(&expr.ty) {
        eprintln!("PROBE owed {binder:?} from {}", expr.ty);
        owed.entry(binder).or_insert(restriction);
    }
    // **Top-down.** An `elif` chain is a `Case` whose trailing arm is another `Case`, and
    // `flatten_trailing_value_case` collapses the chain into one N-choice partition —
    // which it can only do while the inner one is still a `Case`. Realizing children
    // first turns it into a union, the flatten silently no-ops, and the outer fan-out
    // ends up with a leg that is already a fan-out.
    if !in_predicate {
        changed |= realize_here(expr, owed, discharged);
    }
    expr.walk_children_mut(|child| {
        changed |= realize_and_unbox(child, erased, memo, owed, in_predicate, discharged)
    });
    // **A refinement predicate is a term too, and it carries its own copy of the source.**
    // A filter looks the collection up at the index (`__elem ▷ src ▷ 𝑓`), so when `src` is
    // a `box` the introduction sits inside the predicate — somewhere the term walk above
    // never reaches, since predicates ride *type* slots. Left there it survives to
    // op-conversion, which has no `box` arm and rejects it as a non-combinator.
    expr.walk_type_slots_mut(|ty| {
        changed |= walk_refined_predicates_mut(ty, memo, &(), &mut |pred, memo| {
            realize_and_unbox(
                pred,
                erased,
                memo,
                &mut std::collections::HashMap::new(),
                true,
                &mut std::collections::HashSet::new(),
            )
        });
    });
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
    let (unboxed, erased_here) = unbox(
        std::mem::replace(expr, Expr::lit(crate::ccl::Lit::Unit)),
        Some(erased),
    );
    *expr = unboxed;
    changed |= erased_here;
    changed
}

/// Replace every sum on an **erased** binder by its single candidate, throughout `expr`'s
/// types — the type-level half of [`unbox`].
///
/// Reaches refinement *predicates* too, via [`walk_refined_predicates_mut`]: a predicate is
/// a term with type slots of its own, and a filter's predicate reads the very collection
/// whose sum is being erased, so a witness left there outlives every other mention.
fn instantiate_erased_witnesses(
    expr: &mut Expr,
    erased: &std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
    memo: &PredMemo<()>,
) {
    expr.walk_type_slots_mut(|ty| {
        walk_refined_predicates_mut(ty, memo, &(), &mut |pred, memo| {
            instantiate_erased_witnesses(pred, erased, memo);
            true
        });
        instantiate_erased_in_type(ty, erased);
    });
    expr.walk_children_mut(|child| instantiate_erased_witnesses(child, erased, memo));
}

fn instantiate_erased_in_type(
    ty: &mut Type,
    erased: &std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) {
    ty.walk_children_mut(|child| instantiate_erased_in_type(child, erased));
    if let Type::Sigma(sg) = ty
        && erased.contains(&sg.binder())
        && let Some([sole]) = sg.kind().listed()
    {
        // The candidate is this occurrence's own — the same sum is spelled both factored
        // and unfactored, and each instantiates against what it lists.
        let mut instantiated = sg.instantiate_body(sole);
        instantiate_erased_in_type(&mut instantiated, erased);
        *ty = instantiated;
    }
}

/// The restriction a consuming site placed **on a witness**, with the binder it names.
///
/// `Σ σ ∈ 𝐾. ({σ | 𝑝} ⤇ 𝑉)` — a filtered comprehension over a conditional collection. The
/// filter rides the witness rather than the candidates
/// (`src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness"), so it is a
/// fact about *whichever* domain the witness turns out to name, and nothing has compiled it
/// yet: the site cannot, having no extent for a witness.
fn restriction_on_a_witness(
    ty: &Type,
) -> Option<(
    crate::ccl::infer_var::WitnessBinderId,
    crate::ccl::Refinement,
)> {
    let Type::Sigma(sum) = peel_refinements(ty) else {
        return None;
    };
    let Type::Refinement(base, restriction) = sum.body.domain()? else {
        return None;
    };
    matches!(*base, Type::WitnessRef(w) if w == sum.binder())
        .then(|| (sum.binder(), restriction.clone()))
}

/// `predicate` with the conditional it reads replaced by `arm`.
///
/// A filter's predicate looks its collection up at the index (`__elem ▷ src ▷ 𝑓`), and `src`
/// is the whole conditional. Under leg `i` that conditional *is* `arm`, because the leg is
/// gated by `π̂ᵢ` — so reading the arm directly is the same fact, said in a form a predicate
/// may hold: a plain collection, needing no realization and therefore none of the
/// `iterate`/`restrict` machinery a predicate is forbidden to carry.
///
/// Identified by **type**, not by shape: the source is whatever names this sum, which the
/// witness binder says exactly. Matching structurally would have to guess which subterm is
/// the collection.
fn read_the_arm_instead(
    predicate: &Expr,
    binder: crate::ccl::infer_var::WitnessBinderId,
    kind: &crate::ccl::ty::TypeKind,
    arm: &Expr,
) -> Expr {
    // Two spellings name this sum, and inside a predicate it is usually the second: the
    // sum itself, or — once lambda elimination has opened it — the **arrow view** `𝑤 ⤇ 𝑉`,
    // which is a `Fun` whose domain is the witness. Matching only the constructor misses
    // the case that actually occurs.
    let names_this_sum = match peel_refinements(&predicate.ty) {
        // **By candidate list, not by binder.** The predicate holds its *own copy* of the
        // source, and that copy carries a **different** witness binder than the site's sum
        // — measured. The two print identically (`σ` names no binder) and compare unequal,
        // which is the α-invariance cost of naming the witness. Identity would be the
        // better key if the copies shared one; they do not, and until they do the candidate
        // list is what says "this is that sum".
        Type::Sigma(s) => s.kind() == kind,
        // Once lambda elimination has opened the sum, the source is its **arrow view**
        // `𝑤 ⤇ 𝑉` — a `Fun` on the witness, with no candidate list left to compare, so the
        // binder is all there is.
        other => matches!(
            other.domain().map(|d| peel_refinements(&d).clone()),
            Some(Type::WitnessRef(w)) if w == binder
        ),
    };
    if names_this_sum {
        return arm.clone();
    }
    let mut out = predicate.clone();
    out.walk_children_mut(|child| *child = read_the_arm_instead(child, binder, kind, arm));
    out
}

/// Returns whether this node was realized — load-bearing, not bookkeeping: a `Case` inside
/// a **refinement predicate** is rewritten through [`PredMemo::rebuild`], which *discards*
/// the rewrite when the caller reports no change. A realization that forgot to report would
/// be silently undone, leaving an unrealized `Case` in a predicate for op-conversion to
/// reject.
fn realize_here(
    expr: &mut Expr,
    owed: &std::collections::HashMap<
        crate::ccl::infer_var::WitnessBinderId,
        crate::ccl::Refinement,
    >,
    discharged: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) -> bool {
    let TypedExprNode::Case {
        scrutinee: None,
        branches,
    } = &expr.node
    else {
        return false;
    };
    if !branches.iter().all(|b| b.pattern.is_none()) {
        return false;
    }
    let Some(value_ty) = collection_value_ty(&expr.ty) else {
        return false;
    };
    let TypedExprNode::Case { branches, .. } =
        std::mem::replace(&mut expr.node, TypedExprNode::Lit(crate::ccl::Lit::Unit))
    else {
        unreachable!("matched a Case above")
    };
    // Flatten `elif` chains first, so a nested conditional collapses into one N-choice
    // fan-out rather than a union of unions.
    let branches = flatten_trailing_value_case(branches);

    // Which sum this `Case` realizes, so the restriction owed on that witness can be found.
    let (binder, kind) = match peel_refinements(&expr.ty) {
        Type::Sigma(s) => (s.binder(), s.kind().clone()),
        _ => (
            crate::ccl::infer_var::WitnessBinderId::UNBOUND,
            crate::ccl::ty::TypeKind::Enumerated(Vec::new()),
        ),
    };
    let bool_ty = Type::Base(BaseType::Bool);
    let mut prior_guards: Vec<Expr> = Vec::new();
    let mut arms: Vec<Expr> = Vec::new();
    let mut tags: Vec<(FieldKey, Type)> = Vec::new();
    for b in branches {
        let Some(arm_dom) = arm_domain(&b.body.ty) else {
            // A multi-candidate arm is a genuinely nested conditional collection, and a
            // described one needs the runtime witness. Either way this rewrite does not
            // apply; leave the `Case` for op-conversion to reject by name.
            return false;
        };
        let gate = synthesize_arm_predicate(&b.guard, &prior_guards);
        prior_guards.push(b.guard);
        let Ok(gate_pf) = lambda_elim::run(gate) else {
            return false;
        };
        let gate_fn = apply_primitive(
            gate_pf,
            Builtin::Const,
            Type::fun(arm_dom.clone(), bool_ty.clone()),
        );
        let refined = refine_with(arm_dom, &gate_fn);
        let arm = unbox(b.body, None).0;
        // **Discharge the site's restriction into this leg.** Realization materializes the
        // witness, so it owes what the consuming site placed on it — and the leg is the one
        // place that restriction can be said *denotationally*, because here the conditional
        // has become a single arm.
        let refined = match owed.get(&binder) {
            Some(restriction) => Type::Refinement(
                Box::new(refined),
                crate::ccl::Refinement::born(std::rc::Rc::new(read_the_arm_instead(
                    &restriction.predicate,
                    binder,
                    &kind,
                    &arm,
                ))),
            ),
            None => refined,
        };
        if owed.contains_key(&binder) {
            discharged.insert(binder);
        }
        tags.push((FieldKey::Index(tags.len()), refined.clone()));
        arms.push(arm.with_ty(Type::data_fun(refined, value_ty.clone())));
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
    true
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
///
/// `erased` records the binder whose sum this erased, so
/// [`instantiate_erased_witnesses`] can finish the job in the types. Realization passes
/// `None` for the arms it consumes: it materializes those witnesses itself, as the gated
/// union, and `Realize` asserts the sum over a `Variant` domain on purpose — instantiating
/// that assertion would contradict the term it is asserting over.
fn unbox(
    e: Expr,
    erased: Option<&mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>>,
) -> (Expr, bool) {
    let TypedExprNode::Apply { function, argument } = &e.node else {
        return (e, false);
    };
    if !matches!(function.node, TypedExprNode::Builtin(Builtin::Box)) {
        return (e, false);
    }
    // Only a determined witness — one candidate — is erasable.
    match peel_refinements(&e.ty) {
        Type::Sigma(s) if matches!(s.kind().listed(), Some([_])) => {
            if let Some(erased) = erased {
                erased.insert(s.binder());
            }
            // Reported rather than inferred from the recorded set: the *same* binder can be
            // erased at two occurrences, and a set that already holds it does not grow.
            ((**argument).clone(), true)
        }
        _ => (e, false),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::infer_var::fresh_witness_binder_id;
    use crate::ccl::ty::{SigmaType, TypeKind, Witness};
    use crate::ccl::{Branch, Lit, Name};

    /// **A `box` inside a refinement predicate is erased, and the erasure sticks.**
    ///
    /// A filter's predicate looks its collection up at the index (`__elem ▷ src ▷ 𝑓`), so
    /// when `src` is boxed the introduction sits inside the predicate — a term riding a
    /// *type* slot, which no term walk reaches. Both walks descend into predicates for that
    /// reason, and predicates are rewritten through [`PredMemo::rebuild`], which
    /// **discards** the rewrite unless the caller reports a change. So the report is
    /// load-bearing: erasing without reporting leaves the original predicate in place, and
    /// a `box` reaches op-conversion, which has no arm for it.
    ///
    /// A `Case` in the same position is deliberately *not* realized — the gated union it
    /// would become needs `iterate`/`restrict`, which a predicate may not carry
    /// (`debug_assert_no_iteration_markers_in_type`). The per-leg discharge replaces it with
    /// a plain arm instead. Both halves are asserted here, since they are one decision.
    #[test]
    fn a_box_inside_a_refinement_predicate_is_erased_but_a_case_is_left_alone() {
        let int = Type::Base(BaseType::Int);
        let coll = Type::data_fun(Type::UIntRange(2), int.clone());
        // `Σ σ ∈ {coll}. σ` — one candidate, so the witness is determined and erasable.
        let w = fresh_witness_binder_id();
        let sum = || {
            Type::Sigma(Box::new(SigmaType::bound(
                Witness::bound_to(w, TypeKind::Enumerated(vec![coll.clone()])),
                Type::WitnessRef(w),
            )))
        };
        let boxed = Expr::apply(
            Expr::new(TypedExprNode::Var(Name::from("xs"))).with_ty(coll.clone()),
            Expr::builtin(Builtin::Box).with_ty(Type::fun(coll.clone(), sum())),
        )
        .with_ty(sum());
        let guard = |b: bool| Expr::lit(Lit::Bool(b)).with_ty(Type::Base(BaseType::Bool));
        let case = Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: vec![
                Branch {
                    pattern: None,
                    guard: guard(true),
                    body: Expr::new(TypedExprNode::Var(Name::from("ys"))).with_ty(coll.clone()),
                },
                Branch {
                    pattern: None,
                    guard: guard(true),
                    body: Expr::new(TypedExprNode::Var(Name::from("zs"))).with_ty(coll.clone()),
                },
            ],
        })
        .with_ty(coll.clone());
        // One predicate holding both.
        let pred = Expr::new(TypedExprNode::Tuple(vec![boxed, case])).with_ty(int.clone());
        let ty = Type::Refinement(
            Box::new(Type::UIntRange(2)),
            crate::ccl::Refinement::born(std::rc::Rc::new(pred)),
        );
        let mut expr =
            Expr::new(TypedExprNode::Var(Name::from("site"))).with_ty(Type::data_fun(ty, int));

        realize_conditional_collections(&mut expr);

        let Type::Fun { domain, .. } = &expr.ty else {
            panic!("expected a function type, got {}", expr.ty);
        };
        let Type::Refinement(_, refinement) = &**domain else {
            panic!("expected the refinement to survive, got {domain}");
        };
        let rendered = crate::ccl::symbolic::symbolic(&refinement.predicate);
        assert!(
            !rendered.contains("box"),
            "the predicate's `box` was erased and then discarded: {rendered}"
        );
        assert!(
            rendered.contains('→'),
            "the predicate's `Case` must be left for the per-leg discharge: {rendered}"
        );
    }

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

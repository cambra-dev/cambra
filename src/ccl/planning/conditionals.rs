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
    PredMemo, apply_primitive, flatten_trailing_value_case, make_cast, peel_refinements,
    refine_with, synthesize_arm_predicate, walk_refined_predicates, walk_refined_predicates_mut,
};
use crate::ccl::{
    BaseType, BinOpKind, Builtin, Expr, FieldKey, LogicKind, Type, TypedExprNode, lambda_elim,
};

/// Rewrite every collection-valued value-`Case` in `expr` into its gated union, and erase
/// every sum whose witness is **determined** — from the types as well as the terms.
pub(super) fn realize_conditional_collections(
    expr: &mut Expr,
) -> std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId> {
    let mut erased = std::collections::HashSet::new();
    let mut discharged = std::collections::HashSet::new();
    bring_restrictions_under_their_sites_binder(expr);
    inline_restricted_conditionals(expr);
    realize_and_unbox(expr, &mut erased, &PredMemo::new(), false, &mut discharged);
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

/// Give every consumer of a **restricted** conditional collection its own copy of it,
/// dropping the binding that shared it.
///
/// Realization is demand-directed: the legs it builds carry the consuming site's filter,
/// gated arm by arm ([`realize`]). So the legs belong to *one* consumer's demand, and a
/// binding consumed twice has one set of legs and two demands. Two filters cannot both gate
/// one shared union, and an unfiltered consumer of the same binding must not be handed the
/// other's filter at all. Spelled inline, with a conditional per consumer, both programs
/// already compile; this is that spelling, performed.
///
/// It also puts the `Case` back *below* the site that restricts it. The restriction rides
/// the consuming site's type, so a `Case` in the binding is reached before the demand it
/// owes is known — an ordering no walk direction fixes, since the binding precedes the body
/// by scope, not by traversal.
///
/// Only conditionals someone restricts are inlined. An unrestricted one owes nothing, so
/// sharing costs nothing and duplicating it would only duplicate the union.
fn inline_restricted_conditionals(expr: &mut Expr) {
    let mut restricted = std::collections::HashSet::new();
    collect_restricted_witnesses(expr, &mut std::collections::HashSet::new(), &mut restricted);
    if !restricted.is_empty() {
        inline_restricted(expr, &restricted);
    }
}

fn collect_restricted_witnesses(
    expr: &Expr,
    visited: &mut std::collections::HashSet<crate::ccl::ty::PredicateId>,
    restricted: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) {
    if let Some((binder, _)) = restriction_on_a_witness(&expr.ty) {
        restricted.insert(binder);
    }
    // A filter's predicate reads the collection it filters, so a restricted sum is named
    // inside predicates as well as on terms.
    expr.walk_type_slots(|ty| {
        walk_refined_predicates(ty, visited, &mut |pred, visited| {
            collect_restricted_witnesses(pred, visited, restricted);
        });
    });
    expr.walk_children(|child| collect_restricted_witnesses(child, visited, restricted));
}

fn inline_restricted(
    expr: &mut Expr,
    restricted: &std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) {
    expr.walk_children_mut(|child| inline_restricted(child, restricted));
    let TypedExprNode::Let { bound_expr, .. } = &expr.node else {
        return;
    };
    let is_conditional_collection = matches!(
        bound_expr.node,
        TypedExprNode::Case {
            scrutinee: None,
            ..
        }
    ) && collection_value_ty(&bound_expr.ty).is_some();
    if !is_conditional_collection
        || !witness_named_by(&bound_expr.ty).is_some_and(|w| restricted.contains(&w))
    {
        return;
    }
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = std::mem::replace(&mut expr.node, TypedExprNode::Lit(crate::ccl::Lit::Unit))
    else {
        unreachable!("matched a Let above")
    };
    // Substitution reaches type slots and their predicates, which is required rather than
    // thorough: the filter's predicate holds its own read of the binding, and a copy left
    // naming a variable this rewrite just deleted would outlive it.
    *expr = lambda_elim::substitute(*body, &binding.name, &bound_expr);
}

/// What a consuming site placed on a witness, and the sum it said it about.
///
/// The candidate list travels with the predicate because it is the only usable key for
/// finding the *same* sum inside that predicate: a predicate holds its own copy of the
/// source, and the copy carries a different witness binder (see [`read_the_arm_instead`]).
#[derive(Clone)]
struct Owed {
    kind: crate::ccl::ty::TypeKind,
    restriction: crate::ccl::Refinement,
}

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
    in_predicate: bool,
    discharged: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) -> bool {
    let mut changed = false;
    // **A conditional inside a predicate is left entirely alone** — not only unrealized,
    // but un-rewritten. It is a placeholder: the per-leg discharge replaces the whole
    // predicate with one reading that leg's arm ([`read_the_arm_instead`]), so nothing
    // inside this copy survives to be compiled. Descending would only *break* it, and does:
    // erasing the `box` off each arm leaves a `Case` joining collections over distinct
    // domains, which is exactly the type error `box` exists to prevent. Nothing on the
    // normal path notices — the pass-boundary typecheck does not descend into predicates —
    // so it shows up only under the `deep-typecheck` feature.
    if in_predicate && collection_value_ty(&expr.ty).is_some() && is_value_case(expr) {
        return changed;
    }
    // **Top-down.** An `elif` chain is a `Case` whose trailing arm is another `Case`, and
    // `flatten_trailing_value_case` collapses the chain into one N-choice partition —
    // which it can only do while the inner one is still a `Case`. Realizing children
    // first turns it into a union, the flatten silently no-ops, and the outer fan-out
    // ends up with a leg that is already a fan-out.
    if !in_predicate {
        changed |= realize(expr, discharged);
    }
    expr.walk_children_mut(|child| {
        changed |= realize_and_unbox(child, erased, memo, in_predicate, discharged)
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

/// α-convert each site's restriction onto that site's **own** witness binder.
///
/// A filter's predicate holds its own copy of the source, and inference types that copy
/// independently — so the sum inside the predicate carries a *different* binder than the sum
/// on the site, for one value. The two print identically (`σ` names no binder) and compare
/// unequal, so the predicate is ill-typed against its own parameter: `__elem : σ₄` applied to
/// a collection over `σ₇`. Nothing on the normal path looks — the pass-boundary typecheck
/// does not descend into predicates — so it surfaces only under `deep-typecheck`, at the
/// point planning compiles the predicate.
///
/// A binder is bound, so renaming one changes nothing about the type
/// ([`SigmaType::rename_binder`](crate::ccl::ty::SigmaType::rename_binder)); what it changes
/// is what the *rest* of the type may name. The predicate rides the domain under the site's
/// binder, so a sum in it describing the same value belongs under that binder — the same
/// reading that brings a variable's sum-typed lower bounds under one binder before anything
/// opens them.
///
/// Whole-tree rather than per-site because a predicate rides **several** type slots (the
/// site's own, a `Cast` target, the consumer's parameter) as one shared `Rc`, and they must
/// agree: renaming the site's copy alone leaves the consumer's parameter naming the binder
/// that was renamed away.
///
/// Sameness is keyed on the **candidate list**, the only key available across copies, so a
/// copy claimed by two different sites is left alone rather than assigned to either. Witness
/// identity minted at the value is what would retire the key; until then it is the same one
/// [`read_the_arm_instead`] matches on, and this makes it agree with identity afterwards.
fn bring_restrictions_under_their_sites_binder(expr: &mut Expr) {
    let mut renames = std::collections::HashMap::new();
    let mut claimed_twice = std::collections::HashSet::new();
    collect_renames(expr, &mut renames, &mut claimed_twice);
    renames.retain(|copy, _| !claimed_twice.contains(copy));
    if !renames.is_empty() {
        rename_witnesses(expr, &renames, &PredMemo::new());
    }
}

fn collect_renames(
    expr: &Expr,
    renames: &mut std::collections::HashMap<
        crate::ccl::infer_var::WitnessBinderId,
        crate::ccl::infer_var::WitnessBinderId,
    >,
    claimed_twice: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) {
    if let Some((binder, owed)) = restriction_on_a_witness(&expr.ty) {
        let mut copies = std::collections::HashSet::new();
        same_sum_binders(&owed.restriction.predicate, &owed.kind, binder, &mut copies);
        for copy in copies {
            if *renames.entry(copy).or_insert(binder) != binder {
                claimed_twice.insert(copy);
            }
        }
    }
    expr.walk_children(|child| collect_renames(child, renames, claimed_twice));
}

/// The binders of every sum in `expr`'s types that lists exactly `kind`'s candidates and is
/// **not** already `binder` — the copies of one sum, minted apart.
fn same_sum_binders(
    expr: &Expr,
    kind: &crate::ccl::ty::TypeKind,
    binder: crate::ccl::infer_var::WitnessBinderId,
    out: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) {
    fn in_type(
        ty: &Type,
        kind: &crate::ccl::ty::TypeKind,
        binder: crate::ccl::infer_var::WitnessBinderId,
        out: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
    ) {
        if let Type::Sigma(s) = ty
            && s.kind() == kind
            && s.binder() != binder
        {
            out.insert(s.binder());
        }
        ty.walk_children(|child| in_type(child, kind, binder, out));
    }
    expr.walk_type_slots(|ty| in_type(ty, kind, binder, out));
    expr.walk_children(|child| same_sum_binders(child, kind, binder, out));
}

fn rename_witnesses(
    expr: &mut Expr,
    renames: &std::collections::HashMap<
        crate::ccl::infer_var::WitnessBinderId,
        crate::ccl::infer_var::WitnessBinderId,
    >,
    memo: &PredMemo<()>,
) {
    fn in_type(
        ty: &mut Type,
        renames: &std::collections::HashMap<
            crate::ccl::infer_var::WitnessBinderId,
            crate::ccl::infer_var::WitnessBinderId,
        >,
    ) {
        ty.walk_children_mut(|child| in_type(child, renames));
        match ty {
            Type::WitnessRef(w) => {
                if let Some(to) = renames.get(w) {
                    *ty = Type::WitnessRef(*to);
                }
            }
            // The body's occurrences were renamed by the walk above, so the binder itself is
            // all that is left to move.
            Type::Sigma(s) => {
                if let Some(to) = renames.get(&s.binder()) {
                    *ty = Type::Sigma(Box::new(crate::ccl::ty::SigmaType::bound(
                        crate::ccl::ty::Witness::bound_to(*to, s.kind().clone()),
                        (*s.body).clone(),
                    )));
                }
            }
            _ => {}
        }
    }
    expr.walk_type_slots_mut(|ty| {
        walk_refined_predicates_mut(ty, memo, &(), &mut |pred, memo| {
            rename_witnesses(pred, renames, memo);
            true
        });
        in_type(ty, renames);
    });
    expr.walk_children_mut(|child| rename_witnesses(child, renames, memo));
}

/// The restriction a consuming site placed **on a witness**, with the binder it names.
///
/// `Σ σ ∈ 𝐾. ({σ | 𝑝} ⤇ 𝑉)` — a filtered comprehension over a conditional collection. The
/// filter rides the witness rather than the candidates
/// (`src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness"), so it is a
/// fact about *whichever* domain the witness turns out to name, and nothing has compiled it
/// yet: the site cannot, having no extent for a witness.
/// Whether `ty` names `binder` anywhere. Binder ids are globally unique, so an occurrence is
/// this binder's wherever it sits.
fn mentions_witness(ty: &Type, binder: crate::ccl::infer_var::WitnessBinderId) -> bool {
    if matches!(ty, Type::WitnessRef(w) if *w == binder) {
        return true;
    }
    let mut found = false;
    ty.walk_children(|child| found |= mentions_witness(child, binder));
    found
}

fn restriction_on_a_witness(ty: &Type) -> Option<(crate::ccl::infer_var::WitnessBinderId, Owed)> {
    let Type::Sigma(sum) = peel_refinements(ty) else {
        return None;
    };
    let Type::Refinement(base, restriction) = sum.body.domain()? else {
        return None;
    };
    // **Mentioning the witness, not being it.** With one generator the consuming site is
    // indexed by the witness itself and the refinement lands on `{σ | 𝑝}`. A second generator
    // indexes it by a *product*, so the same filter lands on `{(σ, 𝐷) | 𝑝}` — the witness is
    // one position of the domain rather than the whole of it. It is the same restriction,
    // owed by the same witness, and reading only the whole leaves a filter uncompiled.
    mentions_witness(&base, sum.binder()).then(|| {
        (
            sum.binder(),
            Owed {
                kind: sum.kind().clone(),
                restriction: restriction.clone(),
            },
        )
    })
}

/// The witness a collection type names, in **either spelling**.
///
/// A `Case` that reaches realization inside a composition (`case ≫ 𝑓` — what a mapping
/// comprehension body builds) does not carry the sum: the composition opened it, and what
/// is left on the `Case` is the **arrow view** `σ ⤇ 𝑉`, a data function whose domain is the
/// witness. Both spellings name the same sum and both owe the same restriction, so reading
/// the binder off only the `Σ` silently skips the discharge on the composed shape and
/// leaves the site's filter uncompiled.
fn witness_named_by(ty: &Type) -> Option<crate::ccl::infer_var::WitnessBinderId> {
    match peel_refinements(ty) {
        Type::Sigma(sum) => Some(sum.binder()),
        other => match peel_refinements(&other.domain()?) {
            Type::WitnessRef(w) => Some(*w),
            _ => None,
        },
    }
}

/// Instantiate `binder` to `candidate` throughout a term's **types**, predicates included.
fn strip_the_instantiated_binder(ty: &mut Type, binder: crate::ccl::infer_var::WitnessBinderId) {
    ty.walk_children_mut(|child| strip_the_instantiated_binder(child, binder));
    if let Type::Sigma(sum) = ty
        && sum.binder() == binder
    {
        *ty = (*sum.body).clone();
    }
}

fn instantiate_witness_in_types(
    expr: &mut Expr,
    binder: crate::ccl::infer_var::WitnessBinderId,
    candidate: &Type,
    memo: &PredMemo<()>,
) {
    expr.walk_type_slots_mut(|ty| {
        walk_refined_predicates_mut(ty, memo, &(), &mut |pred, memo| {
            instantiate_witness_in_types(pred, binder, candidate, memo);
            true
        });
        *ty = crate::ccl::ty::instantiate_witness(ty, binder, candidate);
        // **And drop the binder it bound.** Substituting the occurrences leaves the sum
        // quantifying a witness nothing mentions — a wrapper asserting a choice already
        // made. It is not inert: the next realization reads the *outermost* binder to know
        // which conditional it is realizing, and a vacuous one hides the sum below it, so a
        // second conditional source is never reached.
        strip_the_instantiated_binder(ty, binder);
    });
    expr.walk_children_mut(|child| instantiate_witness_in_types(child, binder, candidate, memo));
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
    copies: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
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
        //
        // **Either spelling of the candidates counts.** `Σ 𝜎 ∈ {𝐷ᵢ ⤇ 𝑉}. 𝜎` and
        // `Σ 𝜎 ∈ {𝐷ᵢ}. 𝜎 ⤇ 𝑉` are one sum viewed two ways
        // ([`SigmaType::factored_view`]), and which one a copy carries depends on where its
        // position was materialized — so comparing the listing verbatim would answer "a
        // different sum" for the same one.
        Type::Sigma(s) => s.kind() == kind || s.factored_view().is_some_and(|f| f.kind() == kind),
        // Once lambda elimination has opened the sum, the source is its **arrow view**
        // `𝑤 ⤇ 𝑉` — a `Fun` on the witness, with no candidate list left to compare, so the
        // binder is all there is.
        other => matches!(
            other.domain().map(|d| peel_refinements(&d).clone()),
            Some(Type::WitnessRef(w)) if w == binder
        ),
    };
    if names_this_sum {
        if let Type::Sigma(s) = peel_refinements(&predicate.ty) {
            copies.insert(s.binder());
        }
        return arm.clone();
    }
    let mut out = predicate.clone();
    out.walk_children_mut(|child| *child = read_the_arm_instead(child, binder, kind, arm, copies));
    out
}

/// A **value**-`Case` — guardless arms selecting a value, as opposed to a pattern `match`.
/// The form realization rewrites, and the form a filter's predicate carries a copy of.
fn is_value_case(expr: &Expr) -> bool {
    matches!(
        &expr.node,
        TypedExprNode::Case {
            scrutinee: None,
            branches,
        } if branches.iter().all(|b| b.pattern.is_none())
    )
}

/// Realize the conditional collections a site chooses between, as its gated union.
///
/// **Where the union goes.** It is an iteration *source*: each leg carries a refined domain
/// that [`super::iterate::wrap_with_iterate`] turns into `iterate ▷ (π̂ᵢ ▷ restrict) ≫ armᵢ`.
/// So it has to sit where a source belongs — at the head of the pipeline consuming it. That
/// is the node whose type carries the choice, which is the outermost `Σ` binding the witness:
/// rewriting the `Case` in place puts the union at the head only when the conditional is the
/// sole generator, and with a second the head moves above it to the product iterate, where a
/// source stranded mid-chain is what op-conversion rejects (`zip requires an input operator`).
/// The chain between site and `Case` is copied into every leg — under leg `i` the conditional
/// *is* `armᵢ` and the witness *is* that arm's domain, so a leg is that substitution made
/// everywhere at once, including in the filter predicates that hold their own read of the
/// source. That is also what discharges a consuming site's restriction: inside the leg the
/// fact is *sayable*, a predicate being allowed to hold a plain arm but not a gated union.
///
/// **All of the site's witnesses at once.** Two conditional generators nest two sums over one
/// product domain — `Σ σ₄ ∈ 𝐾₄. Σ σ₇ ∈ 𝐾₇. ((σ₄, σ₇) ⤇ 𝑉)` — and that is one site with two
/// choices on it, not a site inside a site. Realizing them one at a time nests the unions, and
/// a nested union is wrong in the *term*, not just in the type it records: an outer leg's gate
/// is carried as a refinement on its domain, and the term-level `restrict` is emitted only
/// where that domain heads an iteration. Wrapping the inner union — which is not an iteration
/// site — silently drops the outer gate, leaving two legs live at once where exactly one may
/// be. So the legs are the **combinations**: one per tuple of arms, gated by the conjunction of
/// their path conditions, indexed by the product of their arms' domains. That is the same
/// finite-Σ ≡ gated-union isomorphism, stated for a product of witnesses rather than for one —
/// and it is flat, which is what the term already is, since [`Expr::collection_union`] flattens.
///
/// **A conditional with no witness is realized at itself**, and can be nowhere else: arms over
/// one domain type as a plain collection, so no enclosing type mentions the choice and there is
/// no binder to find it by. It is the degenerate case rather than a second algorithm — one
/// choice, the site *is* the `Case`, and substituting the arm for the conditional leaves the
/// arm. Nothing above changes, so no [`TypedExprNode::Realize`] asserts anything.
///
/// Returns whether this node was realized — load-bearing, not bookkeeping: a `Case` inside a
/// **refinement predicate** is rewritten through [`PredMemo::rebuild`], which *discards* the
/// rewrite when the caller reports no change. A realization that forgot to report would be
/// silently undone, leaving an unrealized `Case` in a predicate for op-conversion to reject.
fn realize(
    expr: &mut Expr,
    discharged: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) -> bool {
    let Some(value_ty) = collection_value_ty(&expr.ty) else {
        return false;
    };
    // Each witness's own fan-out, in the order the site's binders nest. A witness whose
    // `Case` is not below this node cannot be realized here, and realizing only the others
    // would rebuild the nesting the combinations exist to avoid — so the site declines as a
    // whole, and op-conversion rejects the surviving sum by name.
    let witnesses = witnesses_named_by(&expr.ty);
    let choices: Vec<Vec<ArmChoice>> = if witnesses.is_empty() {
        if !is_value_case(expr) {
            return false;
        }
        let TypedExprNode::Case { branches, .. } = &expr.node else {
            unreachable!("is_value_case matched a Case")
        };
        match arm_choices(branches.clone(), None) {
            Some(arms) => vec![arms],
            None => return false,
        }
    } else {
        let mut per_witness = Vec::new();
        for (binder, kind) in &witnesses {
            let Some(branches) = conditional_below(expr, *binder) else {
                return false;
            };
            match arm_choices(branches, Some((*binder, kind.clone()))) {
                Some(arms) => per_witness.push(arms),
                None => return false,
            }
        }
        per_witness
    };

    let original = expr.ty.clone();
    let bool_ty = Type::Base(BaseType::Bool);
    let mut legs: Vec<Expr> = Vec::new();
    let mut tags: Vec<(FieldKey, Type)> = Vec::new();
    for combination in combinations(&choices) {
        // **The gate is the conjunction**, built while still pointful and eliminated once:
        // the leg is the one where *every* witness took the arm this combination names, and
        // each path condition is constant in the element, so their conjunction is too.
        let Some(gate) = combination.iter().map(|c| c.gate.clone()).reduce(|acc, g| {
            Expr::binop(acc, BinOpKind::BoolLogic(LogicKind::And), g).with_ty(bool_ty.clone())
        }) else {
            return false;
        };
        let Ok(gate_pf) = lambda_elim::run(gate) else {
            return false;
        };
        let mut leg = expr.clone();
        for choice in &combination {
            let Some((binder, kind)) = &choice.witness else {
                // No witness: the site is the `Case` itself, so the substitution is the arm.
                leg = choice.arm.clone();
                continue;
            };
            if !replace_the_conditional(&mut leg, *binder, &choice.arm) {
                return false;
            }
            // **A filter's predicate holds its own read of the source**, so the conditional is
            // in there too and a leg whose predicate still tests the *whole* conditional is not
            // that leg. Rewritten before the witness is instantiated, because the match that
            // finds the source in a predicate reads the witness it is indexed by.
            let memo = PredMemo::new();
            // A predicate's copy of the source carries its **own** witness binder, so the
            // copies it names have to be instantiated as well as the site's. They are
            // collected here rather than looked up, because the rewrite below erases the
            // sum that carried the copy's binder: after it, a bare `Type::WitnessRef` is
            // all that is left and it names a binder and nothing else.
            let mut copies = std::collections::HashSet::from([*binder]);
            leg.walk_type_slots_mut(|ty| {
                walk_refined_predicates_mut(ty, &memo, &(), &mut |pred, _| {
                    *pred = read_the_arm_instead(pred, *binder, kind, &choice.arm, &mut copies);
                    true
                });
            });
            for copy in &copies {
                instantiate_witness_in_types(&mut leg, *copy, &choice.dom, &PredMemo::new());
            }
        }
        // The gate rides the **leg's** domain, not any one arm's: with a second generator the
        // leg is indexed by a product, and the gate is constant in the element either way.
        let Some(leg_dom) = leg.ty.domain() else {
            return false;
        };
        let gate_fn = apply_primitive(
            gate_pf,
            Builtin::Const,
            Type::fun(leg_dom.clone(), bool_ty.clone()),
        );
        let refined = refine_with(leg_dom, &gate_fn);
        tags.push((FieldKey::Index(tags.len()), refined.clone()));
        // The gate rides a **`cast`** whose target refines the leg's domain rather than
        // being written onto the leg's type in place. Two things read it, and neither
        // would find a bare retyping: the post-planning consistency wall re-derives a
        // node's type from its children, where a data domain is invariant and an added
        // refinement is a mismatch; and `insert_iterate_markers` reifies a domain
        // refinement into a `restrict` only at a term that carries one. A refinement no
        // term carries is one nothing downstream is obliged to honour.
        let gated = matches!(refined, Type::Refinement(_, _));
        let leg_ty = Type::fun_like(&leg.ty, refined, value_ty.clone());
        // A **vacuously true** gate refines nothing (`refine_with` drops it), so there is
        // no refinement for a cast to carry and the leg is its arm at its own type. One
        // arm is the case: its path condition is the trailing `true`.
        legs.push(if gated {
            make_cast(leg, leg_ty.clone()).with_ty(leg_ty)
        } else {
            leg.with_ty(leg_ty)
        });
    }
    if legs.is_empty() {
        return false;
    }
    for (binder, _) in &witnesses {
        discharged.insert(*binder);
    }
    // Every witness of the site is instantiated in its legs, so the union is a plain data
    // function over the flat `Variant` of their domains — no binder is left for it to carry.
    debug_assert!(
        !matches!(peel_refinements(&legs[0].ty), Type::Sigma(_)),
        "a realized leg quantifies a witness the site did not name"
    );
    // **Which union, decided by whether the site names a witness.** A site that does is a
    // conditional between *distinct* domains: its legs live over different index sets, so
    // combining them is a `Copair` over the `Variant` of those sets, and the sum it realizes
    // is asserted back on top. A site that does not is a same-domain conditional: every leg
    // is a gated restriction of one domain `𝐷`, first-match keeps their supports disjoint,
    // and the union *is* `𝐷 ⤇ 𝑉` — a [`TypedExprNode::DisjointJoin`], typed at the site's
    // own type. A coproduct domain there would claim the legs live over distinct index sets,
    // which every consumer's `𝐷`-shaped demand would then have to undo
    // (`src/ccl/design/ir.md`, "`Copair` and `DisjointJoin` — two collection-combining
    // operations, not one").
    let mentions_witness = !witnesses.is_empty() || original.is_witness_indexed();
    // One leg denotes just that arm's collection — no union, and no witness to discriminate
    // on. It keeps its gate, which rides its domain either way.
    let realized = if legs.len() == 1 {
        legs.pop().expect("len == 1")
    } else if mentions_witness {
        let union_ty = Type::fun_like(&legs[0].ty, Type::variant(tags), value_ty);
        Expr::copair(legs).with_ty(union_ty)
    } else {
        Expr::disjoint_join(legs).with_ty(original.clone())
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
    // Only where the site *mentioned a witness*. A same-domain conditional types as a plain
    // collection, so its realization changes no mention and needs no assertion.
    //
    // A sum is the usual such type but not the only one: by the time a `Case` reaches here
    // inside a **predicate** it has been lambda-eliminated to its arrow view `𝑤 ⤇ 𝑉` — the
    // sum opened, the witness still named — and realizing that without an assertion shifts
    // the enclosing composition's domain from the witness to the union. The condition is
    // therefore about what the type *says*, not which constructor says it.
    *expr = if mentions_witness {
        Expr::new(TypedExprNode::Realize(Box::new(realized))).with_ty(original)
    } else {
        realized
    };
    true
}

/// One arm per branch, with the first-match path condition each is gated by.
///
/// `witness` is the sum this fan-out realizes, absent for a same-domain conditional that
/// names none. `None` where an arm's domain cannot be read: a multi-candidate arm is a
/// genuinely nested conditional collection and a described one needs the runtime witness, so
/// either way the rewrite does not apply and the `Case` is left for op-conversion to reject.
fn arm_choices(
    branches: Vec<crate::ccl::Branch>,
    witness: Option<(
        crate::ccl::infer_var::WitnessBinderId,
        crate::ccl::ty::TypeKind,
    )>,
) -> Option<Vec<ArmChoice>> {
    let mut arms = Vec::new();
    let mut prior_guards: Vec<Expr> = Vec::new();
    // Flatten `elif` chains first, so a nested conditional collapses into one N-choice
    // fan-out rather than a union of unions.
    for b in flatten_trailing_value_case(branches) {
        let dom = arm_domain(&b.body.ty)?;
        let gate = synthesize_arm_predicate(&b.guard, &prior_guards);
        prior_guards.push(b.guard);
        arms.push(ArmChoice {
            witness: witness.clone(),
            gate,
            arm: discharge_determined_witnesses(b.body),
            dom,
        });
    }
    Some(arms)
}

/// An arm with every **determined** witness discharged — the term *and* the types.
///
/// [`unbox`] alone is the term half, and only where the arm *is* the introduction. A `box`
/// interior to the arm — anything with a mapping body, where the introduction becomes a
/// morphism inside a point-free chain — leaves the resulting sum standing on the arm's type,
/// and the leg then carries it into the union, where the assertion that a leg is a plain
/// collection rightly fails.
///
/// Both halves, in the order [`realize_conditional_collections`] runs them tree-wide: the
/// term first, so no `box` is left whose function type the type half would rewrite (that type
/// is what [`unbox`] reads to know the witness is determined), then the types, per occurrence
/// via [`instantiate_erased_witnesses`] — a binder is named by both spellings of its sum, and
/// one global substitution would put a domain where the unfactored spelling wants an arrow.
///
/// The erased set is **local** to the arm, which is what keeps realization's own witness out
/// of it: an arm-level `box` names the arm's binder, never the site's, so the sum
/// [`TypedExprNode::Realize`] asserts over the union is untouched.
fn discharge_determined_witnesses(arm: Expr) -> Expr {
    fn go(
        expr: &mut Expr,
        erased: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
    ) {
        expr.walk_children_mut(|child| go(child, erased));
        let (unboxed, _) = unbox(
            std::mem::replace(expr, Expr::lit(crate::ccl::Lit::Unit)),
            Some(erased),
        );
        *expr = unboxed;
    }
    let mut arm = arm;
    let mut erased = std::collections::HashSet::new();
    go(&mut arm, &mut erased);
    if !erased.is_empty() {
        instantiate_erased_witnesses(&mut arm, &erased, &PredMemo::new());
    }
    arm
}

/// One witness taking one arm: what a leg is a tuple of.
struct ArmChoice {
    /// The sum this arm is a candidate of — absent for a conditional that names no witness,
    /// whose only site is the `Case` itself.
    witness: Option<(
        crate::ccl::infer_var::WitnessBinderId,
        crate::ccl::ty::TypeKind,
    )>,
    /// The arm's first-match path condition, still pointful so combinations can conjoin it.
    gate: Expr,
    arm: Expr,
    dom: Type,
}

/// Every way to take one arm from each witness, the last witness varying fastest.
fn combinations(choices: &[Vec<ArmChoice>]) -> Vec<Vec<&ArmChoice>> {
    let mut out: Vec<Vec<&ArmChoice>> = vec![Vec::new()];
    for arms in choices {
        out = out
            .into_iter()
            .flat_map(|prefix| {
                arms.iter().map(move |a| {
                    let mut next = prefix.clone();
                    next.push(a);
                    next
                })
            })
            .collect();
    }
    out
}

/// The witnesses this site names, outermost binder first.
///
/// A site's type wraps one `Σ` per conditional generator feeding it, over a single body whose
/// domain is the product they index — so "which witness" is a list, and the depth-one reading
/// ([`witness_named_by`]) is its head.
fn witnesses_named_by(
    ty: &Type,
) -> Vec<(
    crate::ccl::infer_var::WitnessBinderId,
    crate::ccl::ty::TypeKind,
)> {
    let mut out = Vec::new();
    let mut cursor = peel_refinements(ty).clone();
    while let Type::Sigma(sum) = peel_refinements(&cursor).clone() {
        out.push((sum.binder(), sum.kind().clone()));
        cursor = (*sum.body).clone();
    }
    out
}

/// Whether `expr` **is** the conditional collection this witness names.
///
/// A *type* test, deliberately: node identity is provenance, not semantics, and a predicate's
/// copy of the source carries its own. What makes a term the conditional here is that it is a
/// collection-valued value-`Case` typed by this witness — which the copy satisfies too, so
/// finding and replacing can use one test and agree by construction.
fn is_the_conditional(expr: &Expr, binder: crate::ccl::infer_var::WitnessBinderId) -> bool {
    is_value_case(expr)
        && witness_named_by(&expr.ty) == Some(binder)
        && collection_value_ty(&expr.ty).is_some()
}

/// The branches of the conditional collection below `expr` that this witness names.
fn conditional_below(
    expr: &Expr,
    binder: crate::ccl::infer_var::WitnessBinderId,
) -> Option<Vec<crate::ccl::Branch>> {
    if is_the_conditional(expr, binder)
        && let TypedExprNode::Case { branches, .. } = &expr.node
    {
        return Some(branches.clone());
    }
    let mut found = None;
    expr.walk_children(|child| {
        if found.is_none() {
            found = conditional_below(child, binder);
        }
    });
    found
}

/// Replace the conditional this witness names with `replacement`. Answers whether one was
/// found — a leg that kept the whole conditional is not that leg, and would compile a choice
/// that never happened.
fn replace_the_conditional(
    expr: &mut Expr,
    binder: crate::ccl::infer_var::WitnessBinderId,
    replacement: &Expr,
) -> bool {
    if is_the_conditional(expr, binder) {
        *expr = replacement.clone();
        return true;
    }
    let mut done = false;
    expr.walk_children_mut(|child| done |= replace_the_conditional(child, binder, replacement));
    done
}

/// The shared element type of a collection-valued `Case`, or `None` when the `Case` is
/// not collection-valued (a scalar one, which `lambda_elim`'s C-form already handled).
fn collection_value_ty(ty: &Type) -> Option<Type> {
    match peel_refinements(ty) {
        Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
        Type::Sigma(s) => match &*s.body {
            // A sum inside a sum — two conditional sources — carries its element type under
            // the inner binder, since a nested sum's fibers share it just as one sum's do.
            Type::Sigma(_) => collection_value_ty(&s.body),
            // Factored: the body is the data function `w ⤇ 𝑉`, and `𝑉` is shared across
            // the fibers.
            Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
            // Unfactored — what `box`ing each arm builds, and what survives when nothing
            // consumes the collection (a conditional as the program's own result). Each
            // candidate carries its own element type, and the one the union gets is the
            // one the factored view shares out ([`SigmaType::factored_view`]): equal
            // codomains as they are, codomains differing only in a refinement at the base
            // they refine, since a claim only some legs make is not a claim about the
            // union. Bases that differ leave no element type at all, so realization
            // declines and op-conversion rejects the `Case` by name.
            Type::WitnessRef(_) => s.factored_view()?.body.codomain(),
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
    // **A box over a sum introduced nothing**, so it goes whatever its candidates are.
    // Boxing a sum is the identity ([`crate::ccl::ty::SigmaType::into_type`]), so this node
    // and its argument carry the same type and no witness is being erased — nothing is
    // recorded, and `instantiate_erased_witnesses` must not touch a binder that is still
    // live in the argument.
    if matches!(peel_refinements(&argument.ty), Type::Sigma(_)) {
        return ((**argument).clone(), true);
    }
    // **The introduction's stated type, because only a binding position carries the kind.**
    // Determinedness is a fact about the witness's range, and a range belongs to its binder
    // ([`Type::witness_kind`]) — so an interior `box`, whose node type is the sum's body with
    // the witness free, cannot answer. `box`'s function type states the sum it introduces and
    // no rewrite retypes it.
    let stated = function.ty.codomain().unwrap_or_else(|| e.ty.clone());
    // Only a determined witness — one candidate — is erasable.
    match stated.witness_kind() {
        Some(kind) if matches!(kind.listed(), Some([_])) => {
            if let Some(erased) = erased
                && let Type::Sigma(s) = peel_refinements(&stated)
            {
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
    /// Pinned as a unit test because end-to-end the shift it forbids is invisible until
    /// something above the `Case` reads the type: the arrow view is what a mapping
    /// comprehension leaves, and only its *filtered* form
    /// (`a_filter_over_a_conditional_source_is_applied`) looks. Without the assertion that
    /// path silently shifts the enclosing composition's domain from the witness to the
    /// realized union.
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

    /// **A conditional binding is inlined only when someone restricts it.**
    ///
    /// Both halves are one decision and neither is observable end-to-end — the programs
    /// compute the same answer whether the binding was shared or copied — so the sharing
    /// itself is what gets asserted here.
    ///
    /// Copying is what lets the legs carry a consumer's filter, since the legs are then that
    /// consumer's alone; the price is a union per consumer, which is why an unrestricted
    /// binding, owing nothing, keeps its one.
    #[test]
    fn a_conditional_binding_is_copied_to_its_consumer_only_when_restricted() {
        let int = Type::Base(BaseType::Int);
        let w = fresh_witness_binder_id();
        let kind = TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]);
        let sum = |body| {
            Type::Sigma(Box::new(SigmaType::bound(
                Witness::bound_to(w, kind.clone()),
                body,
            )))
        };
        // `Σ σ ∈ {[0, 2], [0, 3]}. (σ ⤇ Int)` — the conditional's own type, and what an
        // unrestricted consumer sees.
        let unrestricted = sum(Type::data_fun(Type::WitnessRef(w), int.clone()));
        // `Σ σ ∈ {[0, 2], [0, 3]}. ({σ | 𝑝} ⤇ Int)` — a filtered comprehension's, the
        // restriction riding the witness.
        let restricted = sum(Type::data_fun(
            Type::Refinement(
                Box::new(Type::WitnessRef(w)),
                crate::ccl::Refinement::born(std::rc::Rc::new(
                    Expr::lit(Lit::Bool(true)).with_ty(Type::Base(BaseType::Bool)),
                )),
            ),
            int.clone(),
        ));
        let guard = |b: bool| Expr::lit(Lit::Bool(b)).with_ty(Type::Base(BaseType::Bool));
        // Each arm is **boxed**, as inference leaves it: two collections over distinct
        // domains have no common type, so the arms of a conditional that types as a sum
        // are one-candidate sums themselves. An unboxed arm is not merely unrealistic
        // here — it is ill-typed, which the `deep-typecheck` feature checks at every
        // rewrite `substitute` performs.
        let arm = |dom: usize| {
            let coll = Type::data_fun(Type::UIntRange(dom), int.clone());
            let aw = fresh_witness_binder_id();
            let boxed = Type::Sigma(Box::new(SigmaType::bound(
                Witness::bound_to(aw, TypeKind::Enumerated(vec![coll.clone()])),
                Type::WitnessRef(aw),
            )));
            Expr::apply(
                Expr::new(TypedExprNode::Var(Name::from("xs"))).with_ty(coll.clone()),
                Expr::builtin(Builtin::Box).with_ty(Type::fun(coll, boxed.clone())),
            )
            .with_ty(boxed)
        };
        let bind_to = |consumer_ty: Type| {
            Expr::let_bind(
                "x",
                Expr::new(TypedExprNode::Case {
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
                })
                .with_ty(unrestricted.clone()),
                Expr::new(TypedExprNode::Var(Name::from("x"))).with_ty(consumer_ty),
            )
            .with_ty(unrestricted.clone())
        };

        let mut shared = bind_to(unrestricted.clone());
        inline_restricted_conditionals(&mut shared);
        assert!(
            matches!(shared.node, TypedExprNode::Let { .. }),
            "an unrestricted conditional owes nothing, so its binding stays shared: {:?}",
            shared.node
        );

        let mut copied = bind_to(restricted);
        inline_restricted_conditionals(&mut copied);
        assert!(
            matches!(copied.node, TypedExprNode::Case { .. }),
            "a restricted consumer gets the conditional itself, not a name for it: {:?}",
            copied.node
        );
    }
}

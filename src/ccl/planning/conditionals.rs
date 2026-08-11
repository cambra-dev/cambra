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
    synthesize_arm_predicate, walk_refined_predicates, walk_refined_predicates_mut,
};
use crate::ccl::{BaseType, Builtin, Expr, FieldKey, Type, TypedExprNode, lambda_elim};

/// Rewrite every collection-valued value-`Case` in `expr` into its gated union, and erase
/// every sum whose witness is **determined** — from the types as well as the terms.
pub(super) fn realize_conditional_collections(
    expr: &mut Expr,
) -> std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId> {
    let mut erased = std::collections::HashSet::new();
    let mut discharged = std::collections::HashSet::new();
    bring_restrictions_under_their_sites_binder(expr);
    inline_restricted_conditionals(expr);
    realize_and_unbox(
        expr,
        &mut erased,
        &PredMemo::new(),
        &OwedRestrictions::new(),
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

/// Give every consumer of a **restricted** conditional collection its own copy of it,
/// dropping the binding that shared it.
///
/// Realization is demand-directed: the legs it builds carry the consuming site's filter,
/// gated arm by arm ([`realize_here`]). So the legs belong to *one* consumer's demand, and a
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

type OwedRestrictions = std::collections::HashMap<crate::ccl::infer_var::WitnessBinderId, Owed>;

/// `owed` carries, per witness binder, the restriction a consuming site **on the path from
/// the root to here** placed on that witness — `Σ σ ∈ 𝐾. ({σ | 𝑝} ⤇ 𝑉)`, the shape a
/// filtered comprehension over a conditional collection has. Realization is what
/// materializes the witness, so it is what discharges the restriction: [`realize_here`]
/// gates each leg by `𝑝` rewritten to read *that leg's arm*.
///
/// Scoped to the path, not accumulated over the tree, and the binder is not enough to make
/// it so: [`inline_restricted_conditionals`] gives each consumer its own copy of the
/// conditional, and the copies share the binder they were cloned from. Two consumers
/// restricting the same sum differently are told apart by *where they are*, so a map that
/// outlived the subtree that filled it would hand one consumer's filter to the other's legs.
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
    owed: &OwedRestrictions,
    in_predicate: bool,
    discharged: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) -> bool {
    let mut changed = false;
    let extended;
    let owed = match restriction_on_a_witness(&expr.ty) {
        // Innermost wins: a site nested under another restricting the same sum is the one
        // whose demand these legs serve.
        Some((binder, restriction)) => {
            extended = {
                let mut path = owed.clone();
                path.insert(binder, restriction);
                path
            };
            &extended
        }
        None => owed,
    };
    // **A conditional inside a predicate is left entirely alone** — not only unrealized,
    // but un-rewritten. It is a placeholder: the per-leg discharge replaces the whole
    // predicate with one reading that leg's arm ([`predicate_under_the_leg`]), so nothing
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
                &OwedRestrictions::new(),
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
fn restriction_on_a_witness(ty: &Type) -> Option<(crate::ccl::infer_var::WitnessBinderId, Owed)> {
    let Type::Sigma(sum) = peel_refinements(ty) else {
        return None;
    };
    let Type::Refinement(base, restriction) = sum.body.domain()? else {
        return None;
    };
    matches!(*base, Type::WitnessRef(w) if w == sum.binder()).then(|| {
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

/// `predicate` as it reads **under leg `i`**: the conditional replaced by `arm`, and the
/// witness instantiated to that arm's domain.
///
/// Both halves are one act, and the second is not bookkeeping. A filter's predicate is
/// *indexed by the element* (`__elem ▷ src ▷ 𝑓`), so `__elem` is typed by the witness the
/// sum's domain names. Swap `src` for a concrete arm and leave the index alone and the
/// application is ill-typed — `expected σ, found [0, 1]` — which nothing on the normal path
/// checks, since the always-on pass-boundary typecheck does not descend into predicates
/// (the `deep-typecheck` feature does, and this is what it caught).
fn predicate_under_the_leg(
    predicate: &Expr,
    binder: crate::ccl::infer_var::WitnessBinderId,
    kind: &crate::ccl::ty::TypeKind,
    arm: &Expr,
    arm_dom: &Type,
) -> Expr {
    let mut out = read_the_arm_instead(predicate, binder, kind, arm);
    instantiate_witness_in_types(&mut out, binder, arm_dom, &PredMemo::new());
    out
}

/// Instantiate `binder` to `candidate` throughout a term's **types**, predicates included.
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

/// Returns whether this node was realized — load-bearing, not bookkeeping: a `Case` inside
/// a **refinement predicate** is rewritten through [`PredMemo::rebuild`], which *discards*
/// the rewrite when the caller reports no change. A realization that forgot to report would
/// be silently undone, leaving an unrealized `Case` in a predicate for op-conversion to
/// reject.
fn realize_here(
    expr: &mut Expr,
    owed: &OwedRestrictions,
    discharged: &mut std::collections::HashSet<crate::ccl::infer_var::WitnessBinderId>,
) -> bool {
    if !is_value_case(expr) {
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
    let owed_here = witness_named_by(&expr.ty).and_then(|w| owed.get(&w).map(|o| (w, o)));
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
        let refined = refine_with(arm_dom.clone(), &gate_fn);
        let arm = unbox(b.body, None).0;
        // **Discharge the site's restriction into this leg.** Realization materializes the
        // witness, so it owes what the consuming site placed on it — and the leg is the one
        // place that restriction can be said *denotationally*, because here the conditional
        // has become a single arm.
        let refined = match owed_here {
            Some((binder, owed)) => {
                discharged.insert(binder);
                Type::Refinement(
                    Box::new(refined),
                    crate::ccl::Refinement::born(std::rc::Rc::new(predicate_under_the_leg(
                        &owed.restriction.predicate,
                        binder,
                        &owed.kind,
                        &arm,
                        &arm_dom,
                    ))),
                )
            }
            None => refined,
        };
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

//! Compiling a conditional collection: `Case{gᵢ → collᵢ}` → the gated union.
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
//! for. And it *changes the representation*: a `Case` typed `Σ (𝐷 : 𝐾). 𝐷 ⤇ 𝑉` becomes a
//! union typed `Variant({𝑖: {𝐷ᵢ | π̂ᵢ}}) ⤇ 𝑉`, a tagged union. Those are different types —
//! the sum picks one branch, the tagged union has rows from every leg — and only the gates
//! make them agree, which no typing rule can check. Performing it *after* the type system
//! is done is what lets the two coexist without a `Fun(Data) <: Σ` bridge to relate them
//! (`src/ccl/design/type-inference.md`, "Only a term builds a sum").
//!
//! Only a witness over **named candidates** can be realized here: the legs are the
//! candidates, so there have to be finitely many, named. A witness a `Case` picks between is
//! realized. Every other is **materialized**: its `box` stays standing, the identity it is at
//! runtime, and the value carries the witness in its keys. A jagged list literal's element
//! position is a listed kind with no `Case` to pick a candidate, and a `List(𝑇)`'s `UIntRanges`
//! and a `Map(𝐾, 𝑉)`'s `SubtypesOf(𝐾)` are described ones
//! (`src/ccl/design/collections.md`, "Compiling a conditional collection").

use std::rc::Rc;

use crate::ccl::ccl_utils::{
    PredMemo, apply_primitive, flatten_trailing_value_case, make_cast, refine_with,
    synthesize_arm_predicate, walk_refined_predicates, walk_refined_predicates_mut,
};
use crate::ccl::{
    BaseType, BinOpKind, Builtin, Expr, FieldKey, LogicKind, Type, TypedExprNode, provenance,
};

/// The witnesses realization realized, by binder.
///
/// One per program rather than one per term, because survival is a fact about a witness
/// rather than about a position ([`realize_conditional_collections`]). A term planning lifts
/// out of a type names the witnesses of the tree it came from.
#[derive(Default, Clone)]
pub(crate) struct Witnesses {
    pub(super) realized: std::collections::HashSet<crate::ccl::ty::WitnessId>,
}

/// Rewrite every collection-valued value-`Case` in `expr` into its gated union.
///
/// Every other sum stays, `box` included: `box` is the identity at runtime, and a collection
/// carries its own domain, so a sum over one candidate is that candidate's collection whether
/// or not its type says so (`src/ccl/design/collections.md`, "Compiling a conditional
/// collection").
pub(super) fn realize_conditional_collections(
    expr: &mut Expr,
    witnesses: &mut Witnesses,
) -> Result<(), String> {
    realize_everywhere(expr, &PredMemo::new(), false, &mut witnesses.realized);
    Ok(())
}

/// Realize every conditional collection in `expr`, top-down.
///
/// `in_predicate` records that this subtree *is* a refinement predicate. A predicate may
/// carry no realized collection (`debug_assert_no_iteration_markers_in_type`: a gated union
/// needs the `iterate`/`restrict` a predicate is forbidden), so realization does not fire
/// there — the `Case` stays, and the per-leg discharge is what replaces it, with a plain arm
/// rather than a union.
fn realize_everywhere(
    expr: &mut Expr,
    memo: &PredMemo<()>,
    in_predicate: bool,
    realized: &mut std::collections::HashSet<crate::ccl::ty::WitnessId>,
) -> bool {
    let mut changed = false;
    // **A conditional inside a predicate is left entirely alone** — not only unrealized,
    // but un-rewritten. It is a placeholder: the per-leg discharge replaces the whole
    // predicate with one reading that leg's arm ([`read_the_arm_instead`]), so nothing
    // inside this copy survives to be compiled.
    if in_predicate && collection_value_ty(&expr.ty).is_some() && is_value_case(expr) {
        return changed;
    }
    // **Top-down.** An `elif` chain is a `Case` whose trailing arm is another `Case`, and
    // `flatten_trailing_value_case` collapses the chain into one N-choice partition —
    // which it can only do while the inner one is still a `Case`. Realizing children
    // first turns it into a union, the flatten silently no-ops, and the outer fan-out
    // ends up with a leg that is already a fan-out.
    if !in_predicate {
        // **Scoped to the attempt and closed before the child walk**, as the group-by
        // recognizer's is: a leg is a copy of this site, so recursing under the recording
        // would make an inner site's legs descend from this one. A site that declines
        // mints nothing, so the wrapper costs a push and a pop
        // (`src/ccl/design/provenance.md`, "Duplication").
        let _g = provenance::enter(
            expr.node_id(),
            "planning.realize",
            provenance::Nature::Expansion,
        );
        changed |= realize(expr, realized);
    }
    expr.walk_children_mut(|child| {
        changed |= realize_everywhere(child, memo, in_predicate, realized)
    });
    expr.walk_type_slots_mut(|ty| {
        changed |= walk_refined_predicates_mut(ty, memo, &(), &mut |pred, memo| {
            realize_everywhere(pred, memo, true, &mut std::collections::HashSet::new())
        });
    });
    changed
}

/// Replace every sum on an **erased** binder by its single candidate, throughout `expr`'s
/// types — the type-level half of [`erase_determined_boxes`].
///
/// Reaches refinement *predicates* too, via [`walk_refined_predicates_mut`]: a predicate is
/// a term with type slots of its own, and a filter's predicate reads the very collection
/// whose sum is being erased, so a witness left there outlives every other mention.
fn instantiate_erased_witnesses(
    expr: &mut Expr,
    erased: &std::collections::HashMap<crate::ccl::ty::WitnessId, Type>,
    memo: &PredMemo<()>,
    in_predicate: bool,
) {
    // **A conditional a predicate quotes stays whole**, as realization leaves it
    // ([`realize_everywhere`]): its arms keep their `box`es, so their sums keep their
    // binders, whichever of those binders the tree's realized copy erased.
    if in_predicate && collection_value_ty(&expr.ty).is_some() && is_value_case(expr) {
        return;
    }
    expr.walk_type_slots_mut(|ty| {
        walk_refined_predicates_mut(ty, memo, &(), &mut |pred, memo| {
            instantiate_erased_witnesses(pred, erased, memo, true);
            true
        });
        instantiate_erased_in_type(ty, erased);
    });
    expr.walk_children_mut(|child| instantiate_erased_witnesses(child, erased, memo, in_predicate));
    // `unbox` of a collection whose witness is erased is that collection: its domain is the
    // candidate the projection now names.
    if let TypedExprNode::Apply { argument, function } = &mut expr.node
        && matches!(function.node, TypedExprNode::Builtin(Builtin::Unbox))
        && argument.ty.peel_refinements().sum().is_none()
    {
        *expr = std::mem::take(&mut **argument);
    }
}

fn instantiate_erased_in_type(
    ty: &mut Type,
    erased: &std::collections::HashMap<crate::ccl::ty::WitnessId, Type>,
) {
    // **Top-down: a sum instantiates its own references before anything below it is
    // visited.** The candidate is spelled where the sum stands, and one witness is named in
    // several frames — a channel keyed by a loop's position and a row inside that loop name the
    // same binder, each sum spelling the candidate in its own binders. Visiting the body first
    // would hand a reference the sum binds the candidate recorded for another frame, whose
    // closed indices then bind whatever function encloses this one.
    if let Some([first, ..]) = ty.sum()
        && erased.contains_key(first.id())
        && let crate::ccl::ty::TypeKind::Enumerated(ds) = first.type_kind()
        && let [sole] = ds.as_slice()
    {
        let sole = sole.clone();
        let mut instantiated = ty.instantiate_sum(&sole);
        instantiate_erased_in_type(&mut instantiated, erased);
        *ty = instantiated;
        return;
    }
    // **A free reference to an erased witness is instantiated too.** Consumption names the
    // witness rather than presenting it (the sum-against-plain constrain arm), so a
    // consumer's recorded
    // domain is a bare `Type::WitnessRef` sitting outside the sum that bound it. Erasing
    // the sum leaves that reference naming nothing, and the chain then carries `σ` where
    // the source carries the concrete domain.
    if let Type::WitnessRef(b) = ty
        && let Some(sole) = erased.get(b)
    {
        *ty = sole.clone();
        return;
    }
    // **So is a projection of one.** `σ₁(𝑐)` names the witness through `𝑐`, whose own type binds
    // it, and erasing that witness leaves the candidate as the domain `𝑐` ranges over
    // (`src/ccl/design/collections.md`, "Projecting a sum's witness").
    // A determined witness is its one candidate by any binder's name, so a projection of one
    // is too: copies of one sum's type carry different binders, and the erased set names only
    // the ones a `box` stated.
    if let Type::WitnessProjection(p) = ty
        && let Some(witness) = p.witness()
        && let Some(sole) = erased
            .get(witness.id())
            .cloned()
            .or_else(|| witness.sole_candidate())
    {
        *ty = sole;
        return;
    }
    ty.walk_children_mut(|child| instantiate_erased_in_type(child, erased));
    // A candidate is a domain, possibly a filtered one, so instantiating a refined position's
    // base can leave a refinement under a refinement; the position holds one set.
    if let Type::Refinement(base, _) = ty
        && matches!(**base, Type::Refinement(..))
    {
        let Type::Refinement(base, own) = std::mem::replace(ty, Type::Hole) else {
            unreachable!("matched a refinement above")
        };
        *ty = Type::refined(*base, own);
    }
}

/// The witness a collection type names, in **either spelling**.
///
/// A `Case` that reaches realization inside a composition (`case ≫ 𝑓` — what a mapping
/// comprehension body builds) does not carry the sum: the composition opened it, and what
/// is left on the `Case` is the **function view** `σ ⤇ 𝑉`, a data function whose domain is the
/// witness. Both spellings name the same sum and both owe the same restriction, so reading
/// the binder off only the `Σ` silently skips the discharge on the composed shape and
/// leaves the site's filter uncompiled.
fn witness_named_by(ty: &Type) -> Option<crate::ccl::ty::WitnessId> {
    let head = ty.peel_refinements();
    if let Some([first, ..]) = head.sum() {
        return Some(*first.id());
    }
    match (head.domain()?).peel_refinements() {
        Type::WitnessRef(w) => Some(*w),
        _ => None,
    }
}

/// Instantiate `binder` to `candidate` throughout a term's **types**, predicates included.
fn strip_the_instantiated_binder(ty: &mut Type, binder: &crate::ccl::ty::WitnessId) {
    ty.walk_children_mut(|child| strip_the_instantiated_binder(child, binder));
    if let Type::Fun {
        fun_kind: crate::ccl::ty::FunKind::Data(slot @ Some(_)),
        ..
    } = ty
    {
        let ws = slot.as_ref().expect("guarded Some");
        if ws.iter().any(|w| w.id() == binder) {
            let kept: Vec<crate::ccl::ty::Witness> =
                ws.iter().filter(|w| w.id() != binder).cloned().collect();
            *slot = (!kept.is_empty()).then(|| Rc::new(kept));
        }
    }
}

fn instantiate_witness_in_types(
    expr: &mut Expr,
    binder: &crate::ccl::ty::WitnessId,
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

/// `predicate` with the conditional `witness` indexes replaced by `arm`.
///
/// A filter's predicate looks its collection up at the index (`__elem ▷ src ▷ 𝑓`), and `src`
/// is the whole conditional. Under leg `i` that conditional *is* `arm`, because the leg is
/// gated by `π̂ᵢ` — so reading the arm directly is the same fact, said in a form a predicate
/// may hold: a plain collection, needing no realization and therefore none of the
/// `iterate`/`restrict` machinery a predicate is forbidden to carry.
///
/// Identified by **type**, not by shape: the source is whatever is indexed by this sum's
/// witness, which its kind says exactly. Matching structurally would have to guess which
/// subterm is the collection.
///
/// **Which of the site's conditionals, by the index that reads it.** A site over a product
/// of conditional domains has one source per position, and what its index ranges over does
/// not tell them apart — two conditionals over the same candidate domains state identical
/// kinds. What does is the element position the source is applied to, which the predicate
/// spells in the site's own binders (`crate::ccl::ccl_utils::type_element_reads_from_base`).
/// So the
/// two halves ask one question between them: this sum's kind says the function is a
/// conditional collection, and the argument naming `witness` says it is *this* one.
fn read_the_arm_instead(predicate: &Expr, witness: &crate::ccl::ty::Witness, arm: &Expr) -> Expr {
    let mut out = predicate.clone();
    if let TypedExprNode::Apply { argument, function } = &mut out.node
        && crate::ccl::ty::free_witness_refs(&argument.ty, &[]) == [*witness.id()]
        && indexed_by_this_sum(function, &witness.type_kind())
    {
        // The argument is the index this source is read at, so nothing below either side is
        // another source: the arm replaces the whole collection.
        **function = arm.clone();
        return out;
    }
    out.walk_children_mut(|child| *child = read_the_arm_instead(child, witness, arm));
    out
}

/// Whether `expr` is a conditional collection whose index ranges over `type_kind`.
///
/// By candidates rather than by binder id, because the predicate holds its **own copy** of
/// the source and that copy names a different binder than the site's sum. Comparing resolved,
/// because a candidate spelled as a variable and the same candidate resolved are one
/// candidate.
///
/// Subtyping does not do this — it relates two references by identity under a correspondence
/// (`src/ccl/design/type-inference.md`, "One rule for the solve and the check") — so a copy
/// whose binder nothing relates to the site's is a naming gap this reads around rather than a
/// rule it follows.
fn indexed_by_this_sum(expr: &Expr, type_kind: &crate::ccl::ty::TypeKind) -> bool {
    match expr.ty.peel_refinements().sum() {
        Some([first, ..]) => first.type_kind() == *type_kind,
        // A domain that *names* an index rather than being a sum has its binder elsewhere,
        // so this type does not say what it ranges over.
        _ => false,
    }
}

/// Every witness `expr` **references** but does not **bind**, predicates included.
///
/// A binder is unique to the sum that minted it, so a reference with no binder anywhere in
/// the tree is free wherever it sits — the two sets can be read whole and subtracted rather
/// than tracked against a scope.
fn free_witnesses(expr: &Expr) -> std::collections::HashSet<crate::ccl::ty::WitnessId> {
    fn in_type(
        ty: &Type,
        referenced: &mut std::collections::HashSet<crate::ccl::ty::WitnessId>,
        bound: &mut std::collections::HashSet<crate::ccl::ty::WitnessId>,
    ) {
        match ty {
            Type::WitnessRef(w) => {
                referenced.insert(*w);
            }
            Type::Fun {
                fun_kind: crate::ccl::ty::FunKind::Data(Some(ws)),
                ..
            } => bound.extend(ws.iter().map(|w| *w.id())),
            _ => {}
        }
        ty.walk_children(|child| in_type(child, referenced, bound));
    }
    fn go(
        expr: &Expr,
        referenced: &mut std::collections::HashSet<crate::ccl::ty::WitnessId>,
        bound: &mut std::collections::HashSet<crate::ccl::ty::WitnessId>,
        visited: &mut std::collections::HashSet<crate::ccl::ty::PredicateId>,
    ) {
        expr.walk_type_slots(|ty| {
            in_type(ty, referenced, bound);
            walk_refined_predicates(ty, visited, &mut |pred, visited| {
                go(pred, referenced, bound, visited);
            });
        });
        expr.walk_children(|child| go(child, referenced, bound, visited));
    }
    let (mut referenced, mut bound) = (Default::default(), Default::default());
    go(
        expr,
        &mut referenced,
        &mut bound,
        &mut std::collections::HashSet::new(),
    );
    referenced.retain(|w| !bound.contains(w));
    referenced
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

/// Realize a conditional collection where it stands, as the gated union of its arms.
///
/// The design is `src/ccl/design/collections.md`, "Compiling a conditional collection". The
/// site is a collection-valued value `Case`: every consumer reads it through `unbox`, over its
/// projected domain, so no consumer names its witness and none is a site. The union replaces
/// the `Case` under a [`TypedExprNode::Realize`] that asserts the `Case`'s type and stages the
/// `Case` itself. A witness-free conditional is the degenerate case: substituting the arm for
/// the conditional leaves the arm, and the union's own type is asserted.
///
/// Returns whether this node was realized, which is load-bearing rather than bookkeeping: a
/// `Case` inside a **refinement predicate** is rewritten through [`PredMemo::rebuild`],
/// which *discards* the rewrite when the caller reports no change. A realization that
/// forgot to report would be silently undone.
fn realize(
    expr: &mut Expr,
    realized: &mut std::collections::HashSet<crate::ccl::ty::WitnessId>,
) -> bool {
    let Some(value_ty) = collection_value_ty(&expr.ty) else {
        return false;
    };
    if !is_value_case(expr) {
        return false;
    }
    // Each witness's own fan-out, in the order the site's binders nest. A witness whose
    // `Case` is not below this node cannot be realized here, and realizing only the others
    // would rebuild the nesting the combinations exist to avoid — so the site declines as a
    // whole, and op-conversion rejects the surviving sum by name.
    let witnesses = witnesses_named_by(&expr.ty);
    let choices: Vec<Vec<ArmChoice>> = if witnesses.is_empty() {
        let TypedExprNode::Case { branches, .. } = &expr.node else {
            unreachable!("is_value_case matched a Case")
        };
        match arm_choices(branches.clone(), None) {
            Some(arms) => vec![arms],
            None => return false,
        }
    } else {
        let mut per_witness = Vec::new();
        for w in &witnesses {
            let Some(branches) = conditional_below(expr, w, ordinal_of(&witnesses, w)) else {
                return false;
            };
            match arm_choices(branches, Some(w.clone())) {
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
            unreachable!("a combination names one arm per witness, so it has a gate")
        };
        // **A decline, not a defect.** A guard is a user expression and elimination reports
        // the shapes it has no rule for, so this is the one bail-out below that a program can
        // reach on its own. The site leaves its sum standing and op-conversion rejects it by
        // name.
        //
        // The gate needs no planning here: realization reaches it as it descends into the
        // union it builds, and every later phase reaches it with the tree
        // (`PlanningPhase::reaches_its_lifts`).
        let Ok(gate_pf) = super::predicates::eliminate_lifted(gate) else {
            return false;
        };
        let mut leg = expr.clone();
        for choice in &combination {
            let Some(wanted) = &choice.witness else {
                // No witness: the site is the `Case` itself, so the substitution is the arm.
                leg = choice.arm.clone();
                continue;
            };
            // Skip 0, not this witness's ordinal: choices apply in witness order,
            // so by this witness's turn every earlier same-kind witness has
            // already replaced its `Case`, and the one this witness read is the
            // first still standing.
            // `conditional_below` found this witness's `Case` in the site, and the leg is a
            // copy of the site, so the same walk finds it here.
            assert!(
                replace_the_conditional(&mut leg, wanted, 0, &choice.arm),
                "a leg has the `Case` the site was realized for"
            );
            // **A filter's predicate holds its own read of the source**, so the conditional is
            // in there too and a leg whose predicate still tests the *whole* conditional is not
            // that leg. Rewritten before the witness is instantiated, because the match that
            // finds the source in a predicate reads the witness it is indexed by.
            let memo = PredMemo::new();
            leg.walk_type_slots_mut(|ty| {
                walk_refined_predicates_mut(ty, &memo, &(), &mut |pred, _| {
                    *pred = read_the_arm_instead(pred, wanted, &choice.arm);
                    true
                });
            });
            // **The site's witness, under every binder that spells it.** A predicate holds
            // its own copy of the source and that copy carries a witness binder of its
            // own, so the site's binder is not the only spelling of this witness in the
            // leg. The rewrite above erased the copy's sum, which leaves those occurrences
            // *free* — and a free witness reference in a leg can only be this consumption's,
            // since the leg is one chosen arm and every other sum in it still carries its
            // own binder. So the set is read off the leg rather than collected at the one
            // site that happened to name it: a predicate spells the witness wherever the
            // element is projected, not only where the source is read
            // (`a_filtered_conditional_generator_beside_another`).
            let mut instantiate = free_witnesses(&leg);
            instantiate.insert(*wanted.id());
            for binder in &instantiate {
                instantiate_witness_in_types(&mut leg, binder, &choice.dom, &PredMemo::new());
            }
            // Every witness this arm was chosen for is gone from the leg — the site's
            // binder by the instantiation above, the predicate's copies with it. What
            // remains is bound by a sum the leg still carries, which is a conditional this
            // combination did not choose and a later realization will reach.
            debug_assert!(
                free_witnesses(&leg).is_empty(),
                "a realized leg still names a witness free: {:?}",
                free_witnesses(&leg)
            );
        }
        // The gate rides the **leg's** domain, not any one arm's: with a second generator the
        // leg is indexed by a product, and the gate is constant in the element either way.
        let Some(leg_dom) = leg.ty.domain() else {
            unreachable!("a leg is the site with an arm in place, and the site is a collection")
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
    assert!(
        !legs.is_empty(),
        "every combination builds a leg, and there is at least one combination"
    );
    for w in &witnesses {
        realized.insert(*w.id());
    }
    // Every witness of the site is instantiated in its legs, so the union is a plain data
    // function over the flat `Variant` of their domains — no binder is left for it to carry.
    debug_assert!(
        legs[0].ty.peel_refinements().sum().is_none(),
        "a realized leg quantifies a witness the site did not name: site {:?} named {:?}, leg {:?}",
        original.peel_refinements().to_string(),
        witnesses.iter().map(|w| w.id()).collect::<Vec<_>>(),
        legs[0].ty.peel_refinements().to_string()
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
    let union = if legs.len() == 1 {
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
    // inside a **predicate** it has been lambda-eliminated to its function view `𝑤 ⤇ 𝑉` — the
    // sum opened, the witness still named — and realizing that without an assertion shifts
    // the enclosing composition's domain from the witness to the union. The condition is
    // therefore about what the type *says*, not which constructor says it.
    // The realization stages the conditional it replaces, so a type quoting the conditional
    // (a consumer's `σ₁(𝑐)`) and this node compare as one term: normal form reads a `Realize`
    // as what it stages.
    let staged = Rc::new(std::mem::take(expr));
    let asserted = if mentions_witness {
        original
    } else {
        union.ty.clone()
    };
    *expr = Expr::new(TypedExprNode::Realize {
        value: Box::new(union),
        staged,
    })
    .with_ty(asserted);
    true
}

/// One arm per branch, with the first-match path condition each is gated by.
///
/// `witness` is the sum this fan-out realizes, absent for a same-domain conditional that
/// names none. `None` where an arm's domain cannot be read: a multi-candidate arm is a
/// genuinely nested conditional collection, and an arm naming no candidate needs the runtime
/// witness, so either way the rewrite does not apply and the `Case` is left for
/// op-conversion to reject.
fn arm_choices(
    branches: Vec<crate::ccl::Branch>,
    witness: Option<crate::ccl::ty::Witness>,
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
/// [`erase_determined_boxes`] alone is the term half, and only where the arm *is* the introduction.
/// A `box` interior to the arm — anything with a mapping body, where the introduction becomes a
/// morphism inside a point-free chain — leaves the resulting sum standing on the arm's type, and
/// the leg then carries it into the union, where the assertion that a leg is a plain collection
/// rightly fails.
///
/// Both halves, in the order [`realize_conditional_collections`] runs them tree-wide: the
/// term first, so no `box` is left whose function type the type half would rewrite (that type is
/// what [`erase_determined_boxes`] reads to know the witness is determined), then the types, per
/// occurrence via [`instantiate_erased_witnesses`] — a binder is named by the closed and the open
/// spelling of its sum alike, and each occurrence instantiates against what it holds.
///
/// The erased set is **local** to the arm, which is what keeps realization's own witness out
/// of it: an arm-level `box` names the arm's binder, never the site's, so the sum
/// [`TypedExprNode::Realize`] asserts over the union is untouched.
fn discharge_determined_witnesses(arm: Expr) -> Expr {
    fn go(
        expr: &mut Expr,
        erased: &mut std::collections::HashMap<crate::ccl::ty::WitnessId, Type>,
    ) {
        expr.walk_children_mut(|child| go(child, erased));
        let (unboxed, _) = erase_determined_boxes(
            std::mem::replace(expr, Expr::lit(crate::ccl::Lit::Unit)),
            Some(erased),
        );
        *expr = unboxed;
    }
    let mut arm = arm;
    let mut erased = std::collections::HashMap::new();
    go(&mut arm, &mut erased);
    if !erased.is_empty() {
        instantiate_erased_witnesses(&mut arm, &erased, &PredMemo::new(), false);
    }
    collapse_determined_sums(&mut arm, &std::collections::HashSet::new());
    arm
}

/// Instantiate every **determined** sum in `expr`'s types — one whose witness ranges over a
/// single candidate, so the candidate is the domain and the binder quantifies nothing.
///
/// Erasing the `box` above is not enough to reach them. A consumer of a sum is a sum over
/// its *own* binder ([`crate::ccl::ty::FunKindVar::binder_ids`]), related to the
/// introduction's by the scope change the edge carried — so erasing the introduction leaves
/// every consumer downstream still quantifying a witness with one candidate. Determinedness
/// is a fact about a kind rather than about the term that introduced it, which is what this
/// asks.
fn collapse_determined_sums(
    expr: &mut Expr,
    keep: &std::collections::HashSet<crate::ccl::ty::WitnessId>,
) {
    // **Not into the predicates.** A predicate holding a conditional source is a
    // placeholder realization replaces wholesale ([`read_the_arm_instead`]), and collapsing
    // a sum inside it rewrites a copy that does not survive — the same reason
    // [`realize_everywhere`] leaves one alone.
    fn gather_type(
        ty: &Type,
        keep: &std::collections::HashSet<crate::ccl::ty::WitnessId>,
        out: &mut std::collections::HashMap<crate::ccl::ty::WitnessId, Type>,
    ) {
        let mut ty = ty.clone();
        while let Some([first, ..]) = ty.peel_refinements().sum() {
            if keep.contains(first.id()) {
                break;
            }
            let kind = first.type_kind();
            let crate::ccl::ty::TypeKind::Enumerated(ds) = &kind else {
                break;
            };
            let [sole] = ds.as_slice() else {
                break;
            };
            out.entry(*first.id()).or_insert_with(|| sole.clone());
            // A sum's body can be another, and dropping one binder is what exposes it.
            ty = ty.instantiate_sum(sole);
        }
        // A projection names its witness through the term it quotes, whose type binds it under
        // the id that term was typed with, so the witness is gathered from there.
        if let Type::WitnessProjection(p) = &ty {
            gather(&p.term, keep, out);
        }
        ty.walk_children(|child| gather_type(child, keep, out));
    }

    fn gather(
        expr: &Expr,
        keep: &std::collections::HashSet<crate::ccl::ty::WitnessId>,
        out: &mut std::collections::HashMap<crate::ccl::ty::WitnessId, Type>,
    ) {
        expr.walk_type_slots(|ty| gather_type(ty, keep, out));
        expr.walk_children(|child| gather(child, keep, out));
    }
    let mut determined = std::collections::HashMap::new();
    gather(expr, keep, &mut determined);
    if !determined.is_empty() {
        instantiate_erased_witnesses(expr, &determined, &PredMemo::new(), false);
    }
}

/// One witness taking one arm: what a leg is a tuple of.
struct ArmChoice {
    /// The sum this arm is a candidate of — absent for a conditional that names no witness,
    /// whose only site is the `Case` itself.
    witness: Option<crate::ccl::ty::Witness>,
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
fn witnesses_named_by(ty: &Type) -> Vec<crate::ccl::ty::Witness> {
    ty.peel_refinements().sum().unwrap_or_default().to_vec()
}

/// Whether `expr` **is** the conditional collection this witness names.
///
/// A *type* test, deliberately: node identity is provenance, not semantics, and a predicate's
/// copy of the source carries its own. What makes a term the conditional here is that it is a
/// collection-valued value-`Case` typed by this witness — which the copy satisfies too, so
/// finding and replacing can use one test and agree by construction.
///
/// Matched by **kind**: the site's witness and the value's `Case` are two derivations
/// of one consumption, and no mint ever needs to agree with another
/// (`src/ccl/design/type-inference.md`, "A binder is minted where a scope needs one"), so the
/// binder ids differ and the kind is the shared content. Two conditionals over identical
/// candidates are told apart by
/// position: a realized `Case` stops matching, so the walk pairs sites and `Case`s in
/// order (`two_conditional_sources_compile`).
fn is_the_conditional(expr: &Expr, wanted: &crate::ccl::ty::Witness) -> bool {
    let named = match expr.ty.peel_refinements().sum() {
        Some([first, ..]) => first.type_kind() == wanted.type_kind(),
        _ => witness_named_by(&expr.ty) == Some(*wanted.id()),
    };
    is_value_case(expr) && named && collection_value_ty(&expr.ty).is_some()
}

/// Which same-kind `Case` this witness pairs with: its position among the site's
/// witnesses of the same kind. Binders nest in generator order and the `Case`s stand in
/// the same order, so position is the pairing for witnesses one kind cannot tell apart.
fn ordinal_of(witnesses: &[crate::ccl::ty::Witness], wanted: &crate::ccl::ty::Witness) -> usize {
    witnesses
        .iter()
        .take_while(|w| w.id() != wanted.id())
        .filter(|w| w.type_kind() == wanted.type_kind())
        .count()
}

/// The branches of the conditional collection below `expr` that this witness names —
/// the `skip`-th matching `Case` in walk order. Witnesses over one kind are told apart
/// by position: the site's binders nest in generator order and the `Case`s stand in the
/// same order, so the i-th same-kind witness pairs with the i-th same-kind `Case`
/// (`two_conditional_sources_compile`).
fn conditional_below(
    expr: &Expr,
    wanted: &crate::ccl::ty::Witness,
    mut skip: usize,
) -> Option<Vec<crate::ccl::Branch>> {
    fn go(
        expr: &Expr,
        wanted: &crate::ccl::ty::Witness,
        skip: &mut usize,
    ) -> Option<Vec<crate::ccl::Branch>> {
        if is_the_conditional(expr, wanted)
            && let TypedExprNode::Case { branches, .. } = &expr.node
        {
            if *skip == 0 {
                return Some(branches.clone());
            }
            *skip -= 1;
        }
        let mut found = None;
        expr.walk_children(|child| {
            if found.is_none() {
                found = go(child, wanted, skip);
            }
        });
        found
    }
    go(expr, wanted, &mut skip)
}

/// Replace the conditional this witness names — the `skip`-th match, the one
/// [`conditional_below`] read — with `replacement`. Answers whether one was found — a
/// leg that kept the whole conditional is not that leg, and would compile a choice
/// that never happened.
fn replace_the_conditional(
    expr: &mut Expr,
    wanted: &crate::ccl::ty::Witness,
    mut skip: usize,
    replacement: &Expr,
) -> bool {
    fn go(
        expr: &mut Expr,
        wanted: &crate::ccl::ty::Witness,
        skip: &mut usize,
        done: &mut bool,
        replacement: &Expr,
    ) -> bool {
        if *done {
            return true;
        }
        if is_the_conditional(expr, wanted) {
            if *skip == 0 {
                *expr = replacement.clone();
                *done = true;
                return true;
            }
            *skip -= 1;
        }
        expr.walk_children_mut(|child| {
            go(child, wanted, skip, done, replacement);
        });
        *done
    }
    let mut done = false;
    go(expr, wanted, &mut skip, &mut done, replacement)
}

/// The shared element type of a collection-valued `Case`, or `None` when the `Case` is
/// not collection-valued (a scalar one, which `lambda_elim`'s C-form already handled).
fn collection_value_ty(ty: &Type) -> Option<Type> {
    match ty.peel_refinements() {
        // A sum's codomain is the element type shared across its fibers, at any number
        // of binders — one slot read serves both spellings.
        Type::Fun { codomain, .. } => Some(codomain.as_ref().clone()),
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
    let head = ty.peel_refinements();
    match head.sum() {
        Some([first, ..]) => match first.type_kind() {
            crate::ccl::ty::TypeKind::Enumerated(ds) if ds.len() == 1 => {
                let sole = &ds[0];
                let sole = sole.clone();
                head.instantiate_sum(&sole).peel_refinements().domain()
            }
            _ => None,
        },
        _ => head.domain(),
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
fn erase_determined_boxes(
    e: Expr,
    erased: Option<&mut std::collections::HashMap<crate::ccl::ty::WitnessId, Type>>,
) -> (Expr, bool) {
    let TypedExprNode::Apply { function, argument } = &e.node else {
        return (e, false);
    };
    if !matches!(function.node, TypedExprNode::Builtin(Builtin::Box)) {
        return (e, false);
    }
    // **The introduction's stated type, because only a binding position carries the kind.**
    // Determinedness is a fact about the witness's range, and a range belongs to its binder
    // ([`Type::witness_kind`]) — so an interior `box`, whose node type is the sum's body with
    // the witness free, cannot answer. `box`'s function type states the sum it introduces and
    // no rewrite retypes it.
    let stated = function.ty.codomain().unwrap_or_else(|| e.ty.clone());
    // **A box over a sum introduced nothing**, so it goes whatever its candidates are.
    // The node and its argument carry the same collection and no witness is being erased —
    // nothing is recorded, and `instantiate_erased_witnesses` must not touch a binder that
    // is still live in the argument.
    //
    // **Except one stating a described sum.** It re-views the argument's sum as the one its
    // position declares — a mutable variable's seed restated at its value type is the case
    // (`mut_elim::view_values_at_value_type`) — and the argument's own sum may be one this pass
    // erases. Erasing both would leave a plain collection where the declared sum stands, so
    // this one stays as the entry into that sum, which op-conversion takes as the identity.
    let described = stated
        .witness_kind()
        .is_some_and(|k| !matches!(k, crate::ccl::ty::TypeKind::Enumerated(_)));
    if argument.ty.peel_refinements().sum().is_some() && !described {
        return ((**argument).clone(), true);
    }
    // Only a determined witness — one candidate — is erasable.
    match stated.witness_kind() {
        Some(crate::ccl::ty::TypeKind::Enumerated(ds)) if ds.len() == 1 => {
            if let Some(erased) = erased
                && let Some([first, ..]) = stated.peel_refinements().sum()
                && let crate::ccl::ty::TypeKind::Enumerated(inner) = first.type_kind()
                && let [sole] = inner.as_slice()
            {
                erased.insert(*first.id(), sole.clone());
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
    use crate::ccl::ty::{TypeKind, Witness};
    use crate::ccl::{Branch, Lit, Name};

    /// **A `Case` inside a refinement predicate is left alone.** The gated union it would
    /// become needs `iterate`/`restrict`, which a predicate may not carry
    /// (`debug_assert_no_iteration_markers_in_type`), so the per-leg discharge replaces it with
    /// a plain arm instead.
    #[test]
    fn a_case_inside_a_refinement_predicate_is_left_alone() {
        let int = Type::Base(BaseType::Int);
        let coll = Type::data_fun(Type::UIntRange(2), int.clone());

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
        let ty = Type::refined_one(
            Type::UIntRange(2),
            crate::ccl::Refinement::born(Rc::new(case)),
        );
        let mut expr =
            Expr::new(TypedExprNode::Var(Name::from("site"))).with_ty(Type::data_fun(ty, int));

        realize_conditional_collections(&mut expr, &mut Witnesses::default())
            .expect("realization does not fail");

        let Type::Fun { domain, .. } = &expr.ty else {
            panic!("expected a function type, got {}", expr.ty);
        };
        let Type::Refinement(_, refinements) = &**domain else {
            panic!("expected the refinement to survive, got {domain}");
        };
        let refinement = refinements.sole().expect("one refinement");
        let rendered = crate::ccl::symbolic::symbolic(&refinement.predicate);
        assert!(
            rendered.contains('→'),
            "the predicate's `Case` must be left for the per-leg discharge: {rendered}"
        );
    }

    /// **Realization never changes a type that names the witness.** `Realize` asserts the
    /// pre-realization type precisely so that nothing above a realized `Case` has to be
    /// rewritten, and the mentions that would need rewriting are exactly the ones naming
    /// the witness — whether the naming type is the sum itself or the function view
    /// `𝑤 ⤇ 𝑉` a lambda-eliminated `Case` carries inside a predicate.
    ///
    /// Pinned as a unit test because end-to-end the shift it forbids is invisible until
    /// something above the `Case` reads the type: the function view is what a mapping
    /// comprehension leaves, and only its *filtered* form
    /// (`a_filter_over_a_conditional_source_is_applied`) looks. Without the assertion that
    /// path silently shifts the enclosing composition's domain from the witness to the
    /// realized union.
    #[test]
    fn realizing_a_body_fun_case_keeps_the_witness_in_its_type() {
        let int = Type::Base(BaseType::Int);
        let w = fresh_witness_binder_id();
        let wv = Witness::bound_to(w, TypeKind::Type);
        let witness = Type::WitnessRef(*wv.id());
        // Two guarded arms, each a concrete collection — the shape a conditional
        // collection has once `box` is gone and the sum has been opened.
        let arm = |dom: u64| {
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
        // The **function view**: the sum opened, the witness still named. Not a `Type::Sigma`,
        // which is the whole point — the old condition tested the constructor.
        let body_fun = Type::data_fun(witness.clone(), int.clone());
        let mut expr = Expr::new(case).with_ty(body_fun.clone());

        realize_conditional_collections(&mut expr, &mut Witnesses::default())
            .expect("no jagged rows here");

        assert_eq!(
            expr.ty, body_fun,
            "realization must assert the pre-realization type, not the union's: {}",
            expr.ty
        );
        assert!(
            matches!(expr.node, TypedExprNode::Realize { .. }),
            "the assertion is carried by a `Realize` node, got {:?}",
            expr.node
        );
    }
}

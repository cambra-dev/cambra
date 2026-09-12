//! Name the inner source of a **correlated** comprehension.
//!
//! An inner comprehension whose body reads the outer binder runs once per outer row, and
//! `lambda_elim` writes that as `curry(𝑔)` over the outer stream, where `𝑔` takes the pair
//! `(outer value, inner position)`. The collection `curry` produces is over the second half
//! of that pair, and the term does not say which positions those are: `𝑔` reaches them only
//! by *applying* the inner source at the pair's `.1`.
//!
//! A type answers only where the positions are an extent — a list's index range. Where they
//! are a collection's own domain the type says `{𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`, whose
//! extent is the whole key type (`extent_of` strips refinements) and whose refinement is
//! carried and never executed. The positions are in the data, so the term has to name them,
//! and [`name_correlated_sources`] rewrites the site to [`Builtin::CurryOver`], which does.
//!
//! Declining is safe: the site keeps its `curry`, and op-conversion falls back to reading
//! the positions off the type — correct wherever that type is an extent.

use super::*;
use crate::ccl::ccl_utils::free_names_in_value;
use crate::ccl::subst::Subst;
use crate::ccl::ty::Refinement;

use super::predicates::fn_of_bare_predicate;

/// Rewrite every correlated curry site to name its inner source.
///
/// Runs before the iteration-site walk, so the `map_domain` this mints is marked like any
/// other iteration source.
pub(super) fn name_correlated_sources(expr: &mut Expr) {
    // Before the naming below, which reads the pair domain's second component: a filter
    // riding that component is part of the domain this site iterates.
    let node_id = expr.node_id();
    if let TypedExprNode::Apply { argument, function } = &mut expr.node
        && is_builtin(function, Builtin::Curry)
    {
        let _g = provenance::enter(
            node_id,
            "planning.correlated_filter",
            provenance::Nature::Machinery,
        );
        if rebase_pair_filter(argument) {
            // `curry`'s own stamp says what it takes; the argument's domain just moved.
            function.ty = Type::fun(argument.ty.clone(), expr.ty.clone());
        }
    }
    let rewritten = {
        let _g = provenance::enter(
            expr.node_id(),
            "planning.correlated",
            provenance::Nature::Machinery,
        );
        name_inner_source(expr)
    };
    if let Some(rewritten) = rewritten {
        *expr = rewritten;
    }
    expr.walk_children_mut(name_correlated_sources);
}

/// `curry(𝑔)` rewritten to `(map_domain(𝑠), 𝑔) ▷ curry_over`, where `𝑠` is the collection
/// `𝑔` applies at the pair's second component.
///
/// `map_domain` and not `𝑠` itself: [`Builtin::CurryOver`] reads the positions off its
/// source's *codomain*, and a collection carries values there. Re-viewing it at its own
/// domain is what puts the positions where they are read.
fn name_inner_source(expr: &Expr) -> Option<Expr> {
    let TypedExprNode::Apply {
        argument: g,
        function,
    } = &expr.node
    else {
        return None;
    };
    if !is_builtin(function, Builtin::Curry) {
        return None;
    }
    let Some(Type::Tuple(pair)) = g.ty.domain().map(|d| d.peel_refinements().clone()) else {
        return None;
    };
    let [_, positions] = pair.as_slice() else {
        return None;
    };
    let source = inner_source(g, positions)?;
    let source_ty = Type::data_fun(positions.clone(), positions.clone());
    // A **recorded copy**: the source stays where it is inside `𝑔`, which applies it at each
    // position, and this second occurrence re-views it at its domain. `Clone` re-mints the
    // ids and the frame records the parentage, as entry iteration's kept collection does.
    let copy = {
        let _frame = provenance::copy_frame("planning.correlated_source");
        source.clone()
    };
    let keys = apply_primitive(copy, Builtin::MapDomain, source_ty.clone());
    let pair = Expr::tuple(vec![keys, g.as_ref().clone_preserving_ids()])
        .with_ty(Type::Tuple(vec![source_ty, g.ty.clone()]));
    Some(apply_primitive(pair, Builtin::CurryOver, expr.ty.clone()))
}

/// The collection `g` applies at the pair's second component, where its domain is the
/// positions the curried collection is over.
///
/// The search is for the spelling `lambda_elim` leaves — a chain headed by `.1` — and is
/// coupled to it the way a site matcher is. The domain check is what keeps an unrelated
/// `.1` out: a pair's second component is projected wherever the body reads the position,
/// and only the one feeding a collection over those positions names the source.
fn inner_source<'a>(g: &'a Expr, positions: &Type) -> Option<&'a Expr> {
    if let TypedExprNode::Compose(elements) = &g.node
        && let [head, source, ..] = elements.as_slice()
        && matches!(&head.node, TypedExprNode::Proj(ProjKey::Index(1)))
        && source.ty.domain().is_some_and(|d| &d == positions)
    {
        return Some(source);
    }
    let mut found = None;
    g.walk_children(|child| {
        if found.is_none() {
            found = inner_source(child, positions);
        }
    });
    found
}

/// Re-base a correlated filter's predicate from the inner element onto the **pair**.
///
/// `lambda_elim`'s pairing rule leaves a filter as a refinement on the *second component* of
/// the pair domain, whose predicate reaches the outer value through the enclosing Pi binder:
/// `(𝐴, {𝐾 | p(__elem, __pair.0)})`. That predicate is not closed, and a compiled refinement
/// predicate has to be a **value function** — the producer/consumer match compares distinct
/// `Rc`s, and `__pair` is minted fresh per elimination, so two copies of one predicate would
/// compare unequal (`src/ccl/planning/predicates.rs`).
///
/// The same set is `{(𝐴, 𝐾) | p(__elem.0, __elem.1)}`: a refinement on the product rather
/// than a dependent component. Written that way the outer value is reached through the
/// refinement's own binder and nothing is free, so the predicate is a value function and the
/// pair binder is not needed at all.
fn rebase_pair_filter(g: &mut Expr) -> bool {
    let Type::Fun {
        fun_kind,
        domain,
        codomain,
        ..
    } = &g.ty
    else {
        return false;
    };
    let Type::Tuple(components) = domain.as_ref() else {
        return false;
    };
    let [outer, Type::Refinement(inner, filters)] = components.as_slice() else {
        return false;
    };
    // **The pair binder is free here, and has to be.** A `Type::Fun`'s binder scopes over
    // its codomain, so a domain referencing the function's own parameter names something no
    // binder binds — which is what the pairing rule writes when it substitutes the outer
    // binder for `pair.0` inside the second component's type. The name is read off the
    // predicate rather than off the function for that reason.
    let Some(binder) = filters
        .as_slice()
        .iter()
        .flat_map(|r| free_names_in_value(&r.predicate))
        .find(Name::is_synthetic_pair)
    else {
        return false;
    };
    let pair_ty = Type::Tuple(vec![outer.clone(), (**inner).clone()]);
    let elem = Expr::var(Name::elem()).with_ty(pair_ty.clone());
    let at = |index: usize, ty: &Type| {
        Expr::apply(
            elem.clone_preserving_ids(),
            Expr::proj_index(index).with_ty(Type::fun(pair_ty.clone(), ty.clone())),
        )
        .with_ty(ty.clone())
    };
    // Innermost first: the element read introduces a reference to the new binder, and the
    // pair read must not then be rewritten as one of its own occurrences.
    let rebased: Vec<Expr> = filters
        .as_slice()
        .iter()
        .map(|r| {
            let onto_pair = Subst::discharge(Name::elem(), at(1, inner)).apply_expr(&r.predicate);
            // The pair binder becomes the refinement's own binder: the predicate already
            // projects `.0` out of it, so what changes is which pair it projects from.
            Subst::discharge(binder.clone(), elem.clone_preserving_ids()).apply_expr(&onto_pair)
        })
        .collect();
    let old_domain = (**domain).clone();
    let fun_kind = fun_kind.clone();
    let codomain = (**codomain).clone();
    retype_subtree(g, &old_domain, &pair_ty);
    g.ty = Type::Fun {
        name: None,
        fun_kind,
        domain: Box::new(pair_ty.clone()),
        codomain: codomain.clone().into(),
    };
    // **The filter becomes a term, not a domain refinement.** `filter_values` is the
    // value-preserving mid-chain filter lambda elimination already emits for a gate that
    // varies with the element (`src/ccl/ops.rs`, `Builtin::FilterValues`), and a gate that
    // varies with the row is the same thing. Stamped `𝐷 ⇒ 𝐷` rather than at a refined
    // domain for the reason that arm records: a refinement type here would have planning
    // inject its own value-dropping `restrict` beside it.
    let chain = rebased.into_iter().fold(
        std::mem::replace(g, Expr::builtin(Builtin::Id)),
        |acc, predicate| {
            let p = fn_of_bare_predicate(&pair_ty, &predicate, &[]);
            let filter = apply_primitive(
                p,
                Builtin::FilterValues,
                Type::fun(pair_ty.clone(), pair_ty.clone()),
            );
            compose(filter, acc).with_ty(Type::fun(pair_ty.clone(), codomain.clone()))
        },
    );
    *g = chain;
    true
}

/// Whether a refinement's predicate names a pair binder free — the domain-side spelling,
/// where no binder scopes and the reference is an ordinary free name.
fn references_pair(r: &Refinement) -> bool {
    free_names_in_value(&r.predicate)
        .iter()
        .any(Name::is_synthetic_pair)
}

/// Apply [`replace_domain`] to every type slot in `e` and below it: the pair domain is the
/// type every morphism in the chain is written at, so one slot is never the only one.
fn retype_subtree(e: &mut Expr, old: &Type, bare: &Type) {
    e.walk_type_slots_mut(|ty| replace_domain(ty, old, bare));
    e.walk_children_mut(|child| retype_subtree(child, old, bare));
}

/// Replace the dependent pair domain with its bare product wherever it occurs, and drop the
/// component refinement it carried — the refinement now rides the pair.
fn replace_domain(ty: &mut Type, old: &Type, bare: &Type) {
    if ty == old {
        *ty = bare.clone();
        return;
    }
    if let Type::Refinement(base, set) = ty
        && set.as_slice().iter().any(references_pair)
    {
        *ty = (**base).clone();
        return replace_domain(ty, old, bare);
    }
    // A pair binder in the **codomain** is stored positionally, not as a name: the binder
    // scopes there, so `free_names_in_value` sees nothing and only the enclosing function
    // says what the index points at. Strip the refinement that carries it and the binder
    // with it — what it said now rides the domain.
    if let Type::Fun {
        name: Some(binder),
        codomain,
        ..
    } = ty
        && binder.is_synthetic_pair()
    {
        if let Type::Refinement(base, _) = codomain.as_mut() {
            let bare = (**base).clone();
            **codomain = bare;
        }
        if let Type::Fun { name, .. } = ty {
            *name = None;
        }
    }
    ty.walk_children_mut(|child| replace_domain(child, old, bare));
}

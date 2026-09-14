//! The two rewrites a **correlated** comprehension's `curry` site needs.
//!
//! An inner comprehension whose body reads the outer binder runs once per outer row, and
//! `lambda_elim` writes that as `curry(𝑔)` over the outer stream, where `𝑔` takes the pair
//! `(outer value, inner element)`. Both rewrites read that pair.
//!
//! **The inner source is named** ([`name_correlated_sources`]). The collection `curry`
//! produces is over the second half of the pair, and the term does not say what its domain
//! is: `𝑔` reaches the inner source only by applying it at the pair's `.1`, never by naming
//! it.
//!
//! A type answers only where it **gives** that domain. A list literal's is an index range,
//! which `extent_of` reads straight off as a bound [`IterateExtent`] can enumerate. A map's
//! is the present-key refinement `{𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`, and `extent_of`
//! strips the refinement and answers the whole key type — unbounded, so nothing can iterate
//! it, and the refinement that would have narrowed it is carried and never executed. The
//! domain is in the data, so the term has to name it, and the site is rewritten to
//! [`Builtin::CurryOver`], which does.
//!
//! **A filter is re-based onto the pair** ([`rebase_pair_filter`]). The pairing rule leaves a
//! filter as a refinement on the pair domain's second component, where nothing applies it. A
//! predicate that reads the outer value reaches it through the enclosing binder — a
//! reference no binder binds, and one that keeps the predicate from being the value function
//! a compiled refinement has to be. Re-based onto the product it names the same set with
//! nothing free, and it is emitted as `filter_values` so that something applies it.
//!
//! **A body that never applies the inner source leaves nothing to name**, and is the second
//! of the two routes rather than a failure of the first. `sum([r for v in xs])` under a
//! correlated site reads the outer binder alone, so `𝑔` is `.0` and the source occurs
//! nowhere in the term. Such a site keeps its `curry`, and op-conversion reads the domain
//! off the type instead.
//!
//! The two routes therefore need the collection in different places. A list literal's domain
//! type gives an index range outright, so reading the type serves it. A map's gives
//! `{𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`, where the collection sits inside the refinement
//! `extent_of` strips, so reading the type answers the unbounded key type. Naming the source
//! serves a map, and needs the source in the term.
//!
//! A map whose body never applies it is therefore served by neither — but that is not a
//! property of these two routes. The same program without an enclosing comprehension fails
//! as well (`a_map_comprehension_that_ignores_the_element_does_not_compile`): a collection
//! reached only through its carried `collection_contains` is a gap this module neither
//! creates nor closes.

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
/// `map_domain` and not `𝑠` itself: [`Builtin::CurryOver`] reads the domain off its source's
/// codomain, and a collection carries values there. Re-viewing it at its own domain is what
/// puts the keys where they are read.
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
    let [_, inner_domain] = pair.as_slice() else {
        return None;
    };
    let source = inner_source(g, inner_domain)?;
    let source_ty = Type::data_fun(inner_domain.clone(), inner_domain.clone());
    // A **recorded copy**: the source stays where it is inside `𝑔`, which applies it at each
    // element, and this second occurrence re-views it at its domain. `Clone` re-mints the
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

/// The collection `g` applies at the pair's second component, whose domain is the one the
/// curried collection is over.
///
/// The search is for the spelling `lambda_elim` leaves — a chain headed by `.1` — and is
/// coupled to it the way a site matcher is. The domain check is what keeps an unrelated
/// `.1` out: a pair's second component is projected wherever the body reads the element,
/// and only the one feeding a collection over that domain names the source.
fn inner_source<'a>(g: &'a Expr, inner_domain: &Type) -> Option<&'a Expr> {
    // A nested `curry` is a different site, reaching its own source at its own pair's `.1`,
    // and [`name_correlated_sources`] visits it separately. Descending lets this site name
    // that one's collection wherever the two domains agree — which two literal ranges of the
    // same length routinely do.
    if let TypedExprNode::Apply { function, .. } = &g.node
        && is_builtin(function, Builtin::Curry)
    {
        return None;
    }
    if let TypedExprNode::Compose(elements) = &g.node
        && let [head, source, ..] = elements.as_slice()
        && matches!(&head.node, TypedExprNode::Proj(ProjKey::Index(1)))
        && source.ty.domain().is_some_and(|d| &d == inner_domain)
    {
        return Some(source);
    }
    let mut found = None;
    g.walk_children(|child| {
        if found.is_none() {
            found = inner_source(child, inner_domain);
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
    // **The pair binder is free here when the predicate reads the outer value, and has
    // to be.** A `Type::Fun`'s binder scopes over its codomain, so a domain referencing
    // the function's own parameter names something no binder binds — which is what the
    // pairing rule writes when it substitutes the outer binder for `pair.0` inside the
    // second component's type. The name is read off the predicate rather than off the
    // function for that reason.
    //
    // A predicate that reads only the inner element names no binder at all. It still has
    // to be re-based and emitted, because the refinement rides the pair domain either
    // way and nothing else applies it; only the outer reference needs discharging.
    let binder = filters
        .as_slice()
        .iter()
        .flat_map(|r| free_names_in_value(&r.predicate))
        .find(Name::is_synthetic_pair);
    // A keyed collection's domain carries a present-key membership predicate that is never
    // executed (`Refinement::is_collection_membership`), so emitting it as a term is wrong.
    // A correlated predicate is recognisable by its binder and rides alongside one safely;
    // an uncorrelated one is not distinguishable from the carried predicate here, so a
    // component carrying one is left alone.
    if binder.is_none()
        && filters
            .as_slice()
            .iter()
            .any(Refinement::is_collection_membership)
    {
        return false;
    }
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
            match &binder {
                // The pair binder becomes the refinement's own binder: the predicate
                // already projects `.0` out of it, so what changes is which pair it
                // projects from.
                Some(binder) => Subst::discharge(binder.clone(), elem.clone_preserving_ids())
                    .apply_expr(&onto_pair),
                // Nothing outer is read, so re-basing onto the pair is the whole rewrite.
                None => onto_pair,
            }
        })
        .collect();
    let old_domain = (**domain).clone();
    let moved = Type::Refinement(inner.clone(), filters.clone());
    let bare_inner = (**inner).clone();
    let fun_kind = fun_kind.clone();
    let codomain = (**codomain).clone();
    retype_subtree(g, &old_domain, &pair_ty, &moved, &bare_inner);
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
fn retype_subtree(e: &mut Expr, old: &Type, bare: &Type, moved: &Type, kept: &Type) {
    e.walk_type_slots_mut(|ty| replace_domain(ty, old, bare, moved, kept));
    e.walk_children_mut(|child| retype_subtree(child, old, bare, moved, kept));
}

/// Replace the dependent pair domain with its bare product wherever it occurs, and drop the
/// component refinement it carried — the refinement now rides the pair.
fn replace_domain(ty: &mut Type, old: &Type, bare: &Type, moved: &Type, kept: &Type) {
    if ty == old {
        *ty = bare.clone();
        return;
    }
    // **The refinement that moved is stripped wherever it is written, not only where it
    // names the pair.** A filter reading the outer value leaves a reference this can
    // recognise; one reading only the element leaves an ordinary refinement, and a slot
    // still carrying it would disagree with the bare pair the chain is now written at.
    if ty == moved {
        *ty = kept.clone();
        return;
    }
    if let Type::Refinement(base, set) = ty
        && set.as_slice().iter().any(references_pair)
    {
        *ty = (**base).clone();
        return replace_domain(ty, old, bare, moved, kept);
    }
    // A pair binder in the **codomain** is stored positionally, not as a name: the binder
    // scopes there, so `free_names_in_value` sees nothing and only the enclosing function
    // says what the index points at. Strip the refinement that carries it and the binder
    // with it — what it said now rides the domain.
    if let Type::Fun {
        name: name @ Some(_),
        codomain,
        ..
    } = ty
        && name.as_ref().is_some_and(Name::is_synthetic_pair)
    {
        if let Type::Refinement(base, _) = codomain.as_mut() {
            let bare = (**base).clone();
            **codomain = bare;
        }
        *name = None;
    }
    ty.walk_children_mut(|child| replace_domain(child, old, bare, moved, kept));
}

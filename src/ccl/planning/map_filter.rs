//! Per-group filter planning: materialize a refinement that rides an inner
//! collection's domain as a [`Builtin::MapFilter`].

use super::{join::combine_predicates, *};
use crate::ccl::{Refinement, application_order, subst::open_codomain};

/// Insert a `map_filter` wherever a morphism's codomain refines the collection its
/// domain carries.
///
/// The site is `𝑚 : (𝑔: {𝐷 | 𝑟} ⤇ 𝑊) ⇒ ({𝐷 | 𝑟, 𝑝(𝑔)} ⤇ 𝑉)` — a morphism taking a
/// collection and returning one over a *narrower* domain, with the binder `𝑔` free in
/// the refinements the codomain adds. Only a per-group filter produces that: an inner
/// comprehension over the outer binder (`sum([s.amount for s in g if s.qty > 2])`),
/// where the surviving elements differ per key. `wrap_with_iterate` cannot reach it —
/// it materializes refinements on a node's own domain, and this one is a codomain in.
///
/// The narrowing is the **difference** between the two refinement sets, not whichever
/// refinement sits outermost: a set has no outermost member, and the site's domain
/// already carries every refinement its upstream materialized (the group predicate,
/// for a per-group filter).
///
/// Each added predicate reads `__elem ▷ (𝑔 ≫ 𝑞)`: index `__elem`, looked up in the
/// collection, satisfies 𝑞. The lookup is what makes the predicate mention 𝑔 at all,
/// so filtering the collection whose values 𝑔 denotes leaves 𝑞 as the value
/// predicate, and the rewrite is
///
/// ```text
/// 𝑢 ≫ 𝑚   ⟹   𝑢 ≫ map_filter(𝑞₁ and … and 𝑞ₙ) ≫ 𝑚'
/// ```
///
/// with `𝑚'` re-typed to take the narrowed collection. A refinement set narrows by the
/// conjunction of its members, so a whole difference materializes as one `map_filter`
/// over the conjoined value predicate rather than a chain of them, and every 𝑞ₖ stays
/// stated against the collection the site is handed. The conjunction is built in
/// [`application_order`], so the emitted term is a function of which refinements the
/// difference holds rather than of the order they accumulated in.
///
/// The rewrite retires the site's Pi binder, and the predicates it bound name 𝑔 free in
/// every type emitted here. One spelling has to serve both the filter's codomain and
/// the site's domain, and a domain is a position no binder scopes over: an index there
/// resolves against the enclosing function rather than the collection.
///
/// A site whose added refinements do not all dereference 𝑔 is left alone: nothing here
/// knows what stream to evaluate such a predicate against, and materializing the rest
/// would leave the site claiming a narrowing it no longer performs. An unmaterialized
/// refinement is caught by the check at the end of planning rather than silently
/// dropped.
pub(super) fn insert_map_filters(expr: &mut Expr) {
    expr.walk_children_mut(insert_map_filters);
    let TypedExprNode::Compose(elts) = &expr.node else {
        return;
    };
    let Some(site) = elts.iter().position(|e| map_filter_site(e).is_some()) else {
        return;
    };
    // `site` is never 0: the morphism consumes a collection, so something upstream
    // produces one.
    if site == 0 {
        return;
    }
    let TypedExprNode::Compose(elts) = &mut expr.node else {
        unreachable!("matched a Compose above")
    };
    let Some((site_codomain, value_predicate)) = map_filter_site(&elts[site]) else {
        unreachable!("position found it")
    };
    let narrowed = site_codomain
        .domain()
        .expect("a map_filter site returns a collection");
    // `map_filter(𝑞) : (𝐷 ⤇ 𝑊) ⇒ ({𝐷 | 𝑝} ⤇ 𝑊)` — same values, fewer of them.
    let upstream_codomain = elts[site]
        .ty
        .domain()
        .expect("a map_filter site's own type is a function");
    let carried = upstream_codomain
        .codomain()
        .expect("a map_filter site takes a collection");
    let filtered = Type::fun_like(&upstream_codomain, narrowed, carried);
    let map_filter = apply_primitive(
        value_predicate,
        Builtin::MapFilter,
        Type::fun(upstream_codomain, filtered.clone()),
    );
    // The site now takes the narrowed collection, and its Pi binder retires. An
    // `Apply`'s function slot carries the same arrow, so it is re-typed with the node:
    // leaving it behind makes the node disagree with itself.
    let retyped = Type::fun(filtered, site_codomain);
    if let TypedExprNode::Apply { argument, function } = &mut elts[site].node {
        function.ty = Type::fun(argument.ty.clone(), retyped.clone());
    }
    elts[site].ty = retyped;
    elts.insert(site, map_filter);
}

/// The site's codomain and the value predicate to filter by, if `expr` is a per-group
/// filter site. See [`insert_map_filters`] for the shape.
///
/// The codomain comes back **opened**: a reference to the site's Pi binder is stored as
/// an index, and every use here needs the name — matching a predicate against the
/// binder, and emitting types in which that binder no longer exists.
fn map_filter_site(expr: &Expr) -> Option<(Type, Expr)> {
    let Type::Fun {
        name: Some(binder),
        domain,
        codomain,
        ..
    } = &expr.ty
    else {
        return None;
    };
    let consumed = domain.domain()?;
    let opened = open_codomain(&expr.ty, codomain);
    let narrowed = opened.domain()?;
    // The narrowing must be of the collection the site consumes; a refinement over
    // some unrelated domain is not this shape, and neither is a codomain that *drops*
    // one of the refinements the domain carries — the rewrite only ever adds filters.
    if narrowed.peel_refinements() != consumed.peel_refinements() {
        return None;
    }
    let already = consumed.refinements();
    if !already.iter().all(|r| narrowed.refinements().contains(r)) {
        return None;
    }
    let added: Vec<Refinement> = narrowed
        .refinements()
        .iter()
        .filter(|r| !already.contains(r))
        .cloned()
        .collect();
    // `application_order` is the one place planning fixes an order on a refinement
    // set. One `map_filter` materializes the whole conjunction, so the element types
    // it pairs with — the stages of a filter *pipeline* — have no counterpart here.
    let mut conjoined = None;
    for (r, _) in application_order(&added, &consumed) {
        conjoined = combine_predicates(conjoined, Some(value_predicate(&r.predicate, binder)?));
    }
    Some((opened, conjoined?))
}

/// Strip `__elem ▷ (𝑔 ≫ 𝑞)` down to `𝑞`, the predicate on the collection's values.
///
/// Returns `None` for any other shape, including a predicate that never dereferences
/// `𝑔`: the rewrite is only sound when the collection being filtered is the one the
/// predicate reads through.
fn value_predicate(predicate: &Expr, binder: &Name) -> Option<Expr> {
    let TypedExprNode::Apply { argument, function } = &predicate.node else {
        return None;
    };
    if !matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem()) {
        return None;
    }
    let TypedExprNode::Compose(chain) = &function.node else {
        return None;
    };
    let [head, rest @ ..] = chain.as_slice() else {
        return None;
    };
    if !matches!(&head.node, TypedExprNode::Var(n) if n == binder) {
        return None;
    }
    match rest {
        [] => None,
        [only] => Some(only.clone()),
        many => {
            let ty = match (many.first()?.ty.domain(), many.last()?.ty.codomain()) {
                (Some(d), Some(c)) => Type::fun(d, c),
                _ => Type::Hole,
            };
            Some(Expr::compose(many.to_vec()).with_ty(ty))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    use crate::ccl::{RefinementSet, planning::test_helpers::*};

    /// A collection over the indices `[0, 2]` carrying records, narrowed by
    /// `refinements` on its domain.
    fn collection(refinements: RefinementSet, value: Type) -> Type {
        let idx = Type::UIntRange(3);
        Type::data_fun(Type::refined(idx, refinements), value)
    }

    /// The bare predicate `__elem ▷ (𝑔 ≫ 𝑞)` a per-group filter leaves on the inner
    /// collection's domain, with `q` a named stand-in for the compiled value
    /// predicate.
    fn group_filter_predicate(binder: &Name, q: &str, value: Type) -> Refinement {
        let idx = Type::UIntRange(3);
        let lookup = Expr::compose(vec![
            var(binder.base()).with_ty(collection(RefinementSet::new(), value.clone())),
            var(q).with_ty(fun_ty(value, bool_ty())),
        ])
        .with_ty(fun_ty(idx.clone(), bool_ty()));
        let predicate =
            Expr::apply(Expr::var(Name::elem()).with_ty(idx), lookup).with_ty(bool_ty());
        Refinement::born(Rc::new(predicate))
    }

    /// `𝑢 ≫ 𝑚` with `𝑚 : (𝑔: 𝐷 ⤇ 𝑊) ⇒ ({𝐷 | 𝑝₁(𝑔), 𝑝₂(𝑔)} ⤇ Int)`.
    fn site_adding(predicates: &[&str]) -> (Expr, Name) {
        let value = tuple_ty(vec![int_ty()]);
        let binder = Name::from("g");
        let mut added = RefinementSet::new();
        for q in predicates {
            added.insert(group_filter_predicate(&binder, q, value.clone()));
        }
        let unfiltered = collection(RefinementSet::new(), value.clone());
        let site = var("m").with_ty(Type::pi(
            binder.clone(),
            unfiltered.clone(),
            collection(added, value),
        ));
        let chain = Expr::compose(vec![var("u").with_ty(unfiltered), site]);
        (chain, binder)
    }

    /// The `map_filter` inserted at a site, and the type the site was left with.
    fn planned(expr: &Expr) -> (Option<&Expr>, Type) {
        let TypedExprNode::Compose(elts) = &expr.node else {
            panic!("planning kept the chain a Compose");
        };
        match elts.as_slice() {
            [_, filter, site] => (Some(filter), site.ty.clone()),
            [_, site] => (None, site.ty.clone()),
            other => panic!("unexpected chain of {} elements", other.len()),
        }
    }

    /// A whole refinement-set difference materializes as **one** `map_filter` over the
    /// conjoined value predicate: the set narrows by the conjunction of its members,
    /// and one filter keeps every conjunct stated against the collection the site is
    /// handed rather than against a chain of intermediate ones.
    #[test]
    fn two_added_refinements_become_one_conjoined_map_filter() {
        let (mut expr, _) = site_adding(&["q1", "q2"]);
        insert_map_filters(&mut expr);
        let (filter, site_ty) = planned(&expr);
        let filter = filter.expect("the site narrows, so a map_filter was inserted");
        assert_eq!(symbolic(filter), "((q1, q2) ▷ zip ≫ and) ▷ map_filter");
        // The filter delivers exactly what the site now takes: one type, so the
        // post-planning `typecheck` chains them.
        let filtered = filter.ty.codomain().expect("map_filter is a function");
        assert_eq!(site_ty.domain(), Some(filtered));
    }

    /// All-or-nothing: an added refinement that never dereferences the binder leaves
    /// the whole site alone. Materializing only its siblings would leave the site
    /// claiming a narrowing it no longer performs, and the unmaterialized refinement
    /// is reported at the end of planning instead.
    #[test]
    fn a_refinement_that_does_not_dereference_the_binder_blocks_the_site() {
        let (mut expr, _) = site_adding(&["q1"]);
        let TypedExprNode::Compose(elts) = &mut expr.node else {
            unreachable!("built a Compose")
        };
        let idx = Type::UIntRange(3);
        let closed = Refinement::born(Rc::new(
            Expr::apply(
                Expr::var(Name::elem()).with_ty(idx.clone()),
                var("closed").with_ty(fun_ty(idx, bool_ty())),
            )
            .with_ty(bool_ty()),
        ));
        let Type::Fun { codomain, .. } = &mut elts[1].ty else {
            unreachable!("built a Pi")
        };
        let Type::Fun { domain, .. } = codomain.as_mut() else {
            unreachable!("built a collection codomain")
        };
        let Type::Refinement(_, refinements) = domain.as_mut() else {
            unreachable!("built a refined domain")
        };
        refinements.insert(closed);

        let before = expr.clone();
        insert_map_filters(&mut expr);
        assert_eq!(planned(&expr).0, None, "no map_filter was inserted");
        assert_eq!(expr, before, "the site is untouched");
    }
}

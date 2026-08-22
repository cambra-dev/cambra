//! Per-group filter planning: materialize a refinement that rides an inner
//! collection's domain as a [`Builtin::MapFilter`].

use super::*;

/// Insert a `map_filter` wherever a morphism's codomain refines the collection its
/// domain carries.
///
/// The site is `𝑚 : (𝑔: 𝐷 ⤇ 𝑊) ⇒ ({𝐷 | 𝑝(𝑔)} ⤇ 𝑉)` — a morphism taking a collection
/// and returning one over a *narrower* domain, with the binder `𝑔` free in the
/// narrowing predicate. Only a per-group filter produces that: an inner comprehension
/// over the outer binder (`sum([s.amount for s in g if s.qty > 2])`), where the
/// surviving elements differ per key. `wrap_with_iterate` cannot reach it — it
/// materializes refinements on a node's own domain, and this one is a codomain in.
///
/// The predicate reads `__elem ▷ (𝑔 ≫ 𝑞)`: index `__elem`, looked up in the
/// collection, satisfies 𝑞. The lookup is what makes the predicate mention 𝑔 at all,
/// so filtering the collection whose values 𝑔 denotes leaves 𝑞 as the value
/// predicate, and the rewrite is
///
/// ```text
/// 𝑢 ≫ 𝑚   ⟹   𝑢 ≫ map_filter(𝑞) ≫ 𝑚'
/// ```
///
/// with `𝑚'` re-typed to take the narrowed collection. A predicate that does not
/// dereference `𝑔` is left alone: nothing here knows what stream to evaluate it
/// against, and leaving the refinement unmaterialized is caught by the check at the
/// end of planning rather than silently dropped.
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
    let Some((narrowed, value_predicate)) = map_filter_site(&elts[site]) else {
        unreachable!("position found it")
    };
    // `map_filter(𝑞) : (𝐷 ⤇ 𝑊) ⇒ ({𝐷 | 𝑝} ⤇ 𝑊)` — same values, fewer of them.
    let upstream_codomain = elts[site]
        .ty
        .domain()
        .expect("a map_filter site's own type is a function");
    let carried = upstream_codomain
        .codomain()
        .expect("a map_filter site takes a collection");
    let filtered = Type::fun_like(&upstream_codomain, narrowed.clone(), carried);
    let map_filter = apply_primitive(
        value_predicate,
        Builtin::MapFilter,
        Type::fun(upstream_codomain, filtered.clone()),
    );
    // The site now takes the narrowed collection, and its Pi binder retires with the
    // refinement it bound. An `Apply`'s function slot carries the same arrow, so it is
    // re-typed with the node: leaving it behind makes the node disagree with itself.
    let site_codomain = elts[site]
        .ty
        .codomain()
        .expect("a map_filter site's own type is a function");
    let retyped = Type::fun(filtered, site_codomain);
    if let TypedExprNode::Apply { argument, function } = &mut elts[site].node {
        function.ty = Type::fun(argument.ty.clone(), retyped.clone());
    }
    elts[site].ty = retyped;
    elts.insert(site, map_filter);
}

/// The narrowed inner domain and the value predicate to filter by, if `expr` is a
/// per-group filter site. See [`insert_map_filters`] for the shape.
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
    let narrowed = codomain.domain()?;
    let Type::Refinement(base, refinement) = &narrowed else {
        return None;
    };
    // The narrowing must be of the collection the site consumes; a refinement over
    // some unrelated domain is not this shape.
    if base.as_ref() != &domain.domain()? {
        return None;
    }
    Some((
        narrowed.clone(),
        value_predicate(&refinement.predicate, binder)?,
    ))
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

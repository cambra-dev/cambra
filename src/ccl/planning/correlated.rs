//! Name the inner source of a **correlated** comprehension.
//!
//! An inner comprehension whose body reads the outer binder runs once per outer row, and
//! `lambda_elim` writes that as `curry(𝑔)` over the outer collection, where `𝑔` takes the pair
//! `(outer value, inner element)`. The collection `curry` produces is over the second half
//! of that pair, and the term does not say what its domain is: `𝑔` reaches the inner source
//! only by applying it at the pair's `.1`, never by naming it.
//!
//! A type answers only where it **gives** that domain. A list literal's is an index range,
//! which `extent_of` reads straight off as a bound [`IterateExtent`] can enumerate. A map's
//! is the present-key refinement `{𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`, and `extent_of`
//! strips the refinement and answers the whole key type — unbounded, so nothing can iterate
//! it, and the refinement that would have narrowed it is carried and never executed. The
//! domain is in the data, so the term has to name it, and [`name_correlated_sources`]
//! rewrites the site to [`Builtin::CurryOver`], which does.
//!
//! **A body that never applies the inner source leaves nothing to name**, and is the second
//! of the two routes rather than a failure of the first. `sum([r for v in xs])` under a
//! correlated site reads the outer binder alone, so `𝑔` is `.0` and the source occurs
//! nowhere in the term. Such a site keeps its `curry`, and op-conversion reads the domain
//! off the type instead.
//!
//! A map whose body never applies it is therefore served by neither — but that is not a
//! property of these two routes. The same program without an enclosing comprehension fails
//! as well (`a_map_comprehension_that_ignores_the_element_does_not_compile`): a collection
//! reached only through its carried `collection_contains` is a gap this module neither
//! creates nor closes.

use super::*;

/// Rewrite every correlated curry site to name its inner source.
///
/// Runs before the iteration-site walk, so the `map_domain` this mints is marked like any
/// other iteration source.
pub(super) fn name_correlated_sources(expr: &mut Expr) {
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
    let Some(Type::Tuple(pair)) = g.ty.domain() else {
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

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
    let Some(Type::Tuple(pair)) = g.ty.domain() else {
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

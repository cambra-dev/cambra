//! The two rewrites a **correlated** comprehension's `curry` site needs.
//!
//! Neither moves a refinement to make it compile. Where a refinement sits is decided by what
//! it says — a present-key proof rides the binder whose lookup reads it, a filter rides the
//! pair it selects from — and `lambda_elim` places both. What is left here is naming a
//! domain the term does not carry, and applying a filter nothing else applies.
//!
//! An inner comprehension whose body reads the outer binder runs once per outer row, and
//! `lambda_elim` writes that as `curry(𝑔)` over the outer collection, where `𝑔` takes the pair
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
//! **The filter riding the pair is emitted** ([`emit_pair_filter`]). `lambda_elim` puts a
//! filter on the inner binder onto the pair, as a refinement on the product whose own
//! `__elem` binds both halves. Applying it is what is left: a refinement is a fact about the
//! domain, and only a term filters. The site is a morphism under `curry` rather than an
//! iteration site, so `planning::iterate`'s `iterate`-then-`restrict` chain never reaches
//! it, and `filter_values` is emitted here instead.
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
use std::rc::Rc;

use crate::ccl::TypedExpr;

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
        if emit_pair_filter(argument) {
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
        // The result is `map_domain`'s argument, so it has to be a collection. The
        // domain check alone lets a projection through wherever its domain happens to
        // equal the inner one — two pairs of the same type routinely do — and
        // `map_domain` of a projection denotes nothing.
        && source
            .ty
            .fun_kind()
            .is_some_and(|k| k.resolved().is_data())
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

/// Emit the filter riding a correlated site's pair domain, as a term.
///
/// `lambda_elim` puts a filter on the inner binder onto the pair as a refinement on the
/// product, where the refinement's own `__elem` binds both halves and nothing is free. What
/// it cannot do is *apply* it: a refinement is a fact about the domain, and only a term
/// filters. Nothing else applies this one, because the site is a morphism under `curry`
/// rather than an iteration site, so `planning::iterate`'s `iterate`-then-`restrict` chain
/// never reaches it.
///
/// `filter_values` is the value-preserving mid-chain filter lambda elimination already emits
/// for a gate that varies with the element (`src/ccl/ops.rs`, `Builtin::FilterValues`), and a
/// gate that varies with the row is the same thing. The domain loses the refinement in every
/// slot the chain is written at, because the term now carries it.
fn emit_pair_filter(g: &mut Expr) -> bool {
    let Type::Fun {
        fun_kind,
        domain,
        codomain,
        ..
    } = &g.ty
    else {
        return false;
    };
    let Type::Refinement(bare, filters) = domain.as_ref() else {
        return false;
    };
    if !matches!(bare.as_ref(), Type::Tuple(components) if components.len() == 2) {
        return false;
    }
    let pair_ty = (**bare).clone();
    let predicates: Vec<Rc<TypedExpr>> = filters
        .as_slice()
        .iter()
        .map(|r| Rc::clone(&r.predicate))
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
    let chain = predicates.into_iter().fold(
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

/// Rewrite the refined pair domain to its bare product in every type slot at or below `e`:
/// the domain is the type every morphism in the chain is written at, so one slot is never
/// the only one.
fn retype_subtree(e: &mut Expr, old: &Type, bare: &Type) {
    e.walk_type_slots_mut(|ty| replace_domain(ty, old, bare));
    e.walk_children_mut(|child| retype_subtree(child, old, bare));
}

/// Replace the refined pair with its bare product wherever it occurs inside `ty`, not only
/// where `ty` is it: a morphism in the chain is written at `pair ⇒ 𝑉`, so the occurrence
/// is the domain of a function type rather than the slot itself.
fn replace_domain(ty: &mut Type, old: &Type, bare: &Type) {
    if ty == old {
        *ty = bare.clone();
        return;
    }
    ty.walk_children_mut(|child| replace_domain(child, old, bare));
}

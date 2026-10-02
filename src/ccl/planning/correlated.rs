//! A **correlated** comprehension's `curry` site, rewritten through `strength`.
//!
//! An inner comprehension whose body reads the outer binder runs once per outer row, and
//! `lambda_elim` writes that as `curry(𝑔)` over the outer collection, where `𝑔` takes the pair
//! `(outer value, inner element)`. Op-conversion has no operator for `curry`, so planning
//! rewrites each site to the combinators it compiles:
//!
//! ```text
//! curry(𝑔)  ⟹  ⟨id, const(𝐾)⟩ ▷ zip ≫ strength ≫ map(𝑔)
//! ```
//!
//! `𝐾 : 𝐷 ⤇ 𝐷` is the collection the inner comprehension ranges over, holding its keys as its
//! values, so `strength` ([`Builtin::Strength`]) pairs each outer value with each key, and
//! `map(𝑔)` runs `𝑔` over the pairs. It is the rule `simplify` applies to a generator over a
//! sum (`src/ccl/design/optimization.md`, "A generator over a sum composes with its source"),
//! with a collection that is the same for every row: `const` shares one collection between
//! all of them.
//!
//! **The filter riding the pair is emitted first** ([`emit_pair_filter`]). `lambda_elim` puts
//! a filter on the inner binder onto the pair, as a refinement on the product whose own
//! `__elem` binds both halves. Applying it is what is left: a refinement is a fact about the
//! domain, and only a term filters. The site is a morphism under `curry` rather than an
//! iteration site, so `planning::iterate`'s `iterate`-then-`restrict` chain never reaches
//! it, and `filter_values` is emitted here instead.
//!
//! **`𝐾` is the inner source where the body names one.** `𝑔` reaches the inner source only by
//! applying it at the pair's `.1`, and that source re-viewed at its own domain,
//! `map_domain(𝑠)`, is `𝐾`. A type cannot stand in for it in general: a list literal's
//! domain is an index range, which `extent_of` reads straight off as a bound
//! [`IterateExtent`] can enumerate, but a map's is the membership refinement
//! `{𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`, whose keys are in the data.
//!
//! **A body that never applies the inner source leaves nothing to name.** `sum([r for v in
//! xs])` under a correlated site reads the outer binder alone, so `𝑔` is `.0` and the source
//! occurs nowhere in the term. `𝐾` is then `iterate` over the type's domain, which answers
//! for a list literal. A map read that way is refused by name, as the same comprehension is
//! without an enclosing one (`a_map_comprehension_that_ignores_the_element_does_not_compile`).
//!
//! **A dependent site stays one node.** A correlated filter narrows the inner domain by the
//! outer value, so `curry(𝑔)`'s type is `(𝑟 : 𝑋) ⇒ ({𝑣 : 𝐷 | 𝑣 > 𝑟} ⤇ 𝑊)`, and the chain has
//! no spelling for it. Such a site becomes `(𝐾, 𝑔) ▷ curry_over` under that type
//! ([`Builtin::CurryOver`]), and op-conversion builds the operators the chain compiles to.

use super::*;
use std::rc::Rc;

use crate::ccl::TypedExpr;
use crate::ccl::lambda_elim::zip_pair;

use super::predicates::fn_of_bare_predicate;

/// Emit the filter riding every correlated `curry` site's pair ([`emit_pair_filter`]).
///
/// Runs before planning's first `simplify`, which reads the pair domain the filter leaves.
pub(super) fn emit_correlated_filters(expr: &mut Expr) {
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
    expr.walk_children_mut(emit_correlated_filters);
}

/// Rewrite every correlated `curry` site through `strength`.
///
/// Runs after planning's first `simplify`, so a `curry` exponential eta reduces is gone
/// first, and before the iteration-site walk, so the `map_domain` this mints is marked like
/// any other iteration source.
pub(super) fn pair_correlated_sites(expr: &mut Expr) -> Result<(), String> {
    let rewritten = {
        let _g = provenance::enter(
            expr.node_id(),
            "planning.correlated",
            provenance::Nature::Machinery,
        );
        through_strength(expr)?
    };
    if let Some(rewritten) = rewritten {
        *expr = rewritten;
    }
    let mut result = Ok(());
    expr.walk_children_mut(|child| {
        if result.is_ok() {
            result = pair_correlated_sites(child);
        }
    });
    result
}

/// `curry(𝑔)` rewritten to `⟨id, const(𝐾)⟩ ▷ zip ≫ strength ≫ map(𝑔)`, `𝐾` being the
/// collection the site ranges over (the module doc says which). `None` where `expr` is not a
/// correlated site: a `curry` of a builtin is a partial application, which op-conversion
/// compiles as one.
fn through_strength(expr: &Expr) -> Result<Option<Expr>, String> {
    let TypedExprNode::Apply {
        argument: g,
        function,
    } = &expr.node
    else {
        return Ok(None);
    };
    if !is_builtin(function, Builtin::Curry) || matches!(g.node, TypedExprNode::Builtin(_)) {
        return Ok(None);
    }
    let Some(Type::Tuple(pair)) = g.ty.domain() else {
        return Err(format!(
            "a curried morphism takes the pair of what it is curried over and what it \
             iterates, so its domain is a two-element tuple; got {}",
            g.ty
        ));
    };
    let [enclosing, component] = pair.as_slice() else {
        return Err(format!(
            "a curried morphism's domain pairs exactly two, got {}",
            g.ty
        ));
    };
    // The component states what the element is, which includes a filter reading only the
    // element; the domain ranged over is the keys before any filter. The filter rides the
    // pair as well, which [`emit_pair_filter`] has applied, so the collection is matched — and
    // its keys enumerated — at the component's membership alone.
    let inner_domain = collection_domain(component);
    let keys = match inner_source(g, &inner_domain) {
        Some(source) => {
            // A **recorded copy**: the source stays where it is inside `𝑔`, which applies it
            // at each element, and this second occurrence re-views it at its domain. `Clone`
            // re-mints the ids and the frame records the parentage, as entry iteration's kept
            // collection does.
            let copy = {
                let _frame = provenance::copy_frame("planning.correlated_source");
                source.clone()
            };
            apply_primitive(
                copy,
                Builtin::MapDomain,
                Type::data_fun(inner_domain.clone(), inner_domain.clone()),
            )
        }
        None if inner_domain
            .refinements()
            .iter()
            .any(|r| r.is_collection_membership()) =>
        {
            return Err(format!(
                "a correlated inner comprehension over a collection its body never applies is \
                 not supported yet: its domain {inner_domain} is a membership refinement over \
                 the whole key type, which nothing enumerates"
            ));
        }
        None => make_iterate(trivially_true_predicate(inner_domain.clone())),
    };
    // **A dependent site** — a correlated filter narrows the inner domain by the outer
    // value, `(𝑟 : 𝑋) ⇒ ({𝑣 : 𝐷 | 𝑣 > 𝑟} ⤇ 𝑊)` — has no spelling as a chain: the narrowed
    // domain names the chain's input, which no element after the first takes. It stays one
    // node, `(𝐾, 𝑔) ▷ curry_over`, under `curry`'s own type, and op-conversion builds the
    // same operators the chain compiles to.
    if let Type::Fun {
        name: Some(binder),
        codomain,
        ..
    } = &expr.ty
        && crate::ccl::subst::codomain_depends_on(binder, codomain)
    {
        let keys_ty = keys.ty.clone();
        let pair = Expr::tuple(vec![keys, g.as_ref().clone_preserving_ids()])
            .with_ty(Type::Tuple(vec![keys_ty, g.ty.clone()]));
        return Ok(Some(apply_primitive(
            pair,
            Builtin::CurryOver,
            expr.ty.clone(),
        )));
    }
    let Some(curried) = expr.ty.codomain() else {
        unreachable!("`curry(𝑔)` is a function, got {}", expr.ty)
    };
    let Type::Fun { fun_kind, .. } = &expr.ty else {
        unreachable!("`curry(𝑔)` is a function, got {}", expr.ty)
    };
    let collection = keys.ty.clone();
    let strengthened = Type::fun_like(
        &collection,
        inner_domain.clone(),
        Type::Tuple(vec![enclosing.clone(), inner_domain.clone()]),
    );
    let with_keys = zip_pair(
        id().with_ty(Type::fun(enclosing.clone(), enclosing.clone())),
        apply_primitive(
            keys,
            Builtin::Const,
            Type::fun(enclosing.clone(), collection.clone()),
        ),
        fun_kind,
    );
    let strength = Expr::builtin(Builtin::Strength).with_ty(Type::fun(
        Type::Tuple(vec![enclosing.clone(), collection]),
        strengthened.clone(),
    ));
    // `map`'s stamp takes the pairs `strength` makes, which is what the rewritten chain feeds
    // it; `𝑔` keeps the pair type it was written at, as it did under `curry`.
    let map = apply_primitive(
        g.as_ref().clone_preserving_ids(),
        Builtin::Map,
        Type::fun(strengthened, curried),
    );
    Ok(Some(
        Expr::compose(vec![with_keys, strength, map]).with_ty(expr.ty.clone()),
    ))
}

/// `component` with only its membership refinements: the domain of the collection
/// it ranges over, without the filters a comprehension applies to the elements.
fn collection_domain(component: &Type) -> Type {
    let membership: Vec<_> = component
        .refinements()
        .iter()
        .filter(|r| r.is_collection_membership())
        .cloned()
        .collect();
    let base = component.peel_refinements().clone();
    match membership.is_empty() {
        true => base,
        false => {
            let mut set = crate::ccl::ty::RefinementSet::new();
            set.extend(membership);
            Type::refined(base, set)
        }
    }
}

/// The collection `g` applies at the pair's second component, whose domain is the one the
/// curried collection is over.
///
/// The search is for the spelling `lambda_elim` leaves — a chain headed by `.1` — and is
/// coupled to it the way a site matcher is. The domain check is what keeps an unrelated
/// `.1` out: a pair's second component is projected wherever the body reads the element,
/// and only the one feeding a collection over that domain names the source. Two collections
/// over one domain type hold the same keys, so which of them is found does not change `𝐾`.
fn inner_source<'a>(g: &'a Expr, inner_domain: &Type) -> Option<&'a Expr> {
    // A nested `curry` is a different site, reaching its own source at its own pair's `.1`,
    // and [`pair_correlated_sites`] visits it separately. Descending lets this site name
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

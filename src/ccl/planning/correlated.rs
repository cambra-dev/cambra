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
//! no spelling for it. Such a site becomes `(const(𝐾), 𝑔) ▷ curry_over` under that type
//! ([`Builtin::CurryOver`]), and op-conversion builds the operators the chain compiles to.

use super::*;
use std::rc::Rc;

use crate::ccl::TypedExpr;
use crate::ccl::lambda_elim::zip_pair;

use super::predicates::fn_of_bare_predicate;

/// Emit the filter riding every correlated `curry` site's pair ([`emit_pair_filter`]).
///
/// Runs before planning's first `simplify`, which reads the pair domain the filter leaves.
/// The error is planning's, from the filter it lifts ([`plan_before_iteration`]).
pub(super) fn emit_correlated_filters(
    expr: &mut Expr,
    witnesses: &mut Witnesses,
) -> Result<(), String> {
    let node_id = expr.node_id();
    if let TypedExprNode::Apply { argument, function } = &mut expr.node
        && is_builtin(function, Builtin::Curry)
    {
        let _g = provenance::enter(
            node_id,
            "planning.correlated_filter",
            provenance::Nature::Machinery,
        );
        if emit_pair_filter(argument, witnesses)? {
            // `curry`'s own stamp says what it takes; the argument's domain just moved.
            function.ty = Type::fun(argument.ty.clone(), expr.ty.clone());
        }
    }
    let mut result = Ok(());
    expr.walk_children_mut(|child| {
        if result.is_ok() {
            result = emit_correlated_filters(child, witnesses);
        }
    });
    result
}

/// Rewrite every correlated `curry` site through `strength`.
///
/// Runs after planning's first `simplify`, so a `curry` exponential eta reduces is gone
/// first, and before the iteration-site walk, so the `map_domain` this mints is marked like
/// any other iteration source.
pub(super) fn pair_correlated_sites(
    expr: &mut Expr,
    witnesses: &mut Witnesses,
) -> Result<(), String> {
    let rewritten = {
        let _g = provenance::enter(
            expr.node_id(),
            "planning.correlated",
            provenance::Nature::Machinery,
        );
        through_strength(expr, witnesses)?
    };
    if let Some(rewritten) = rewritten {
        *expr = rewritten;
    }
    let mut result = Ok(());
    expr.walk_children_mut(|child| {
        if result.is_ok() {
            result = pair_correlated_sites(child, witnesses);
        }
    });
    result
}

/// `curry(𝑔)` rewritten to `⟨id, const(𝐾)⟩ ▷ zip ≫ strength ≫ map(𝑔)`, `𝐾` being the
/// collection the site ranges over (the module doc says which). `None` where `expr` is not a
/// correlated site: a `curry` of a builtin is a partial application, which op-conversion
/// compiles as one.
fn through_strength(expr: &Expr, witnesses: &mut Witnesses) -> Result<Option<Expr>, String> {
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
    // **A dependent tuple's entries are a family**: for each enclosing value, the keys of
    // the component its type picks (`src/ccl/design/type-inference.md`, "Iterating a
    // dependent tuple"). The site pairs each enclosing value with its own keys rather
    // than with one collection every row shares.
    if let Some(Type::DepTuple(components)) = g.ty.domain().map(|d| d.peel_refinements().clone()) {
        let family = keys_family(&components, witnesses)?;
        let family_ty = family.ty.clone();
        let pair = Expr::tuple(vec![family, g.as_ref().clone_preserving_ids()])
            .with_ty(Type::Tuple(vec![family_ty, g.ty.clone()]));
        return Ok(Some(apply_primitive(
            pair,
            Builtin::CurryOver,
            expr.ty.clone(),
        )));
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
    // node, `(const(𝐾), 𝑔) ▷ curry_over`, under `curry`'s own type, and op-conversion builds
    // the same operators the chain compiles to. The keys are the family every row shares,
    // `const(𝐾)`, as a dependent tuple's are the family [`keys_family`] builds.
    if let Type::Fun {
        name: Some(binder),
        codomain,
        ..
    } = &expr.ty
        && crate::ccl::subst::codomain_depends_on(binder, codomain)
    {
        let collection = keys.ty.clone();
        let family = apply_primitive(
            keys,
            Builtin::Const,
            Type::fun(enclosing.clone(), collection),
        );
        let family_ty = family.ty.clone();
        let pair = Expr::tuple(vec![family, g.as_ref().clone_preserving_ids()])
            .with_ty(Type::Tuple(vec![family_ty, g.ty.clone()]));
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

/// The morphism taking an enclosing value `𝑥` to the keys of a dependent tuple's second
/// component at `𝑥`, as a collection holding its keys as its values: `𝐹 : (𝑥 : 𝑋) ⇒ (𝐷(𝑥) ⤇
/// 𝐷(𝑥))`.
///
/// The component is read under a name for `𝑥`. A membership refinement `{𝐾 | 𝑘 ∈ 𝑀(𝑥)}`
/// states the keys as the image of the collection `𝑀(𝑥)`, so the keys are
/// `map_domain(converse(𝑀(𝑥)))`, and `𝐹` is `(λ 𝑥 → 𝑀(𝑥)) ≫ converse ≫ map_domain`.
fn keys_family(
    components: &[(Option<Name>, Type)],
    witnesses: &mut Witnesses,
) -> Result<Expr, String> {
    let [(name, enclosing), (_, component)] = components else {
        return Err(format!(
            "a dependent tuple of {} components under one `curry` is not supported yet",
            components.len()
        ));
    };
    let x = name.clone().unwrap_or_else(|| Name::fresh("__x"));
    let component = crate::ccl::subst::open_pi_binder(
        &crate::ccl::subst::Mapping::Rename(x.clone()),
        component,
    );
    let image = component
        .refinements()
        .iter()
        .find_map(|r| {
            r.membership_collection()
                .filter(|collection| ccl_utils::is_free(&x, collection))
                .cloned()
        })
        .ok_or_else(|| {
            format!(
                "a dependent tuple whose second component {component} is not a membership \
                 reading the first is not supported yet"
            )
        })?;
    let keys = component.peel_refinements().clone();
    let indices = image
        .ty
        .domain()
        .ok_or_else(|| format!("a membership's collection is a function, got {}", image.ty))?;
    let image_ty = image.ty.clone();
    // Indexed, as a comprehension reaches lambda elimination: `λ 𝑟 → 𝑟 ▷ 𝑠 ▷ 𝑓` for the
    // chain `𝑠 ≫ 𝑓`, so the collection per `𝑥` is a correlated site planning rewrites
    // through `strength` rather than a `compose` of morphisms.
    let r = Name::fresh("__iter_record");
    let elements = match image.node {
        TypedExprNode::Compose(elements) => elements,
        node => vec![TypedExpr { node, ..image }],
    };
    let indexed = elements
        .into_iter()
        .fold(Expr::var(&r).with_ty(indices.clone()), |acc, f| {
            let ty = f.ty.codomain().unwrap_or_else(|| {
                panic!(
                    "a step of a membership's collection is a function, got {}",
                    f.ty
                )
            });
            Expr::apply(acc, f).with_ty(ty)
        });
    let per_row = predicates::eliminate_lifted(
        Expr::lambda(
            &x,
            enclosing.clone(),
            Expr::lambda(&r, indices.clone(), indexed).with_ty(image_ty.clone()),
        )
        .with_ty(Type::pi(x.clone(), enclosing.clone(), image_ty.clone())),
    )
    .map_err(|e| format!("eliminating a dependent tuple's key collection: {e:?}"))?;
    let mut per_row = plan_before_iteration(per_row, witnesses)?;
    // **The head binds `𝑥` for the whole chain**, whether or not its own codomain reads it:
    // the keys `map_domain` yields are the component at `𝑥`, so its type does, and a
    // chain scopes a morphism's binder over every morphism after it.
    if let Type::Fun {
        fun_kind,
        domain,
        codomain,
        ..
    } = &per_row.ty
    {
        per_row.ty = Type::pi_kinded(
            x.clone(),
            (**domain).clone(),
            (**codomain).clone(),
            fun_kind.clone(),
        );
    }
    let groups = Type::data_fun(
        keys.clone(),
        Type::data_fun(indices.clone(), indices.clone()),
    );
    let converse = Expr::builtin(Builtin::Converse).with_ty(Type::fun(image_ty, groups.clone()));
    let key_set = Type::data_fun(component.clone(), component.clone());
    let map_domain = Expr::builtin(Builtin::MapDomain).with_ty(Type::fun(groups, key_set.clone()));
    // Only the family itself binds `𝑥`, so only its type closes it. `converse` and
    // `map_domain` read it by name, as every morphism after a dependent head of a chain
    // reads that head's binder.
    Ok(
        Expr::compose(vec![per_row, converse, map_domain]).with_ty(Type::pi(
            x,
            enclosing.clone(),
            key_set,
        )),
    )
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
fn emit_pair_filter(g: &mut Expr, witnesses: &mut Witnesses) -> Result<bool, String> {
    if emit_component_filter(g, witnesses)? {
        return Ok(true);
    }
    let Type::Fun {
        name,
        fun_kind,
        domain,
        codomain,
    } = &g.ty
    else {
        return Ok(false);
    };
    let Type::Refinement(bare, filters) = domain.as_ref() else {
        return Ok(false);
    };
    if !matches!(bare.as_ref(), Type::Tuple(components) if components.len() == 2) {
        return Ok(false);
    }
    let pair_ty = (**bare).clone();
    let predicates: Vec<Rc<TypedExpr>> = filters
        .as_slice()
        .iter()
        .map(|r| Rc::clone(&r.predicate))
        .collect();
    let old_domain = (**domain).clone();
    // The binder stays: a row whose keys depend on the pair reads it in the codomain, which
    // is stored closed against it.
    let name = name.clone();
    let fun_kind = fun_kind.clone();
    let codomain = (**codomain).clone();
    retype_subtree(g, &old_domain, &pair_ty);
    g.ty = Type::Fun {
        name: name.clone(),
        fun_kind,
        domain: Box::new(pair_ty.clone()),
        codomain: codomain.clone().into(),
    };
    let mut chain = std::mem::replace(g, Expr::builtin(Builtin::Id));
    for predicate in predicates {
        let p = plan_before_iteration(fn_of_bare_predicate(&pair_ty, &predicate, &[]), witnesses)?;
        let filter = apply_primitive(
            p,
            Builtin::FilterValues,
            Type::fun(pair_ty.clone(), pair_ty.clone()),
        );
        chain = compose(filter, chain).with_ty(Type::Fun {
            name: name.clone(),
            fun_kind: crate::ccl::FunKind::Compute,
            domain: Box::new(pair_ty.clone()),
            codomain: Box::new(codomain.clone()),
        });
    }
    *g = chain;
    Ok(true)
}

/// Emit the filter a dependent pair's second component carries, where that filter is what
/// makes it dependent: `(𝑎 : 𝐴) × {𝐾 | 𝑝(𝑎, ·)}`, a correlated filter that `lambda_elim` keeps
/// on the component. Each row ranges over `𝐾`'s keys, so the site runs over the product
/// `(𝐴, 𝐾)`, and `filter_values` keeps the pairs `𝑝` holds for, `λ 𝑞 → 𝑝(𝑞.0, 𝑞.1)`. The
/// pairs it keeps are the dependent tuple's elements, so it is typed from the product to the
/// dependent tuple, and `𝑔` keeps the domain it was written at.
fn emit_component_filter(g: &mut Expr, witnesses: &mut Witnesses) -> Result<bool, String> {
    let Some(Type::DepTuple(components)) = g.ty.domain().map(|d| d.peel_refinements().clone())
    else {
        return Ok(false);
    };
    let [(first_name, first), (_, second)] = components.as_slice() else {
        return Ok(false);
    };
    let a = first_name.clone().unwrap_or_else(|| Name::fresh("__x"));
    let second =
        crate::ccl::subst::open_pi_binder(&crate::ccl::subst::Mapping::Rename(a.clone()), second);
    let filters: Vec<Rc<TypedExpr>> = second
        .refinements()
        .iter()
        .filter(|r| !r.is_collection_membership())
        .map(|r| Rc::clone(&r.predicate))
        .collect();
    if filters.is_empty()
        || second
            .refinements()
            .iter()
            .any(|r| r.is_collection_membership() && ccl_utils::is_free(&a, &r.predicate))
    {
        return Ok(false);
    }
    // The filters move onto the chain as `filter_values`; a membership refinement says which
    // keys exist, which the collection the row is read from demands on its domain, so it stays.
    let keys = Type::refined(
        second.peel_refinements().clone(),
        second
            .refinements()
            .iter()
            .filter(|r| r.is_collection_membership())
            .cloned()
            .collect(),
    );
    debug_assert!(
        !crate::ccl::subst::type_free_vars(&keys).contains(&a),
        "a filtered component's keys are the same for every row: {keys}"
    );
    let dependent = g.ty.domain().expect("matched a function's domain");
    let product = Type::Tuple(vec![first.clone(), keys.clone()]);
    let at = |index: usize, ty: &Type| {
        Expr::apply(
            Expr::var(Name::elem()).with_ty(product.clone()),
            Expr::proj_index(index).with_ty(Type::fun(product.clone(), ty.clone())),
        )
        .with_ty(ty.clone())
    };
    let mut chain = std::mem::replace(g, Expr::builtin(Builtin::Id));
    // The chain keeps `𝑔`'s binder: a row whose keys depend on the pair reads it in the
    // codomain, which is stored closed against it.
    let Type::Fun {
        name: binder,
        codomain,
        ..
    } = chain.ty.peel_refinements().clone()
    else {
        unreachable!("matched a function")
    };
    let mut kept = Type::fun(product.clone(), dependent.clone());
    for predicate in filters {
        // The element read first, then `𝑎`. A nested refinement reading `𝑎` binds `__elem`
        // to its own element, so there `𝑎` is bound by a lambda applied to `.0` rather than
        // written as `__elem.0` (`src/ccl/design/type-inference.md`, "Lifting a filter onto
        // the pair").
        let on_element =
            crate::ccl::subst::Subst::discharge(Name::elem(), at(1, &keys)).apply_expr(&predicate);
        let over_pair = if ccl_utils::count_free(&a, &on_element)
            > ccl_utils::count_free_in_value(&a, &on_element)
        {
            let ty = on_element.ty.clone();
            Expr::apply(
                at(0, first),
                Expr::lambda(a.clone(), first.clone(), on_element),
            )
            .with_ty(ty)
        } else {
            crate::ccl::subst::Subst::discharge(a.clone(), at(0, first)).apply_expr(&on_element)
        };
        let p = plan_before_iteration(fn_of_bare_predicate(&product, &over_pair, &[]), witnesses)?;
        let filter = apply_primitive(p, Builtin::FilterValues, kept.clone());
        chain = compose(filter, chain).with_ty(Type::Fun {
            name: binder.clone(),
            fun_kind: crate::ccl::FunKind::Compute,
            domain: Box::new(product.clone()),
            codomain: codomain.clone(),
        });
        kept = Type::fun(product.clone(), product.clone());
    }
    *g = chain;
    Ok(true)
}

/// Rewrite the refined pair domain to its bare product in every type slot at or below `e`:
/// the domain is the type every morphism in the chain is written at, so one slot is never
/// the only one. A refinement predicate's own slots count: a row whose keys depend on the
/// pair reads it in its domain's predicate, through projections written at the pair.
fn retype_subtree(e: &mut Expr, old: &Type, bare: &Type) {
    retype_subtree_in(e, old, bare, &PredMemo::default());
}

fn retype_subtree_in(e: &mut Expr, old: &Type, bare: &Type, memo: &PredMemo<()>) {
    e.walk_type_slots_mut(|ty| replace_domain(ty, old, bare, memo));
    e.walk_children_mut(|child| retype_subtree_in(child, old, bare, memo));
}

/// Replace the refined pair with its bare product wherever it occurs inside `ty`, not only
/// where `ty` is it: a morphism in the chain is written at `pair ⇒ 𝑉`, so the occurrence
/// is the domain of a function type rather than the slot itself.
fn replace_domain(ty: &mut Type, old: &Type, bare: &Type, memo: &PredMemo<()>) {
    if ty == old {
        *ty = bare.clone();
        return;
    }
    if let Type::Refinement(_, refinements) = ty {
        refinements.rewrite_each(|_, refinement| {
            memo.rebuild(refinement, &(), |pred| {
                if !mentions_type(pred, old) {
                    return false;
                }
                retype_subtree_in(pred, old, bare, memo);
                true
            });
        });
    }
    ty.walk_children_mut(|child| replace_domain(child, old, bare, memo));
}

/// Whether `old` occurs in a type slot at or below `e`, its predicates' slots included.
fn mentions_type(e: &Expr, old: &Type) -> bool {
    fn in_type(ty: &Type, old: &Type) -> bool {
        ty == old
            || ty
                .refinements()
                .iter()
                .any(|r| mentions_type(&r.predicate, old))
            || {
                let mut found = false;
                ty.walk_children(|c| found |= in_type(c, old));
                found
            }
    }
    let mut found = false;
    e.walk_type_slots(|ty| found |= in_type(ty, old));
    e.walk_children(|c| found |= mentions_type(c, old));
    found
}

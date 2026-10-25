//! Generalized types: a polymorphic type a pass gives a use it moves out of the scope of a binder
//! the use's instance named (`src/ccl/design/type-parameters.md`, "Generalized types").
//!
//! Lambda elimination lifts: one point-free morphism serves every value of a parameter it
//! eliminated, so a type written under that parameter, `sum : ({0..4 | key(__elem) == k} ⤇
//! Int) ⇒ Int`, names a binder that no longer encloses it. Where the name sits in what the
//! morphism receives, the type is generalized over that part, `∀ (D <: 0..4). (D ⤇ Int) ⇒
//! Int`, and each use instantiates it from the type it is handed ([`instantiate`]).

use std::collections::HashMap;
use std::rc::Rc;

use crate::ccl::Type;
use crate::ccl::ty::TypeParamId;

/// `ty` instantiated for an input of type `incoming`: a generalized `Poly`'s parameters replaced by
/// what matching its body's domain against `incoming` binds them to. `ty` itself where it is not
/// a generalized `Poly`.
///
/// A parameter `incoming` does not fix stays quantified: an input that is itself generic, a
/// tuple of generalized types handed to `zip` say, leaves the result generic in the same part.
pub(crate) fn instantiate(ty: &Type, incoming: &Type) -> Type {
    let Type::Poly(poly) = ty else {
        return ty.clone();
    };
    if !poly.params.iter().all(|p| p.param.generalized) {
        return ty.clone();
    }
    let domain = poly
        .body
        .domain()
        .unwrap_or_else(|| panic!("a generalized type is a function, got {ty}"));
    let params: Vec<TypeParamId> = poly.params.iter().map(|p| p.param.id).collect();
    // Matched with every binder of `incoming` read by name: a type a parameter is bound to can
    // read them, and an index would read a different binder at the depth it lands at.
    let mut bound = HashMap::new();
    match_params(&domain, &opened_deep(incoming), &params, &mut bound);
    closed_deep(&instantiate_with(poly, &bound))
}

/// `body` quantified over those of `params` it reads; `body` itself where it reads none.
pub(crate) fn requantify(params: &[crate::ccl::ty::PolyParam], body: Type) -> Type {
    let reads = free_params(&body);
    let kept: Vec<_> = params
        .iter()
        .filter(|p| reads.iter().any(|q| q.id == p.param.id))
        .cloned()
        .collect();
    if kept.is_empty() {
        return body;
    }
    Type::Poly(Rc::new(crate::ccl::ty::PolyType {
        params: kept,
        requires: Vec::new(),
        body,
    }))
}

/// `poly` with the parameters `bound` maps replaced, quantified over the rest it still reads.
fn instantiate_with(poly: &crate::ccl::ty::PolyType, bound: &HashMap<TypeParamId, Type>) -> Type {
    let body = substitute(&poly.body, bound);
    let reads = free_params(&body);
    let unbound: Vec<_> = poly
        .params
        .iter()
        .filter(|p| !bound.contains_key(&p.param.id) && reads.iter().any(|q| q.id == p.param.id))
        .cloned()
        .collect();
    if unbound.is_empty() {
        return body;
    }
    Type::Poly(Rc::new(crate::ccl::ty::PolyType {
        params: unbound,
        requires: Vec::new(),
        body,
    }))
}

/// The two sides of a subtyping edge with their generalized types opened for the comparison: a
/// generic supertype by its body, its parameters standing for any type, and a generic subtype
/// instantiated at what the supertype receives in its place. Two generic types meet as one
/// generic type, whatever their parameters are named.
pub(crate) fn align(sub: &Type, sup: &Type) -> (Type, Type) {
    if !holds_generalized_type(sub) && !holds_generalized_type(sup) {
        return (sub.clone(), sup.clone());
    }
    let sup = match sup {
        Type::Poly(p) if p.params.iter().all(|q| q.param.generalized) => p.body.clone(),
        _ => sup.clone(),
    };
    (align_sub(sub, &sup), sup)
}

/// `codomain`, the codomain of the function `fun`, with `fun`'s references to its binder read
/// as the name `b`.
fn codomain_opened_as(fun: &Type, codomain: &Type, b: &crate::ccl::Name) -> Type {
    let Type::Fun {
        fun_kind, domain, ..
    } = fun.peel_refinements()
    else {
        unreachable!("only a function has a codomain")
    };
    let renamed = Type::Fun {
        name: Some(b.clone()),
        fun_kind: fun_kind.clone(),
        domain: domain.clone(),
        codomain: Box::new(codomain.clone()),
    };
    crate::ccl::subst::open_codomain(&renamed, codomain)
}

/// The names the functions in `ty` bind.
fn pi_binders(ty: &Type, out: &mut Vec<crate::ccl::Name>) {
    if let Type::Fun { name: Some(b), .. } = ty
        && !out.contains(b)
    {
        out.push(b.clone());
    }
    ty.walk_children(|c| pi_binders(c, out));
}

/// `ty` with every named function's references to its own binder read by name.
fn opened_deep(ty: &Type) -> Type {
    match ty {
        Type::Fun {
            name: Some(b),
            fun_kind,
            domain,
            codomain,
        } => Type::Fun {
            name: Some(b.clone()),
            fun_kind: fun_kind.clone(),
            domain: Box::new(opened_deep(domain)),
            codomain: Box::new(opened_deep(&crate::ccl::subst::open_codomain(ty, codomain))),
        },
        _ => {
            let mut out = ty.clone();
            out.walk_children_mut(|c| *c = opened_deep(c));
            out
        }
    }
}

/// [`opened_deep`] undone: every named function closed over its binder (`Type::pi_kinded`).
fn closed_deep(ty: &Type) -> Type {
    match ty {
        Type::Fun {
            name: Some(b),
            fun_kind,
            domain,
            codomain,
        } => Type::pi_kinded(
            b.clone(),
            closed_deep(domain),
            closed_deep(codomain),
            fun_kind.clone(),
        ),
        _ => {
            let mut out = ty.clone();
            out.walk_children_mut(|c| *c = closed_deep(c));
            out
        }
    }
}

/// `ty` with each function the supertype `like` names at the same position named alike, where
/// `ty` names none.
fn adopt_binder_names(ty: Type, like: &Type) -> Type {
    match (ty, like.peel_refinements()) {
        (
            Type::Fun {
                name,
                fun_kind,
                domain,
                codomain,
            },
            Type::Fun {
                name: like_name,
                domain: like_domain,
                codomain: like_codomain,
                ..
            },
        ) => Type::Fun {
            name: name.or_else(|| like_name.clone()),
            fun_kind,
            domain: Box::new(adopt_binder_names(*domain, like_domain)),
            codomain: Box::new(adopt_binder_names(*codomain, like_codomain)),
        },
        (Type::Tuple(ts), Type::Tuple(likes)) if ts.len() == likes.len() => Type::Tuple(
            ts.into_iter()
                .zip(likes)
                .map(|(t, l)| adopt_binder_names(t, l))
                .collect(),
        ),
        (other, _) => other,
    }
}

fn align_sub(sub: &Type, sup: &Type) -> Type {
    if let Type::Poly(p) = sub
        && p.params.iter().all(|q| q.param.generalized)
    {
        let opened = match sup.peel_refinements().domain() {
            Some(input) => instantiate(sub, &input),
            // A generic value meets the type it is expected at whole.
            None => {
                let mut bound = HashMap::new();
                match_params(
                    &p.body,
                    sup,
                    &p.params.iter().map(|q| q.param.id).collect::<Vec<_>>(),
                    &mut bound,
                );
                instantiate_with(p, &bound)
            }
        };
        // A parameter the supertype's input names abstractly binds the subtype's to it: the
        // two generic types are compared with one parameter for both.
        return match &opened {
            Type::Poly(still) => {
                // Matched with every binder read by name: a type a parameter is bound to can
                // read the supertype's binders, and an index would read a different one at
                // the depth it lands at. The instance binds them under the same names, the two
                // being one function up to those names, and is closed over them again.
                let named = opened_deep(sup);
                let mut bound = HashMap::new();
                match_params(
                    &still.body,
                    &named,
                    &still.params.iter().map(|q| q.param.id).collect::<Vec<_>>(),
                    &mut bound,
                );
                closed_deep(&adopt_binder_names(substitute(&still.body, &bound), &named))
            }
            done => done.clone(),
        };
    }
    match (sub, sup.peel_refinements()) {
        (
            Type::Fun {
                name,
                fun_kind,
                domain,
                codomain,
            },
            sup_fun @ Type::Fun {
                name: sup_name,
                domain: sd,
                codomain: sc,
                ..
            },
        ) => {
            let domain = Box::new(align_sub(domain, sd));
            // The codomains are aligned with the binder read by name in both: an index would
            // be loose in either alone, and a type a parameter is bound to would carry it to a
            // depth where it reads a different function.
            match name.clone().or_else(|| sup_name.clone()) {
                Some(b) => {
                    let aligned = align_sub(
                        &codomain_opened_as(sub, codomain, &b),
                        &codomain_opened_as(sup_fun, sc, &b),
                    );
                    if name.is_none() && !crate::ccl::subst::type_free_vars(&aligned).contains(&b) {
                        Type::Fun {
                            name: None,
                            fun_kind: fun_kind.clone(),
                            domain,
                            codomain: Box::new(aligned),
                        }
                    } else {
                        Type::pi_kinded(b, *domain, aligned, fun_kind.clone())
                    }
                }
                None => Type::Fun {
                    name: None,
                    fun_kind: fun_kind.clone(),
                    domain,
                    codomain: Box::new(align_sub(codomain, sc)),
                },
            }
        }
        (Type::Tuple(subs), Type::Tuple(sups)) if subs.len() == sups.len() => Type::Tuple(
            subs.iter()
                .zip(sups)
                .map(|(a, b)| align_sub(a, b))
                .collect(),
        ),
        (Type::Record(subs), Type::Record(sups)) => Type::Record(
            subs.iter()
                .map(|(label, a)| match sups.iter().find(|(l, _)| l == label) {
                    Some((_, b)) => (label.clone(), align_sub(a, b)),
                    None => (label.clone(), a.clone()),
                })
                .collect(),
        ),
        (Type::Variant(subs, openness), Type::Variant(sups, _)) => Type::Variant(
            subs.iter()
                .map(|(key, a)| match sups.iter().find(|(k, _)| k == key) {
                    Some((_, b)) => (key.clone(), align_sub(a, b)),
                    None => (key.clone(), a.clone()),
                })
                .collect(),
            *openness,
        ),
        _ => sub.clone(),
    }
}

/// `ty`'s structure for a pass that reads a type's parts: a generalized type's body, its
/// parameters standing for any type, refinements peeled. A pass that builds types from those
/// parts leaves the parameters outside their `Poly` until [`close_free_params`] closes them.
pub(crate) fn opened(ty: &Type) -> &Type {
    match ty {
        Type::Poly(p) if !p.params.is_empty() && p.params.iter().all(|q| q.param.generalized) => {
            opened(&p.body)
        }
        other => other.peel_refinements(),
    }
}

/// Whether `ty` holds a generalized `Poly` anywhere in its structure.
pub(crate) fn holds_generalized_type(ty: &Type) -> bool {
    if let Type::Poly(poly) = ty
        && poly.params.iter().all(|p| p.param.generalized)
    {
        return true;
    }
    let mut found = false;
    ty.walk_children(|c| found |= holds_generalized_type(c));
    found
}

/// Bind each parameter of `params` that `pattern` holds where `actual` has a type, outermost
/// first.
fn match_params(
    pattern: &Type,
    actual: &Type,
    params: &[TypeParamId],
    out: &mut HashMap<TypeParamId, Type>,
) {
    if let Type::Param(p) = pattern
        && params.contains(&p.id)
    {
        out.entry(p.id).or_insert_with(|| actual.clone());
        return;
    }
    // A refined parameter, `{D | 𝑝}`, is what `actual` is without the refinements the pattern
    // states.
    if let Type::Refinement(base, stated) = pattern
        && let Type::Param(p) = base.as_ref()
        && params.contains(&p.id)
    {
        let rest = match actual {
            Type::Refinement(abase, refinements) => Type::refined(
                (**abase).clone(),
                refinements
                    .iter()
                    .filter(|r| !stated.iter().any(|s| s == *r))
                    .cloned()
                    .collect(),
            ),
            other => other.clone(),
        };
        out.entry(p.id).or_insert(rest);
        return;
    }
    match (pattern.peel_refinements(), actual.peel_refinements()) {
        (
            Type::Fun {
                domain: pd,
                codomain: pc,
                ..
            },
            Type::Fun {
                domain: ad,
                codomain: ac,
                ..
            },
        ) => {
            match_params(pd, ad, params, out);
            match_params(pc, ac, params, out);
        }
        (Type::Tuple(ps), Type::Tuple(acts)) if ps.len() == acts.len() => {
            for (p, a) in ps.iter().zip(acts) {
                match_params(p, a, params, out);
            }
        }
        (Type::DepTuple(ps), Type::DepTuple(acts)) if ps.len() == acts.len() => {
            for ((_, p), (_, a)) in ps.iter().zip(acts) {
                match_params(p, a, params, out);
            }
        }
        (Type::Record(ps), Type::Record(acts)) => {
            for (label, p) in ps {
                if let Some((_, a)) = acts.iter().find(|(l, _)| l == label) {
                    match_params(p, a, params, out);
                }
            }
        }
        (Type::Variant(ps, _), Type::Variant(acts, _)) => {
            for (key, p) in ps {
                if let Some((_, a)) = acts.iter().find(|(k, _)| k == key) {
                    match_params(p, a, params, out);
                }
            }
        }
        _ => {}
    }
}

/// `ty` with each parameter `bound` maps replaced, in the terms it quotes as well. A refined
/// parameter's refinements join what replaces it ([`Type::refined`]).
pub(crate) fn substitute(ty: &Type, bound: &HashMap<TypeParamId, Type>) -> Type {
    let mut out = substitute_go(ty, bound);
    // The terms a type quotes carry type slots of their own, written over the same
    // parameters. The rewrite is the same type's, so it keeps the identities it copies.
    crate::ccl::provenance::preserving_ids(|| {
        crate::ccl::ccl_utils::walk_quoted_terms_mut(
            &mut out,
            &crate::ccl::ccl_utils::PredMemo::default(),
            &(),
            &mut |term, _| {
                fn in_term(e: &mut crate::ccl::Expr, bound: &HashMap<TypeParamId, Type>) {
                    e.walk_type_slots_mut(|t| *t = substitute(t, bound));
                    e.walk_children_mut(|c| in_term(c, bound));
                }
                in_term(term, bound);
                true
            },
        )
    });
    out
}

fn substitute_go(ty: &Type, bound: &HashMap<TypeParamId, Type>) -> Type {
    match ty {
        Type::Param(p) => bound.get(&p.id).cloned().unwrap_or_else(|| ty.clone()),
        Type::Refinement(base, refinements) => {
            Type::refined(substitute_go(base, bound), refinements.clone())
        }
        Type::Poly(poly) => {
            let mut inner = (**poly).clone();
            inner.body = substitute_go(&poly.body, bound);
            Type::Poly(Rc::new(inner))
        }
        _ => {
            let mut out = ty.clone();
            out.walk_children_mut(|c| *c = substitute_go(c, bound));
            renormalized(out)
        }
    }
}

/// Generalize every type in `root` that names a binder no term binder around it binds: lambda
/// elimination and the passes after it move uses out of the binders their instances were stated
/// under.
///
/// A function's input that names such a binder is abstracted over the refined types that name
/// it, each a parameter bounded by the type without those refinements
/// ([`generalized`]). A program's free names (its sources and sinks) are in scope everywhere,
/// and so is an opaque `let`'s name, which stays in the types lifted past it
/// (`Typing::close_let_type`).
// The cache keys on `Type`, whose refinement predicates carry interior mutability that
// equality and hashing do not read (matching the solver's allow).
#[allow(clippy::mutable_key_type)]
pub(crate) fn generalize_out_of_scope(root: &mut crate::ccl::Expr) {
    let everywhere = crate::ccl::ccl_utils::free_names_in_value(root);
    let mut cache = HashMap::new();
    let memo = crate::ccl::ccl_utils::PredMemo::new();
    walk(root, &mut Vec::new(), &everywhere, &mut cache, &memo);
}

/// The names `ty` binds over parts of itself: Pi binders and dependent-tuple components.
fn type_binders(ty: &Type, out: &mut Vec<crate::ccl::Name>) {
    match ty {
        Type::Fun { name: Some(n), .. } => out.push(n.clone()),
        Type::DepTuple(cs) => out.extend(cs.iter().filter_map(|(n, _)| n.clone())),
        _ => {}
    }
    ty.walk_children(|c| type_binders(c, out));
}

#[allow(clippy::mutable_key_type)]
fn walk(
    e: &mut crate::ccl::Expr,
    scope: &mut Vec<crate::ccl::Name>,
    everywhere: &std::collections::BTreeSet<crate::ccl::Name>,
    cache: &mut HashMap<Type, Type>,
    memo: &crate::ccl::ccl_utils::PredMemo<Vec<crate::ccl::Name>>,
) -> bool {
    let mut changed = false;
    // The terms a type slot quotes hold types of their own, under the node's scope, the
    // refinement's `__elem`, and the binders of the type around them. Every binder of the
    // type is taken as in scope, which can leave a type ungeneralized but never generalizes
    // one over a name the type binds.
    e.walk_type_slots_mut(|ty| {
        if !crate::ccl::subst::type_free_vars(ty)
            .iter()
            .any(|n| n.elem_index().is_none() && !scope.contains(n) && !everywhere.contains(n))
        {
            return;
        }
        let mut inner = scope.clone();
        inner.push(crate::ccl::Name::elem());
        type_binders(ty, &mut inner);
        changed |=
            crate::ccl::ccl_utils::walk_quoted_terms_mut(ty, memo, &inner, &mut |term, memo| {
                walk(term, &mut inner.clone(), everywhere, cache, memo)
            });
    });
    let out_of_scope = |n: &crate::ccl::Name| !scope.contains(n) && !everywhere.contains(n);
    let is_morphism = |c: &Type| matches!(c.peel_refinements(), Type::Fun { fun_kind, .. } if !fun_kind.resolved().is_data());
    let morphisms = match opened(&e.ty) {
        Type::Fun { fun_kind, .. } => !fun_kind.resolved().is_data(),
        Type::Tuple(components) => components.iter().any(is_morphism),
        Type::Record(fields) => fields.iter().any(|(_, c)| is_morphism(c)),
        Type::Variant(..) => constructs_variant(e),
        _ => false,
    };
    if morphisms
        && crate::ccl::subst::type_free_vars(&e.ty)
            .iter()
            .any(out_of_scope)
    {
        // The terms the generalized type quotes are minted for the node it types.
        let _g = crate::ccl::provenance::enter(
            e.node_id(),
            "generalize.generalize",
            crate::ccl::provenance::Nature::Machinery,
        );
        changed = true;
        e.ty = if constructs_variant(e) {
            constructor_generalized(&e.ty, &out_of_scope)
                .unwrap_or_else(|Undetermined(m)| panic!("{m}"))
        } else {
            generalized(
                &e.ty,
                &out_of_scope,
                &crate::ccl::symbolic::symbolic(e),
                cache,
            )
        };
    }
    // `const` and `map` are parametric in what they are applied to: `const : ∀ 𝐴. 𝐴 ⇒ (𝑃 ⇒ 𝐴)`,
    // and `map` over a step generic in the position each value is read at. So the type of
    // either applied is its instance there, the argument's type, generic or not, to the
    // application's, under the application's own parameters where it is generic. Lambda
    // elimination writes the type from the instance under the parameter it eliminated, where
    // the argument's read of it and the application's are one dependence, which generalizing
    // the type on its own would separate.
    if let crate::ccl::TypedExprNode::Apply { function, argument } = &mut e.node
        && matches!(
            function.node,
            crate::ccl::TypedExprNode::Builtin(
                crate::ccl::Builtin::Const | crate::ccl::Builtin::Map
            )
        )
        && crate::ccl::subst::type_free_vars(&function.ty)
            .iter()
            .any(out_of_scope)
    {
        walk(argument, scope, everywhere, cache, memo);
        let Type::Fun { fun_kind, .. } = opened(&function.ty) else {
            panic!(
                "an applied builtin's type is a function, got {}",
                function.ty
            )
        };
        let instance = |codomain: Type| Type::Fun {
            name: None,
            fun_kind: fun_kind.clone(),
            domain: Box::new(argument.ty.clone()),
            codomain: Box::new(codomain),
        };
        function.ty = match &e.ty {
            Type::Poly(p) if p.params.iter().all(|q| q.param.generalized) => {
                let mut generic = (**p).clone();
                generic.body = instance(p.body.clone());
                Type::Poly(Rc::new(generic))
            }
            applied => instance(applied.clone()),
        };
        return true;
    }
    let depth = scope.len();
    crate::ccl::scope::for_each_scoped_item_mut(e, &mut |item| match item {
        crate::ccl::scope::ScopedItemMut::Scope(names) => {
            scope.truncate(depth);
            scope.extend(names.iter().cloned());
        }
        crate::ccl::scope::ScopedItemMut::Child(expr) => {
            changed |= walk(expr, scope, everywhere, cache, memo)
        }
        _ => {}
    });
    scope.truncate(depth);
    changed
}

/// Whether `e` is a builtin whose output its use states, or one applied: a variant
/// constructor, `variant_wrap(𝑡)`, whose arms besides `𝑡` it does not build, and `map_domain`,
/// which passes its input through and restates its domain.
fn constructs_variant(e: &crate::ccl::Expr) -> bool {
    use crate::ccl::{Builtin, TypedExprNode};
    let states_its_output = |b: &Builtin| matches!(b, Builtin::VariantWrap(_) | Builtin::MapDomain);
    match &e.node {
        TypedExprNode::Builtin(b) => states_its_output(b),
        TypedExprNode::Apply { function, .. } => {
            matches!(&function.node, TypedExprNode::Builtin(b) if states_its_output(b))
        }
        _ => false,
    }
}

/// The type of a builtin whose output its use states ([`constructs_variant`]), or the value
/// it builds, generalized over every part out of scope, its output's included: the builtin is
/// parametric in what its use states, a constructor's other arms or `map_domain`'s restated
/// domain. A use fixes the parameters its input does not from the type it is stated at
/// ([`align`]).
fn constructor_generalized(
    ty: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
) -> Result<Type, Undetermined> {
    // A type generic already is generalized at its body, its parameters kept.
    if let Type::Poly(p) = ty
        && p.params.iter().all(|q| q.param.generalized)
    {
        let inner = constructor_generalized(&p.body, out_of_scope)?;
        return Ok(match inner {
            Type::Poly(q) => {
                let mut merged = (*q).clone();
                merged.params.splice(0..0, p.params.iter().cloned());
                Type::Poly(Rc::new(merged))
            }
            body => requantify(&p.params, body),
        });
    }
    let mut groups: Vec<Type> = Vec::new();
    refined_parts_naming(ty, out_of_scope, &mut groups);
    quantified(
        ty,
        groups,
        out_of_scope,
        "a builtin whose output its use states",
    )
}

/// `ty` generalized over the parts of its input that name a binder `out_of_scope` reports, at the
/// first function on its spine whose input names one; the value facts its output still states
/// about such a binder dropped.
///
/// # Panics
///
/// Where the output reads such a binder in a collection's domain after generalizing: the
/// domain is data, so the dependence is one the morphism's input has to carry, and the pass
/// that built the type did not pass it in.
///
/// Memoized in `cache` by the type generalized: a builtin's type and the application of it
/// state one type twice, as the builtin's codomain and as the application's own, and the two
/// stay equal only if they generalize to one `Poly`.
#[allow(clippy::mutable_key_type)]
pub(crate) fn generalized(
    ty: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
    at: &str,
    cache: &mut HashMap<Type, Type>,
) -> Type {
    try_generalized(ty, out_of_scope, at, cache).unwrap_or_else(|Undetermined(m)| panic!("{m}"))
}

/// A type that reads a binder no term binder around it binds in a collection's domain its
/// input does not determine, which no generalizing of it removes ([`generalized`]).
pub(crate) struct Undetermined(String);

/// Whether `ty` generalizes over the binders `out_of_scope` reports ([`generalized`]) to a type
/// reading none of them: whether every part reading one is determined by what the morphism
/// receives.
pub(crate) fn generalizes(ty: &Type, out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool) -> bool {
    // The generalized type is discarded, so the terms it quotes are copied under their own ids.
    crate::ccl::provenance::preserving_ids(|| {
        try_generalized(ty, out_of_scope, "", &mut HashMap::new()).is_ok_and(|t| {
            !crate::ccl::subst::type_free_vars(&t)
                .iter()
                .any(out_of_scope)
        })
    })
}

/// [`generalized`], the type that does not generalize answered rather than panicking.
#[allow(clippy::mutable_key_type)]
fn try_generalized(
    ty: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
    at: &str,
    cache: &mut HashMap<Type, Type>,
) -> Result<Type, Undetermined> {
    if let Some(done) = cache.get(ty) {
        return Ok(done.clone());
    }
    // A type generic already is generalized at its body, its parameters kept.
    if let Type::Poly(p) = ty
        && !p.params.is_empty()
        && p.params.iter().all(|q| q.param.generalized)
    {
        let done = match try_generalized(&p.body, out_of_scope, at, cache)? {
            Type::Poly(q) => {
                let mut merged = (*q).clone();
                merged.params.splice(0..0, p.params.iter().cloned());
                Type::Poly(Rc::new(merged))
            }
            body => requantify(&p.params, body),
        };
        cache.insert(ty.clone(), done.clone());
        return Ok(done);
    }
    // Generalized with every Pi binder read by name: a part the type states under a binder
    // of its own and again opened is then one part, spelled one way. A name such a binder
    // binds is the type's own, not one out of scope. A binder spelled like a name the type
    // reads outside it is renamed apart first: a part read under the binder depends on the
    // value it binds, which a parameter quantified outside the binder cannot.
    let mut renames = Vec::new();
    let apart = renamed_apart(ty, &crate::ccl::subst::type_free_vars(ty), &mut renames);
    let mut own = Vec::new();
    pi_binders(&apart, &mut own);
    let out_of_scope_here = |n: &crate::ccl::Name| out_of_scope(n) && !own.contains(n);
    let generalized = closed_deep(&generalized_go(
        &opened_deep(&apart),
        &out_of_scope_here,
        at,
        cache,
    )?);
    let done = restored_names(&generalized, &renames);
    cache.insert(ty.clone(), done.clone());
    Ok(done)
}

/// `ty` with each Pi binder spelled like a name in `free` renamed to a fresh spelling, one per
/// original, so binders spelled alike stay alike; each renaming recorded in `renames` as
/// (fresh, original).
fn renamed_apart(
    ty: &Type,
    free: &std::collections::BTreeSet<crate::ccl::Name>,
    renames: &mut Vec<(crate::ccl::Name, crate::ccl::Name)>,
) -> Type {
    match ty {
        Type::Fun {
            name: Some(b),
            fun_kind,
            domain,
            codomain,
        } if free.contains(b) => {
            let fresh = match renames.iter().find(|(_, original)| original == b) {
                Some((fresh, _)) => fresh.clone(),
                None => {
                    let fresh = b.refreshed();
                    renames.push((fresh.clone(), b.clone()));
                    fresh
                }
            };
            let opened = codomain_opened_as(ty, codomain, &fresh);
            Type::pi_kinded(
                fresh,
                renamed_apart(domain, free, renames),
                renamed_apart(&opened, free, renames),
                fun_kind.clone(),
            )
        }
        _ => {
            let mut out = ty.clone();
            out.walk_children_mut(|c| *c = renamed_apart(c, free, renames));
            out
        }
    }
}

/// [`renamed_apart`] undone: each binder `renames` records gets its original spelling back,
/// unless its codomain still reads that spelling free.
fn restored_names(ty: &Type, renames: &[(crate::ccl::Name, crate::ccl::Name)]) -> Type {
    if renames.is_empty() {
        return ty.clone();
    }
    match ty {
        Type::Fun {
            name: Some(b),
            fun_kind,
            domain,
            codomain,
        } => {
            let name = match renames.iter().find(|(fresh, _)| fresh == b) {
                Some((_, original))
                    if !crate::ccl::subst::type_free_vars(codomain).contains(original) =>
                {
                    original.clone()
                }
                _ => b.clone(),
            };
            Type::Fun {
                name: Some(name),
                fun_kind: fun_kind.clone(),
                domain: Box::new(restored_names(domain, renames)),
                codomain: Box::new(restored_names(codomain, renames)),
            }
        }
        _ => {
            let mut out = ty.clone();
            out.walk_children_mut(|c| *c = restored_names(c, renames));
            out
        }
    }
}

#[allow(clippy::mutable_key_type)]
fn generalized_go(
    ty: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
    at: &str,
    cache: &mut HashMap<Type, Type>,
) -> Result<Type, Undetermined> {
    let names = |t: &Type| {
        crate::ccl::subst::type_free_vars(t)
            .into_iter()
            .any(|n| out_of_scope(&n))
    };
    let Type::Fun {
        name,
        fun_kind,
        domain,
        codomain,
    } = ty.peel_refinements()
    else {
        // A record of morphisms is a product of them by label, each generalized alike.
        let mut component = |c: &Type| match c.peel_refinements() {
            Type::Fun { fun_kind, .. } if !fun_kind.resolved().is_data() => {
                try_generalized(c, out_of_scope, at, cache)
            }
            _ => Ok(c.clone()),
        };
        // A record of morphisms is a product of them by label, each generalized alike.
        if let Type::Record(fields) = ty {
            return Ok(Type::Record(
                fields
                    .iter()
                    .map(|(label, c)| Ok((label.clone(), component(c)?)))
                    .collect::<Result<_, Undetermined>>()?,
            ));
        }
        // A product of morphisms, the argument `zip` pairs: each component is generalized.
        if let Type::Tuple(components) = ty {
            return Ok(Type::Tuple(
                components
                    .iter()
                    .map(component)
                    .collect::<Result<_, Undetermined>>()?,
            ));
        }
        return drop_facts_naming(ty, out_of_scope, at);
    };
    // A collection is not generic in its domain: the domain is its data, so a collection over
    // a domain that names the binder is a value that depends on it, which the term that builds
    // it has to state. Only a compute function is generalized.
    if fun_kind.resolved().is_data() {
        return Ok(ty.clone());
    }
    if !names(domain) {
        // A curried function receives what names the binder further in: generalize there.
        // The parameters are quantified outside the function where their bounds do not read
        // its binder, the one place Check's derivation of an application puts them.
        let inner = product_hoisted(try_generalized(codomain, out_of_scope, at, cache)?);
        let fun = |codomain: Type| Type::Fun {
            name: name.clone(),
            fun_kind: fun_kind.clone(),
            domain: domain.clone(),
            codomain: Box::new(codomain),
        };
        return Ok(match inner {
            Type::Poly(p)
                if p.params.iter().all(|q| q.param.generalized)
                    && name.as_ref().is_none_or(|b| {
                        p.params.iter().all(|q| {
                            q.param
                                .bound
                                .as_ref()
                                .is_none_or(|t| !crate::ccl::subst::type_free_vars(t).contains(b))
                        })
                    }) =>
            {
                let mut hoisted = (*p).clone();
                hoisted.body = fun(p.body.clone());
                Type::Poly(Rc::new(hoisted))
            }
            inner => fun(inner),
        });
    }
    let mut groups: Vec<Type> = Vec::new();
    refined_parts_naming(domain, out_of_scope, &mut groups);
    quantified(ty.peel_refinements(), groups, out_of_scope, at)
}

/// A product whose components are generalized types, quantified once outside it: the form Check
/// derives for a function's result, the instantiation leaving one quantifier over the whole.
/// `ty` itself where no component is generic.
fn product_hoisted(ty: Type) -> Type {
    let is_generalized =
        |t: &Type| matches!(t, Type::Poly(p) if p.params.iter().all(|q| q.param.generalized));
    let mut params = Vec::new();
    let mut body = |t: &Type| match t {
        Type::Poly(p) if is_generalized(t) => {
            params.extend(p.params.iter().cloned());
            p.body.clone()
        }
        other => other.clone(),
    };
    let rebuilt = match &ty {
        Type::Tuple(cs) if cs.iter().any(is_generalized) => {
            Type::Tuple(cs.iter().map(&mut body).collect())
        }
        Type::Record(fs) if fs.iter().any(|(_, c)| is_generalized(c)) => {
            Type::Record(fs.iter().map(|(l, c)| (l.clone(), body(c))).collect())
        }
        _ => return ty,
    };
    Type::Poly(Rc::new(crate::ccl::ty::PolyType {
        params,
        requires: Vec::new(),
        body: rebuilt,
    }))
}

/// `ty` quantified over `groups`, each a parameter ranging as [`part_range`] says, with the
/// value facts it still states about a binder out of scope dropped.
fn quantified(
    ty: &Type,
    groups: Vec<Type>,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
    at: &str,
) -> Result<Type, Undetermined> {
    let mut params = Vec::new();
    let mut body = ty.clone();
    let mut groups = groups;
    for i in 0..groups.len() {
        let group = groups[i].clone();
        // A refined part is bounded by its base with the refinements that read nothing out of
        // scope; a sum's witness read through a term out of scope ranges over the witness's
        // own kind.
        let (kind, bound) = part_range(&group, out_of_scope);
        let param = crate::ccl::ty::TypeParam::generalized(spelling(i), bound);
        let d = Type::Param(Rc::clone(&param));
        body = abstract_deep(&body, &group, &d, out_of_scope);
        // A later part can hold this one inside the terms it quotes; it is matched as the
        // abstraction leaves it.
        for later in groups.iter_mut().skip(i + 1) {
            *later = abstract_deep(later, &group, &d, out_of_scope);
        }
        params.push(crate::ccl::ty::PolyParam {
            param,
            kind,
            bound_at: None,
        });
    }
    let body = drop_facts_naming(&body, out_of_scope, at)?;
    if params.is_empty() {
        return Ok(body);
    }
    Ok(Type::Poly(Rc::new(crate::ccl::ty::PolyType {
        params,
        requires: Vec::new(),
        body,
    })))
}

/// What a part a type is generalized over ranges over, and the bound its parameter states: a
/// refined type's base without the refinements that read out of scope, or, where that base is
/// itself a sum's witness read through a term out of scope, the witness's kind. A bound that
/// would still name such a binder is none.
fn part_range(
    group: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
) -> (crate::ccl::ty::TypeKind, Option<Type>) {
    let base = match group {
        Type::Refinement(..) => split_refinements(group, out_of_scope).0,
        other => other.clone(),
    };
    if let Type::WitnessProjection(p) = base.peel_refinements() {
        let kind = p
            .witness()
            .map(|w| w.type_kind())
            .unwrap_or(crate::ccl::ty::TypeKind::Type);
        let bound = match &kind {
            crate::ccl::ty::TypeKind::SubtypesOf(b) => Some((**b).clone()),
            _ => None,
        };
        return (kind, bound);
    }
    if crate::ccl::subst::type_free_vars(&base)
        .iter()
        .any(out_of_scope)
    {
        return (crate::ccl::ty::TypeKind::Type, None);
    }
    (
        crate::ccl::ty::TypeKind::SubtypesOf(Box::new(base.clone())),
        Some(base),
    )
}

fn spelling(i: usize) -> String {
    match i {
        0 => "D".to_string(),
        _ => format!("D{i}"),
    }
}

/// The maximal refined types in `ty` whose own refinements read a binder `out_of_scope`
/// reports, each once.
fn refined_parts_naming(
    ty: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
    out: &mut Vec<Type>,
) {
    let names = match ty {
        Type::Refinement(_, refinements) => refinements.iter().any(|r| reads(r, out_of_scope)),
        Type::WitnessProjection(p) => {
            crate::ccl::subst::type_free_vars(ty)
                .iter()
                .any(out_of_scope)
                && {
                    let _ = p;
                    true
                }
        }
        _ => false,
    };
    if names {
        if !out.contains(ty) {
            out.push(ty.clone());
        }
        return;
    }
    ty.walk_children(|c| refined_parts_naming(c, out_of_scope, out));
}

fn reads(r: &crate::ccl::Refinement, out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool) -> bool {
    crate::ccl::subst::refinement_free_vars(r)
        .iter()
        .any(out_of_scope)
}

/// `ty`, a refined type, split into its base with the refinements that read no binder
/// `out_of_scope` reports, and the rest.
fn split_refinements(
    ty: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
) -> (Type, crate::ccl::RefinementSet) {
    let Type::Refinement(base, refinements) = ty else {
        unreachable!("a part found by refined_parts_naming is refined")
    };
    let (naming, kept): (Vec<_>, Vec<_>) = refinements
        .iter()
        .cloned()
        .partition(|r| reads(r, out_of_scope));
    let _ = naming;
    let base = Type::refined((**base).clone(), kept.into_iter().collect());
    (base, crate::ccl::RefinementSet::default())
}

/// `ty` with `group` replaced by `d`, and a refinement of `group`'s base that holds all of
/// `group`'s refinements by `d` refined by the rest, in the terms it quotes as well.
///
/// The generalized type is a new type beside the ones that keep the quoted terms as they were,
/// so the terms it rewrites are derived ones, minted under the caller's recording.
fn abstract_deep(
    ty: &Type,
    group: &Type,
    d: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
) -> Type {
    let mut out = abstract_go(ty, group, d);
    crate::ccl::ccl_utils::walk_quoted_terms_mut(
        &mut out,
        &crate::ccl::ccl_utils::PredMemo::default(),
        &(),
        &mut |term, _| {
            fn in_term(
                e: &mut crate::ccl::Expr,
                group: &Type,
                d: &Type,
                out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
            ) -> bool {
                let mut changed = false;
                e.walk_type_slots_mut(|t| {
                    let next = abstract_deep(t, group, d, out_of_scope);
                    changed |= next != *t;
                    *t = next;
                });
                e.walk_children_mut(|c| changed |= in_term(c, group, d, out_of_scope));
                changed
            }
            in_term(term, group, d, out_of_scope)
        },
    );
    out
}

fn abstract_go(ty: &Type, group: &Type, d: &Type) -> Type {
    if ty == group {
        return d.clone();
    }
    if let (Type::Refinement(base, refinements), Type::Refinement(gbase, grefinements)) =
        (ty, group)
        && base == gbase
        && grefinements
            .iter()
            .all(|g| refinements.iter().any(|r| r == g))
    {
        let rest: crate::ccl::RefinementSet = refinements
            .iter()
            .filter(|r| !grefinements.iter().any(|g| g == *r))
            .cloned()
            .collect();
        return Type::refined(d.clone(), rest);
    }
    let mut out = ty.clone();
    out.walk_children_mut(|c| *c = abstract_go(c, group, d));
    renormalized(out)
}

/// `ty`, a dependent tuple a rewrite may have left with no component reading an earlier one,
/// as the plain tuple it then is ([`Type::dep_tuple`]).
fn renormalized(ty: Type) -> Type {
    match ty {
        Type::DepTuple(components) => Type::dep_tuple(components),
        other => other,
    }
}

/// `ty` without the refinements that read a binder `out_of_scope` reports, where each is a fact
/// about a value.
///
/// [`Undetermined`] where such a refinement sits on a collection's domain, which is data
/// ([`generalized`]).
fn drop_facts_naming(
    ty: &Type,
    out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
    at: &str,
) -> Result<Type, Undetermined> {
    fn go(
        ty: &Type,
        on_domain: bool,
        out_of_scope: &dyn Fn(&crate::ccl::Name) -> bool,
        at: &str,
        whole: &Type,
    ) -> Result<Type, Undetermined> {
        Ok(match ty {
            Type::Refinement(base, refinements) => {
                let (naming, kept): (Vec<_>, Vec<_>) = refinements
                    .iter()
                    .cloned()
                    .partition(|r| reads(r, out_of_scope));
                if on_domain && !naming.is_empty() {
                    return Err(Undetermined(format!(
                        "`{at}`'s type `{whole}` reads a binder no term binder around it binds, \
                         in a collection's domain its input does not determine: the dependence \
                         is on a value, which the morphism's input has to carry"
                    )));
                }
                Type::refined(
                    go(base, false, out_of_scope, at, whole)?,
                    kept.into_iter().collect(),
                )
            }
            Type::Fun {
                name,
                fun_kind,
                domain,
                codomain,
            } => Type::Fun {
                name: name.clone(),
                fun_kind: fun_kind.clone(),
                domain: Box::new(go(
                    domain,
                    fun_kind.resolved().is_data(),
                    out_of_scope,
                    at,
                    whole,
                )?),
                codomain: Box::new(go(codomain, false, out_of_scope, at, whole)?),
            },
            _ => {
                let mut out = ty.clone();
                let mut failed = None;
                out.walk_children_mut(|c| match go(c, false, out_of_scope, at, whole) {
                    Ok(t) => *c = t,
                    Err(e) => failed = failed.take().or(Some(e)),
                });
                if let Some(e) = failed {
                    return Err(e);
                }
                renormalized(out)
            }
        })
    }
    go(ty, false, out_of_scope, at, ty)
}

/// Wrap every type in `root` that reads a generalized parameter no `Poly` in it binds back into one
/// over those parameters.
///
/// A pass that reads a generic type's structure sees its body, the parameters standing for
/// any type ([`Type::peel_refinements`]), and the types it builds from those parts read the
/// parameters outside their `Poly`. A generalized parameter comes only from a parametric builtin's
/// type, so a morphism built from such parts is generic in it the same way.
pub(crate) fn close_free_params(root: &mut crate::ccl::Expr) {
    // A parameter whose `Poly` a pass replaced is declared again from its own bound
    // (`close_go`), so a tree declaring none can still read one.
    let mut declared = HashMap::new();
    collect_params(root, &mut declared);
    close_go(root, &declared);
}

fn collect_params(e: &crate::ccl::Expr, out: &mut HashMap<TypeParamId, crate::ccl::ty::PolyParam>) {
    fn in_type(t: &Type, out: &mut HashMap<TypeParamId, crate::ccl::ty::PolyParam>) {
        if let Type::Poly(p) = t {
            for q in &p.params {
                if q.param.generalized {
                    out.entry(q.param.id).or_insert_with(|| q.clone());
                }
            }
        }
        t.walk_children(|c| in_type(c, out));
    }
    e.walk_type_slots(|t| in_type(t, out));
    e.walk_children(|c| collect_params(c, out));
}

fn close_go(e: &mut crate::ccl::Expr, declared: &HashMap<TypeParamId, crate::ccl::ty::PolyParam>) {
    let free = free_params(&e.ty);
    if !free.is_empty() {
        // A parameter whose `Poly` a pass replaced is declared again from its own bound.
        let params: Vec<_> = free
            .iter()
            .map(|p| {
                declared
                    .get(&p.id)
                    .cloned()
                    .unwrap_or_else(|| crate::ccl::ty::PolyParam {
                        param: Rc::clone(p),
                        kind: match &p.bound {
                            Some(b) => crate::ccl::ty::TypeKind::SubtypesOf(Box::new(b.clone())),
                            None => crate::ccl::ty::TypeKind::Type,
                        },
                        bound_at: None,
                    })
            })
            .collect();
        e.ty = match &e.ty {
            Type::Poly(p) if p.params.iter().all(|q| q.param.generalized) => {
                let mut inner = (**p).clone();
                inner.params.extend(params);
                Type::Poly(Rc::new(inner))
            }
            ty => Type::Poly(Rc::new(crate::ccl::ty::PolyType {
                params,
                requires: Vec::new(),
                body: ty.clone(),
            })),
        };
    }
    e.walk_children_mut(|c| close_go(c, declared));
}

/// The generalized parameters `ty` reads that no `Poly` in it binds, in first-occurrence order.
pub(crate) fn free_params(ty: &Type) -> Vec<Rc<crate::ccl::ty::TypeParam>> {
    fn go(ty: &Type, bound: &mut Vec<TypeParamId>, out: &mut Vec<Rc<crate::ccl::ty::TypeParam>>) {
        match ty {
            Type::Param(p)
                if p.generalized && !bound.contains(&p.id) && !out.iter().any(|q| q.id == p.id) =>
            {
                out.push(Rc::clone(p));
            }
            Type::Poly(p) => {
                let depth = bound.len();
                bound.extend(p.params.iter().map(|q| q.param.id));
                go(&p.body, bound, out);
                bound.truncate(depth);
            }
            _ => ty.walk_children(|c| go(c, bound, out)),
        }
    }
    let mut out = Vec::new();
    go(ty, &mut Vec::new(), &mut out);
    out
}

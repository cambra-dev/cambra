//! Grouped fold fusion: a fold over each group of a group-by reads the rows directly, with no
//! group materialized.
//!
//! ```text
//! 𝑘 ▷ converse ≫ 𝑐 ▷ map ≫ 𝑣₂ ▷ map ≫ … ≫ 𝑣ₙ ▷ map ≫ 𝑎
//!   ⟹  (𝐻 ≫ (𝐾, 𝑉) ▷ zip) ▷ group_fold(𝑎)
//! ```
//!
//! where the key chain `𝑘` is `𝐻 ≫ 𝐾` and `𝑉` reads a row's value from what `𝐻` yields at it.
//! The heads it takes and the shapes it declines are in `src/ccl/design/optimization.md`,
//! "Grouped folds".

use super::*;
use crate::ccl::{AggregateKind, simplify, ty::FunKind};

/// Fuse every group-by fold in `expr` into a [`Builtin::GroupFold`].
pub(super) fn fuse_grouped_folds(expr: &mut Expr) {
    expr.walk_children_mut(fuse_grouped_folds);
    while let TypedExprNode::Compose(elts) = &expr.node
        && let Some(site) = match_site(elts)
    {
        fuse_site(expr, site);
    }
}

/// Replace `site` in the composition `expr` with its `group_fold`.
fn fuse_site(expr: &mut Expr, site: Site) {
    let TypedExprNode::Compose(elts) = &expr.node else {
        unreachable!("a site is matched in a composition");
    };
    // The fold is typed as the part of the chain it replaces: the chain itself where it is
    // the whole chain, else the groups' keys to what the aggregate makes of each.
    let whole = site.converse == 0 && site.aggregate + 1 == elts.len();
    let ty = if whole {
        expr.ty.clone()
    } else {
        let groups = &elts[site.converse].ty;
        let folded = elts[site.aggregate]
            .ty
            .codomain()
            .expect("an aggregate is a function");
        // The type built here binds no key, so the aggregate's result may not read the one
        // the `converse`'s type binds.
        if let Type::Fun {
            name: Some(binder), ..
        } = groups
        {
            debug_assert!(
                !crate::ccl::subst::type_free_vars(&folded).contains(binder),
                "a fold's result {folded} reads the group key `{binder}`"
            );
        }
        Type::data_fun(
            groups.domain().expect("a converse yields a collection"),
            folded,
        )
    };
    let chain = expr.node_id();
    let TypedExprNode::Compose(elts) = &mut expr.node else {
        unreachable!("matched above");
    };
    let after = elts.split_off(site.aggregate + 1);
    let replaced = elts.split_off(site.converse);
    // The terms the fold keeps are moved, not cloned, so they keep the provenance the
    // group-by rewrite gave them; only the nodes built here are this phase's.
    let fused = {
        let _g = provenance::enter(
            chain,
            "planning.grouped_fold",
            provenance::Nature::Machinery,
        );
        fuse(site.kind, replaced, ty)
    };
    if whole {
        *expr = fused;
        return;
    }
    elts.push(fused);
    elts.extend(after);
}

/// A group-by fold in a composition: the positions of its `converse` and of its aggregate.
struct Site {
    converse: usize,
    aggregate: usize,
    kind: AggregateKind,
}

/// The first group-by fold `𝑘 ▷ converse ≫ 𝑐 ▷ map ≫ … ≫ 𝑎` in `elts` whose steps after `𝑐`
/// keep the group's keys, whose keys and values are held in columns ([`held_in_columns`]), and
/// whose key chain reads `𝑐` from a head that enumerates the rows ([`reads_from`]).
///
/// What precedes the `converse` looks each group up by key, as it looks the `converse`'s
/// groups up, and what follows `𝑎` applies to each group's result; both stay. A per-group step
/// around the aggregate, such as `min(𝑔) * 10`, is a `zip` around it rather than a step after
/// it, and is not matched.
fn match_site(elts: &[Expr]) -> Option<Site> {
    (0..elts.len()).find_map(|converse| {
        let keys = applied(&elts[converse], Builtin::Converse)?;
        let rest = &elts[converse + 1..];
        let maps = rest
            .iter()
            .take_while(|elt| applied(elt, Builtin::Map).is_some())
            .count();
        let aggregate = rest.get(maps)?;
        let kind = match &aggregate.node {
            TypedExprNode::Builtin(b) => b.as_aggregate()?,
            _ => return None,
        };
        let steps: Vec<&Expr> = rest[..maps]
            .iter()
            .map(|elt| applied(elt, Builtin::Map).expect("counted as a map"))
            .collect();
        let (&collection, pointwise) = steps.split_first()?;
        if !pointwise
            .iter()
            .all(|step| simplify::preserves_domain(step))
        {
            return None;
        }
        let value = aggregate.ty.domain()?.codomain()?;
        if !held_in_columns(&keys.ty.codomain()?) || !held_in_columns(&value) {
            return None;
        }
        reads_from(keys, collection)?;
        Some(Site {
            converse,
            aggregate: converse + 1 + maps,
            kind,
        })
    })
}

/// Whether a value of `ty` is held in columns, as `GroupedFold` holds its keys and values
/// (`Tiling::is_scalar`): a base value or a range position, a variant of such payloads, or a
/// tuple or record of such. Every other type is declined, whether or not it would fit.
fn held_in_columns(ty: &Type) -> bool {
    match ty.peel_refinements() {
        Type::Base(_) | Type::UIntRange(_) => true,
        Type::Tuple(items) => items.iter().all(held_in_columns),
        Type::DepTuple(items) => items.iter().all(|(_, item)| held_in_columns(item)),
        Type::Record(fields) => fields.iter().all(|(_, field)| held_in_columns(field)),
        Type::Variant(arms, _) => arms.iter().all(|(_, payload)| held_in_columns(payload)),
        _ => false,
    }
}

/// The argument of `elt` when `elt` is `argument ▷ builtin`.
fn applied(elt: &Expr, builtin: Builtin) -> Option<&Expr> {
    match &elt.node {
        TypedExprNode::Apply { argument, function } if is_builtin(function, builtin) => {
            Some(argument)
        }
        _ => None,
    }
}

/// How a row's value is read from what the key chain's head yields at it.
enum Head {
    /// The head yields the row's position, and the grouped collection is looked up there.
    Positions,
    /// The head is the grouped collection, and yields the row's element.
    Collection,
}

/// How the key chain `𝐻 ≫ 𝐾` reads the grouped collection `𝑐`, or `None` where it reads it
/// neither way.
///
/// Where `𝐻` yields positions, `𝐾` and `𝑐` start with the same lookup and `𝑐`'s later steps
/// keep every key: a row then has a key exactly where it has a value, so the fold over the rows
/// makes the groups the `converse` made, and no group is lost to a row `𝑐` lacks.
fn reads_from(keys: &Expr, collection: &Expr) -> Option<Head> {
    let (head, steps) = match &keys.node {
        TypedExprNode::Compose(elts) => elts.split_first()?,
        _ => (keys, &[][..]),
    };
    if head == collection {
        return Some(Head::Collection);
    }
    let (lookup, after) = match &collection.node {
        TypedExprNode::Compose(elts) => elts.split_first()?,
        _ => (collection, &[][..]),
    };
    (yields_positions(head)
        && steps.first() == Some(lookup)
        && after.iter().all(simplify::preserves_domain))
    .then_some(Head::Positions)
}

/// Whether `head` is an `iterate`, with or without `restrict`s applied to it: a collection
/// whose values are its own keys.
fn yields_positions(head: &Expr) -> bool {
    match &head.node {
        TypedExprNode::Apply { function, argument } => {
            is_builtin(function, Builtin::Iterate)
                || matches!(&function.node, TypedExprNode::Apply { function, .. }
                    if is_builtin(function, Builtin::Restrict))
                    && yields_positions(argument)
        }
        _ => false,
    }
}

/// The `(𝐻 ≫ (𝐾, 𝑉) ▷ zip) ▷ group_fold(kind)`, typed `ty`, that replaces the chain
/// [`match_site`] matched in `elts`.
fn fuse(kind: AggregateKind, elts: Vec<Expr>, ty: Type) -> Expr {
    let mut elts = elts.into_iter();
    let keys = into_argument(elts.next().expect("matched with a converse"));
    let mut steps: Vec<Expr> = elts.filter_map(into_argument_or_aggregate).collect();
    let collection = steps.remove(0);
    let reads = reads_from(&keys, &collection).expect("matched");
    let (head, key_steps) = if matches!(keys.node, TypedExprNode::Compose(_)) {
        let TypedExprNode::Compose(mut elts) = keys.node else {
            unreachable!("tested above")
        };
        let rest = elts.split_off(1);
        (elts.pop().expect("a chain has a head"), rest)
    } else {
        (keys, Vec::new())
    };
    let yields = head
        .ty
        .codomain()
        .expect("a key chain's head is a collection");
    let chain = |steps: Vec<Expr>| match steps.len() {
        0 => id().with_ty(Type::fun(yields.clone(), yields.clone())),
        1 => steps.into_iter().next().expect("one step"),
        _ => typed_compose(steps),
    };
    let key = chain(key_steps);
    let value = chain(match reads {
        Head::Positions => std::iter::once(collection).chain(steps).collect(),
        Head::Collection => steps,
    });
    let rows = typed_compose(vec![
        head,
        lambda_elim::zip_pair(key, value, &FunKind::Compute),
    ]);
    let fused = apply_primitive(rows, Builtin::GroupFold(kind), ty);
    if let Err(errors) = typecheck(&fused) {
        panic!(
            "the grouped fold of a well-typed chain is well-typed, got {errors:?} for {}",
            symbolic_typed(&fused)
        );
    }
    fused
}

/// The argument of a `map` step, or nothing for the chain's closing aggregate.
fn into_argument_or_aggregate(elt: Expr) -> Option<Expr> {
    match elt.node {
        TypedExprNode::Builtin(_) => None,
        _ => Some(into_argument(elt)),
    }
}

/// The argument of `argument ▷ builtin`, moved out.
fn into_argument(elt: Expr) -> Expr {
    match elt.node {
        TypedExprNode::Apply { argument, .. } => *argument,
        other => unreachable!("matched as an application, got {other:?}"),
    }
}

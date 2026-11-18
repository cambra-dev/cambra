//! A group-by and the aggregation that folds its groups, fused into one `group_fold`.
//!
//! The group-by rewrite ([`super::groupby`]) leaves `𝐾 ▷ converse ≫ 𝐶 ▷ map`, and a per-group
//! aggregate composes after it. Where every step between them acts on a group's elements one at
//! a time, the groups are never needed as collections:
//!
//! ```text
//! 𝐾 ▷ converse ≫ 𝐶 ▷ map ≫ 𝑠₁ ▷ map ≫ … ≫ agg
//!     ⟹  (head ≫ (𝐶 ≫ key, 𝐶 ≫ value, 𝐶 ≫ keep…) ▷ zip) ▷ group_fold(agg)
//! ```
//!
//! `𝐾` reads the collection `𝐶` the groups hold, as `𝐶 ≫ key` or after the `iterate` that
//! enumerates its rows, `iterate ≫ 𝐶 ≫ key`, and each column reads `𝐶` the same way. `value` is
//! each `𝑓` of a step `(𝑓 ▷ map) ▷ map`, or of a scalar step `𝑓 ▷ map`, in turn. Each step
//! `𝑞 ▷ filter_values ▷ map` adds a keep column, `𝑞` read at the values its step sees. The group
//! set is the keys `𝐾` reads, so a group whose elements a filter drops folds nothing rather than
//! disappearing (`src/interpreter/design-operators.md`, "GroupAggregate"). A `zip` of
//! aggregations in place of `agg` folds each with a value column and keep columns of its own.
//!
//! A group-by whose key reads an enclosing row reaches here as `correlated` planning leaves it,
//! and [`fused_correlated`] fuses it the same way, with rows per enclosing row.

use super::*;
use crate::ccl::AggregateKind;
use crate::ccl::ops::{BinOpKind, CompareKind, GroupRows, GroupedFold};

/// Fuse every group-by its aggregation folds.
pub(super) fn fuse_group_aggregates(expr: &mut Expr) {
    fuse_in(expr, &mut Vec::new());
}

/// [`fuse_group_aggregates`] under the let-bound group-bys in scope. A reader `𝑔 ≫ … ≫ agg` of
/// a let-bound group-by `𝑔` fuses with `𝑔`'s chain spliced in its place; names are unique
/// after `uniquify`, so the chain reads the same bindings at the reader.
fn fuse_in(expr: &mut Expr, group_bys: &mut Vec<(Name, Vec<Expr>)>) {
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut expr.node
    {
        fuse_in(bound_expr, group_bys);
        // The chain is copied for the readers it fuses into, which record their own rewrite.
        // Copying mints nodes, which provenance attributes to the group-by they copy.
        let _g = provenance::enter(
            bound_expr.node_id(),
            "planning.groupby",
            provenance::Nature::Expansion,
        );
        let bound = match &bound_expr.node {
            TypedExprNode::Compose(elems) if applied(&elems[0], Builtin::Converse).is_some() => {
                Some(elems.clone())
            }
            _ => None,
        };
        drop(_g);
        let scoped = bound.is_some();
        if let Some(elems) = bound {
            group_bys.push((binding.name.clone(), elems));
        }
        fuse_in(body, group_bys);
        if scoped {
            group_bys.pop();
        }
        return;
    }
    expr.walk_children_mut(|child| fuse_in(child, group_bys));
    {
        let _g = provenance::enter(
            expr.node_id(),
            "planning.groupby",
            provenance::Nature::Expansion,
        );
        if let Some(fused) = fused_correlated(expr) {
            *expr = fused;
            return;
        }
    }
    let TypedExprNode::Compose(elems) = &mut expr.node else {
        return;
    };
    let mut i = 0;
    while i < elems.len() {
        // Recorded as the group-by rewrite: the fused fold is what the user's `groupby` and the
        // aggregation over its groups denote, as the bucketize chain is.
        let _g = provenance::enter(
            elems[i].node_id(),
            "planning.groupby",
            provenance::Nature::Expansion,
        );
        if let Some((fused, consumed)) = fused_window(&elems[i..]) {
            elems.splice(i..i + consumed, [fused]);
        } else if let TypedExprNode::Var(name) = &elems[i].node
            && let Some((_, defined)) = group_bys.iter().rev().find(|(n, _)| n == name)
        {
            let spliced: Vec<Expr> = defined.iter().chain(&elems[i + 1..]).cloned().collect();
            if let Some((fused, consumed)) = fused_window(&spliced)
                && consumed > defined.len()
            {
                elems.splice(i..i + 1 + consumed - defined.len(), [fused]);
            }
        }
        i += 1;
    }
    if elems.len() == 1 {
        let ty = expr.ty.clone();
        let TypedExprNode::Compose(mut elems) =
            std::mem::replace(&mut expr.node, TypedExprNode::Tuple(vec![]))
        else {
            unreachable!("matched above")
        };
        *expr = elems.pop().expect("one element").with_ty(ty);
    }
}

fn applied(e: &Expr, builtin: Builtin) -> Option<&Expr> {
    match &e.node {
        TypedExprNode::Apply { argument, function } if is_builtin(function, builtin) => {
            Some(argument)
        }
        _ => None,
    }
}

/// One step between the group-by and its aggregation, on each element of a group.
enum Step<'a> {
    Id,
    Map(&'a Expr),
    Filter(&'a Expr),
}

fn step_of(elem: &Expr) -> Option<Step<'_>> {
    let per_group = applied(elem, Builtin::Map)?;
    if is_builtin(per_group, Builtin::Id) {
        return Some(Step::Id);
    }
    if let Some(f) = applied(per_group, Builtin::Map) {
        return Some(Step::Map(f));
    }
    if let Some(q) = applied(per_group, Builtin::FilterValues) {
        return Some(Step::Filter(q));
    }
    // A morphism on a scalar applied to a group acts on each element.
    let scalar = per_group
        .ty
        .domain()
        .is_some_and(|d| !matches!(d.peel_refinements().structure().as_ref(), Type::Fun { .. }));
    scalar.then_some(Step::Map(per_group))
}

/// The window starting at `chain[0]`, rewritten, and how many elements it spans.
fn fused_window(chain: &[Expr]) -> Option<(Expr, usize)> {
    let keys = applied(chain.first()?, Builtin::Converse)?;
    let TypedExprNode::Compose(key_chain) = &keys.node else {
        return None;
    };
    let values = applied(chain.get(1)?, Builtin::Map)?;
    // `𝐾` reads the collection the groups hold either as its head, `𝐶 ≫ key`, or after the
    // `iterate` that enumerates the rows, `iterate ≫ 𝐶 ≫ key`.
    let (head, prefix, key) = match key_chain.split_first()? {
        (head, key) if same_term(head, values) => (head, None, key),
        (head, [collection, key @ ..]) if enumerates(head) && same_term(collection, values) => {
            (head, Some(values), key)
        }
        _ => return None,
    };
    let mut steps = Vec::new();
    for (at, elem) in chain.iter().enumerate().skip(2) {
        if let Some(folds) = folds_of(elem) {
            let (rows, folds) = rows_of(head, prefix, key, values, &steps, &folds)?;
            return Some((group_fold(rows, folds, &chain[0], elem), at + 1));
        }
        steps.push(step_of(elem)?);
    }
    None
}

/// One aggregation of a fused fold, with the steps that act on the group's elements before it,
/// after the steps every aggregation shares.
struct Fold<'a> {
    kind: AggregateKind,
    steps: Vec<Step<'a>>,
}

/// The aggregations `elem` folds each group with, where `GroupAggregate` runs them: one
/// aggregation, or a `zip` of several over the same group, each `𝑠₁ ≫ … ≫ agg` with steps of its
/// own, each folding to a scalar. `Sole` selects rather than folds, and an extreme of a nominal
/// type orders by a key op-conversion derives from the type, which the fused fold does not read.
fn folds_of(elem: &Expr) -> Option<Vec<Fold<'_>>> {
    let arms: Vec<&Expr> = match applied(elem, Builtin::Zip) {
        // A zip of one aggregation answers a one-field record, which `GroupAggregate`, answering a
        // scalar for one fold, does not spell.
        Some(zipped) => match &zipped.node {
            TypedExprNode::Tuple(arms) if arms.len() >= 2 => arms.iter().collect(),
            _ => return None,
        },
        None => vec![elem],
    };
    arms.into_iter()
        .map(|arm| {
            let (agg, steps) = match &arm.node {
                TypedExprNode::Compose(elems) => elems.split_last()?,
                _ => (arm, &[][..]),
            };
            let TypedExprNode::Builtin(b) = &agg.node else {
                return None;
            };
            let kind = b.as_aggregate()?;
            let result = agg.ty.codomain()?;
            let by_key = matches!(kind, AggregateKind::Max | AggregateKind::Min)
                && result.mentions_nominal();
            if kind == AggregateKind::Sole || by_key || !is_scalar(&result) {
                return None;
            }
            let steps = steps.iter().map(step_of).collect::<Option<Vec<_>>>()?;
            Some(Fold { kind, steps })
        })
        .collect()
}

fn enumerates(head: &Expr) -> bool {
    is_builtin(head, Builtin::Iterate) || applied(head, Builtin::Iterate).is_some()
}

/// `head ≫ (key, value₁, keep₁…, value₂, keep₂…, …) ▷ zip`, one value column and its keep columns
/// per fold, each column an element morphism read through `prefix` (the collection, where `head`
/// enumerates its rows), and each fold's kind with its count of keep columns. `None` where a type
/// along the way is not a function.
fn rows_of(
    head: &Expr,
    prefix: Option<&Expr>,
    key: &[Expr],
    values: &Expr,
    shared: &[Step<'_>],
    folds: &[Fold<'_>],
) -> Option<(Expr, Vec<GroupedFold>)> {
    let index = head.ty.codomain()?;
    let element = values.ty.codomain()?;
    let id = Expr::builtin(Builtin::Id).with_ty(Type::fun(element.clone(), element));
    let chain = |elts: &[Expr]| {
        let mut all: Vec<Expr> = prefix.into_iter().cloned().collect();
        all.extend(elts.iter().cloned());
        if all.is_empty() {
            all.push(id.clone());
        }
        if all.len() == 1 {
            return all.pop();
        }
        let ty = Type::fun(index.clone(), all.last()?.ty.codomain()?);
        Some(Expr::compose(all).with_ty(ty))
    };
    let key = chain(key)?;
    if !is_scalar(&key.ty.codomain()?) {
        return None;
    }
    let mut columns = vec![key];
    let mut grouped = Vec::with_capacity(folds.len());
    for fold in folds {
        let mut value = Vec::new();
        let mut keeps = Vec::new();
        for step in shared.iter().chain(&fold.steps) {
            match step {
                Step::Id => {}
                Step::Map(f) => value.push((*f).clone()),
                Step::Filter(q) => {
                    let mut read = value.clone();
                    read.push((*q).clone());
                    keeps.push(chain(&read)?);
                }
            }
        }
        // Each filter is a keep column of its own: `GroupAggregate` folds a row into this fold
        // where all of its keep columns hold.
        grouped.push(GroupedFold {
            kind: fold.kind,
            keeps: keeps.len(),
        });
        columns.push(chain(&value)?);
        columns.extend(keeps);
    }
    let row_ty = Type::Tuple(
        columns
            .iter()
            .map(|c| c.ty.codomain())
            .collect::<Option<Vec<_>>>()?,
    );
    let zipped = zip_of(columns, &index, row_ty.clone());
    let rows =
        Expr::compose(vec![head.clone(), zipped]).with_ty(Type::fun(head.ty.domain()?, row_ty));
    Some((rows, grouped))
}

fn zip_of(arms: Vec<Expr>, index: &Type, row: Type) -> Expr {
    let arms_ty = Type::Tuple(arms.iter().map(|a| a.ty.clone()).collect());
    let fun = Type::fun(index.clone(), row);
    Expr::apply(
        Expr::tuple(arms).with_ty(arms_ty.clone()),
        Expr::builtin(Builtin::Zip).with_ty(Type::fun(arms_ty, fun.clone())),
    )
    .with_ty(fun)
}

/// `rows ▷ group_fold(folds)`, typed as the window it replaces.
fn group_fold(rows: Expr, folds: Vec<GroupedFold>, first: &Expr, last: &Expr) -> Expr {
    // The window is a morphism from the group keys, of the group-by's kind: a data function
    // `K ⤇ R`, its binder kept, ending where the aggregation does.
    let mut ty = first.ty.clone();
    if let Type::Fun { codomain, .. } = &mut ty {
        **codomain = last.ty.codomain().unwrap_or(Type::Hole);
    }
    let rows_ty = rows.ty.clone();
    Expr::apply(
        rows,
        Expr::builtin(Builtin::GroupFold(folds, GroupRows::Enumerated))
            .with_ty(Type::fun(rows_ty, ty.clone())),
    )
    .with_ty(ty)
}

/// A correlated group-by its aggregation folds, as `correlated` planning leaves it: the group
/// keys per outer row and, per `(row, key)`, the elements whose key it is, folded.
///
/// ```text
/// (𝑆 ≫ key ▷ map ≫ converse ≫ map_domain, (𝐷, 𝑒𝑞 ▷ filter_values ≫ .1 ≫ value) ▷ curry_over ≫ agg)
///     ▷ curry_over
///   ⟹  (𝑆 ≫ (key, .1 ≫ value) ▷ zip ▷ map) ▷ group_fold(agg)
/// ```
///
/// `𝑆 = 𝐷 ▷ const ▷ strength_over` pairs each outer row with each element, and `key` reads that
/// pair. `𝑒𝑞` is the partition's refinement, `key` of the element against the group's key, so
/// the inner site holds exactly the group's elements. `value` reads the element alone, after
/// `.1`. The per-group fold may start with `(id, .1) ▷ zip`, and `agg` may be a `zip` of
/// aggregations without steps of their own, each folding `value`. Any other shape is left as it
/// is.
fn fused_correlated(site: &Expr) -> Option<Expr> {
    let TypedExprNode::Apply { argument, function } = &site.node else {
        return None;
    };
    if !is_builtin(function, Builtin::CurryOver) {
        return None;
    }
    let TypedExprNode::Tuple(halves) = &argument.node else {
        return None;
    };
    let [keys, per_group] = halves.as_slice() else {
        return None;
    };
    let TypedExprNode::Compose(keys) = &keys.node else {
        return None;
    };
    // The phase runs before `Cleanup` flattens the family `correlated` built as a chain inside
    // the chain.
    let keys: Vec<&Expr> = keys
        .iter()
        .flat_map(|k| match &k.node {
            TypedExprNode::Compose(inner) => inner.iter().collect::<Vec<_>>(),
            _ => vec![k],
        })
        .collect();
    let [pairs, key_map, converse, map_domain] = keys.as_slice() else {
        return None;
    };
    if !is_builtin(converse, Builtin::Converse) || !is_builtin(map_domain, Builtin::MapDomain) {
        return None;
    }
    let key = applied(key_map, Builtin::Map)?;
    let TypedExprNode::Compose(per_group) = &per_group.node else {
        return None;
    };
    // The per-group fold reads `(row, key)`, or `((row, key), key)` behind a `(id, .1) ▷ zip`
    // that hands the inner site its group key beside the pair. The inner site's pair puts the
    // element beside what it reads, so the row sits one `.0` deeper behind that zip.
    let (row_reads, inner, agg) = match per_group.as_slice() {
        [inner, agg] => (2, inner, agg),
        [beside, inner, agg] if pairs_with_its_key(beside) => (3, inner, agg),
        _ => return None,
    };
    let folds = folds_of(agg)?;
    if folds.iter().any(|fold| !fold.steps.is_empty()) {
        return None;
    }
    if !key.ty.codomain().is_some_and(|t| is_scalar(&t)) {
        return None;
    }
    let inner_halves = applied(inner, Builtin::CurryOver)?;
    let TypedExprNode::Tuple(inner_halves) = &inner_halves.node else {
        return None;
    };
    let [domain, filtered] = inner_halves.as_slice() else {
        return None;
    };
    // The inner site ranges over the elements the pairs pair each row with: both lift the same
    // collection with `const`, to functions of different inputs.
    let paired = applied(applied(pairs, Builtin::StrengthOver)?, Builtin::Const)?;
    if !same_term(paired, applied(domain, Builtin::Const)?) {
        return None;
    }
    let TypedExprNode::Compose(filtered) = &filtered.node else {
        return None;
    };
    let (filter, value) = filtered.split_first()?;
    let eq = applied(filter, Builtin::FilterValues)?;
    if !is_partition_check(eq, key, row_reads) {
        return None;
    }
    let (element, value) = value.split_first()?;
    if !matches!(&element.node, TypedExprNode::Proj(ProjKey::Index(1))) {
        return None;
    }
    // `value` read the inner site's pair `((row, key), element)`; it reads `(row, element)` here,
    // through a `.1` typed against that pair. Its first step takes the element, so its domain
    // is the element's type.
    let pair = key.ty.domain()?;
    let element = value.first()?.ty.domain()?;
    let mut read = vec![
        Expr::new(TypedExprNode::Proj(ProjKey::Index(1))).with_ty(Type::fun(pair.clone(), element)),
    ];
    read.extend(value.iter().cloned());
    let value = match read.len() {
        1 => read.pop()?,
        _ => {
            let ty = Type::fun(pair.clone(), read.last()?.ty.codomain()?);
            Expr::compose(read).with_ty(ty)
        }
    };
    // Every fold folds the same value, with no keep column.
    let mut columns = vec![key.clone()];
    columns.extend(std::iter::repeat_n(value, folds.len()));
    let row_ty = Type::Tuple(
        columns
            .iter()
            .map(|c| c.ty.codomain())
            .collect::<Option<Vec<_>>>()?,
    );
    let zipped = zip_of(columns, &pair, row_ty.clone());
    let mut map_ty = key_map.ty.clone();
    set_innermost_codomain(&mut map_ty, row_ty)?;
    let mapped = Expr::apply(
        zipped.clone(),
        Expr::builtin(Builtin::Map).with_ty(Type::fun(zipped.ty.clone(), map_ty.clone())),
    )
    .with_ty(map_ty.clone());
    // The pairs bind the outer row for the chain, which the keys' types read: keep that binder.
    let mut rows_ty = pairs.ty.clone();
    let Type::Fun { codomain, .. } = &mut rows_ty else {
        return None;
    };
    **codomain = map_ty.codomain()?;
    let rows = Expr::compose(vec![(*pairs).clone(), mapped]).with_ty(rows_ty.clone());
    Some(
        Expr::apply(
            rows,
            Expr::builtin(Builtin::GroupFold(
                folds
                    .iter()
                    .map(|fold| GroupedFold {
                        kind: fold.kind,
                        keeps: 0,
                    })
                    .collect(),
                GroupRows::PerRow,
            ))
            .with_ty(Type::fun(rows_ty, site.ty.clone())),
        )
        .with_ty(site.ty.clone()),
    )
}

/// Whether `e` is `(id, .1) ▷ zip`: a pair `(row, key)` beside its own key.
fn pairs_with_its_key(e: &Expr) -> bool {
    let Some(arms) = applied(e, Builtin::Zip) else {
        return false;
    };
    let TypedExprNode::Tuple(arms) = &arms.node else {
        return false;
    };
    matches!(
        arms.as_slice(),
        [id, second] if is_builtin(id, Builtin::Id)
            && matches!(&second.node, TypedExprNode::Proj(ProjKey::Index(1)))
    )
}

/// `(key', .0 ≫ .1) ▷ zip ≫ eq`: the element's key against the group key the pair carries, where
/// `key'` is `key` reading the row through `row_reads` projections `.0` rather than one.
fn is_partition_check(eq: &Expr, key: &Expr, row_reads: usize) -> bool {
    let TypedExprNode::Compose(steps) = &eq.node else {
        return false;
    };
    let [zipped, compare] = steps.as_slice() else {
        return false;
    };
    let Some(arms) = applied(zipped, Builtin::Zip) else {
        return false;
    };
    let TypedExprNode::Tuple(arms) = &arms.node else {
        return false;
    };
    is_builtin(
        compare,
        Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)),
    ) && arms.len() == 2
        && symbolic(&arms[1]) == ".0 ≫ .1"
        && symbolic(&arms[0]) == read_through_row(&symbolic(key), row_reads)
}

/// A pair-reading term's printed form with each read of the pair's `.0`, a `.0` that heads a
/// chain, made through `row_reads` projections `.0`: how a term over `(row, element)` reads
/// `((row, key), element)` (two), or `(((row, key), key), element)` (three).
fn read_through_row(printed: &str, row_reads: usize) -> String {
    let through = vec![".0"; row_reads].join(" ≫ ");
    let mut out = String::with_capacity(printed.len());
    let mut rest = printed;
    while let Some(at) = rest.find(".0") {
        let (before, after) = rest.split_at(at);
        out.push_str(before);
        let continues = after[2..].starts_with(|c: char| c.is_ascii_digit());
        let heads_chain = !out.trim_end().ends_with('≫');
        out.push_str(if heads_chain && !continues {
            &through
        } else {
            ".0"
        });
        rest = &after[2..];
    }
    out.push_str(rest);
    out
}

/// Whether `a` and `b` are the same term: the same printed form at the same type. Planning has no
/// structural comparison that ignores node identity, so the printed form stands in for one.
fn same_term(a: &Expr, b: &Expr) -> bool {
    a.ty == b.ty && symbolic(a) == symbolic(b)
}

/// Whether `ty` is a value a column holds: `GroupAggregate` keys groups by one and folds to one.
fn is_scalar(ty: &Type) -> bool {
    !matches!(
        ty.peel_refinements().structure().as_ref(),
        Type::Tuple(_) | Type::Record(..) | Type::Fun { .. } | Type::DepTuple(_)
    )
}

/// Replace the innermost codomain of a function whose codomain is a collection: `𝐴 ⇒ (𝑈 ⤇ 𝑉)`
/// becomes `𝐴 ⇒ (𝑈 ⤇ row)`.
fn set_innermost_codomain(ty: &mut Type, row: Type) -> Option<()> {
    let Type::Fun { codomain, .. } = ty else {
        return None;
    };
    let Type::Fun { codomain, .. } = &mut **codomain else {
        return None;
    };
    **codomain = row;
    Some(())
}

//! Pointful group-by recognizer/rewrite (design §6.5).
//!
//! [`recognize_groupby_sites`] walks the tree before the iteration-site materialisation
//! walk and rewrites each group-by source (the dependent refinement
//! `const(cast(c)) : (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)`) to the bucketize-and-aggregate
//! chain `converse(c ≫ key) ≫ map(c)` built by [`emit_groupby`].
//!
//! Nothing marks a group-by as such; planning discovers it. The module is split along the
//! axis that decides what can grow:
//!
//! - [`partition_key_of`] — **is this refinement a partition by a key?** A question about a
//!   refinement alone, independent of how the surrounding term is spelled. New sources of
//!   refinements reuse it unchanged.
//! - [`match_pointful_site`] — **is this the term shape I can rebuild from?** Coupled to
//!   what `lambda_elim` emits; a new site pattern is a sibling of this, not an edit to it.
//!
//! Declining to rewrite is safe — the site falls back to the generic iterate/restrict
//! lowering — so the failure mode to guard against is *silence*. A refinement that
//! partitions at a site that did not match is logged as a near miss.

use super::*;
use crate::ccl::ty::FunKind;

/// Recognize group-by sites and rewrite them to the bucketize chain.
///
/// Group-by lowers to the dependent-refinement source `const(cast(c)) :
/// (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)`; [`convert_groupby_pointful`] matches
/// that **pointful** form (design §6.5) and rewrites it to
/// `converse(c ≫ key) ≫ map(c)`. Walks the tree, rewriting every such site
/// (a rewritten site's tail may contain further sites).
///
/// Not matching is **not** an error: the site falls back to the generic
/// iterate/restrict lowering, which is correct, just unbucketized. But a *near miss*
/// — a refinement that [partitions](partition_key_of), at a site this recognizer
/// could not rebuild from — is worth seeing, because it is the difference between
/// "there was nothing to recognize here" and "this should have been recognized and
/// the spelling drifted". [`log_near_miss`] reports those; as the recognizer grows to
/// cover refinements from beyond the group-by lowering, that log is the list of
/// patterns still to add.
pub(super) fn recognize_groupby_sites(expr: &mut Expr) {
    // The recording names the composition site — the term-tree node the
    // bucketize chain replaces — and deliberately not the key morphism the
    // rewrite lifts out of the refined domain's predicate. The composition is
    // what the user's `groupby(...)` became and what the chain now stands in
    // for; the lifted key keeps its own parentage, since a clone's copy carries
    // the predicate node it was freshened from rather than the node named here.
    //
    // `Nature::Expansion`: the bucketize chain is what `groupby` *denotes*, so
    // the rewrite expands a construct the user wrote. Contrast
    // `planning.hash_join`, which is `Machinery` because a hash join is a
    // materialization strategy for a site the user wrote as a comprehension.
    //
    // Scoped to the *attempt* and closed before the child walk. Recursing under
    // it would make a nested site's products descend from this one. A
    // non-matching node writes no rows here: the matcher bails on node shape
    // before it reaches anything that mints, and the type work it does reach
    // (`open_codomain`) opens its own `subst.*` recordings, so wrapping the
    // attempt costs a push and a pop.
    let rewritten = {
        let _g = provenance::enter(
            expr.node_id(),
            "planning.groupby",
            provenance::Nature::Expansion,
        );
        convert_groupby_pointful(expr)
    };
    if let Some(rewritten) = rewritten {
        *expr = rewritten;
    }
    log_near_miss(expr);
    expr.walk_children_mut(recognize_groupby_sites);
}

/// Report a partitioning refinement the recognizer declined to rewrite.
///
/// Scoped to the shape the rewrite *starts* from — a `Compose` head — so this stays
/// about sites, not about every partition refinement anywhere in the tree.
fn log_near_miss(expr: &Expr) {
    if !log::log_enabled!(log::Level::Debug) {
        return;
    }
    let TypedExprNode::Compose(elts) = &expr.node else {
        return;
    };
    let Some(head) = elts.first() else { return };
    let Type::Fun {
        codomain: inner, ..
    } = &head.ty
    else {
        return;
    };
    let Type::Fun { domain: dom, .. } = inner.as_ref() else {
        return;
    };
    let Type::Refinement(_, refinements) = dom.as_ref() else {
        return;
    };
    // Any member of the set may be the partition; the others are ordinary filters.
    for r in refinements.iter() {
        if partition_key_of(&r.predicate).is_some() {
            log::debug!(
                "group-by near miss: {} partitions, but the site did not match — planning \
                 falls back to iterate/restrict. Head: {}",
                symbolic(&r.predicate),
                symbolic(head)
            );
        }
    }
}

/// Build the bucketize-and-aggregate chain `converse(keys) ≫ map(values)`
/// : `K ⇒ (I ⇒ V)` from a key-extraction morphism `keys : I ⇒ K` and a value
/// morphism `values : I ⇒ V` over the shared element-index domain `I`. Shared
/// by the pointful recognizer ([`convert_groupby_pointful`]); the surrounding aggregate is
/// composed on by the caller and `wrap_with_iterate` prepends the `iterate`.
fn emit_groupby(
    keys: Expr,
    values: Expr,
    group_idx_ty: Type,
    key_binder: Option<Name>,
    key_dom: Type,
    value_ty: Type,
) -> Expr {
    // A partition is a **collection of collections**: keyed by `K`, each group the
    // index set of its members. Both are data — the transformer
    // (`map`, taking one collection to another) stays a capability.
    //
    // `group_idx_ty` is the group's *refined* index set `{I | key(i) == k}`, and
    // `key_binder` the `k` its predicate closes over, both taken from the source
    // this chain replaces. A group holds the members sharing one key, and for a
    // data function the domain *is* the data, so typing the group as the bare `I`
    // would claim every element belongs to every group. Consumers demand the
    // refined form (a per-group aggregate casts to it), and the bare one is only
    // readable as its supertype under the contravariant reading of a function —
    // wrong for a collection. The binder must ride the function type as a Pi for the
    // predicate's `k` to stay bound.
    // Construction closes (`Type::pi_kinded`): the group's predicate references
    // the key binder, and a stored function spells that reference as an index,
    // so building it with a bare literal would leave the name free and the
    // checker's rebuilt (closed) type would no longer match the recorded one.
    let partition = |codomain: Type| match &key_binder {
        Some(k) => Type::pi_kinded(k.clone(), key_dom.clone(), codomain, FunKind::Data(None)),
        None => Type::data_fun(key_dom.clone(), codomain),
    };
    let group_of = |codomain: Type| Type::data_fun(group_idx_ty.clone(), codomain);

    let converse_ty = partition(group_of(group_idx_ty.clone()));
    let grouped = apply_primitive(keys, Builtin::Converse, converse_ty);
    typecheck(&grouped).expect("Bad group expr");
    let values_fn = apply_primitive(
        values,
        Builtin::Map,
        Type::fun(group_of(group_idx_ty.clone()), group_of(value_ty.clone())),
    );
    let grouped_values_ty = partition(group_of(value_ty));
    typecheck(&values_fn).expect("Bad values_fn expr");
    let grouped_values = compose(grouped, values_fn).with_ty(grouped_values_ty);
    typecheck(&grouped_values).expect("Bad grouped_values expr");
    grouped_values
}

/// A refinement that **partitions** its domain by a key: `{𝑖 | 𝑖 ▷ path ▷ key == 𝑘}`
/// — every element reaches `key` through the refinement binder, and the result is
/// compared against a `𝑘` bound *outside* the refinement, which names *which*
/// partition this is.
///
/// This is the durable half of group-by recognition, and the half worth growing. It
/// is a fact about a **refinement**, so it holds however that refinement arrived —
/// today only the `groupby` lowering writes one, but a user-written or
/// pass-generated refinement of the same shape is the same partition and should plan
/// the same way. Nothing here knows about `const`, `cast`, or `Compose`; matching the
/// particular term a site is spelled in is [`match_pointful_site`]'s job.
struct PartitionKey<'a> {
    /// The key morphism, applied to `elem_path` — `key` in `𝑖 ▷ path ▷ key`.
    key_fn: &'a Expr,
    /// What `key_fn` is applied to: the path from the refinement binder to the value
    /// being keyed (`𝑖 ▷ path`). A rewriter must check this reaches the collection it
    /// intends to group.
    elem_path: &'a Expr,
}

/// Read a [`PartitionKey`] off a refinement predicate, or `None` if it does not
/// partition.
///
/// The key binder is identified structurally, as the free variable on one side of an
/// equality whose other side extracts the element — deliberately *not* by matching a
/// Pi name, which the comprehension's discharge may have stripped.
fn partition_key_of(predicate: &Expr) -> Option<PartitionKey<'_>> {
    let TypedExprNode::BinOp {
        left,
        op: BinOpKind::Compare(CompareKind::Equals),
        right,
    } = &predicate.node
    else {
        return None;
    };
    // One side extracts the element; the other is the free key binder.
    let extract = if side_extracts_element(left) && is_free_var(right) {
        left
    } else if side_extracts_element(right) && is_free_var(left) {
        right
    } else {
        return None;
    };
    let TypedExprNode::Apply {
        function: key_fn,
        argument: elem_path,
    } = &extract.node
    else {
        return None;
    };
    Some(PartitionKey { key_fn, elem_path })
}

/// Match the **pointful** group-by site: a `Compose` whose head is
/// `const(cast(c)) : (𝑘) ⇒ ({𝑖: 𝐼 | 𝑖 ▷ c ▷ key == 𝑘} ⇒ 𝑉)`, the form lambda-elim
/// produces for `groupby(c, key)`.
///
/// This is the *syntactic* half — coupling to how a site is currently spelled, as
/// opposed to [`partition_key_of`]'s question of whether a refinement partitions at
/// all. Keep it narrow; grow the other one.
///
/// Returns the pieces `emit_groupby` needs, or `None` (in which case the site falls
/// back to the generic iterate/restrict lowering).
struct PointfulSite<'a> {
    /// The collection the group-by ranges over — the cast's value.
    collection: &'a Expr,
    /// The key morphism read off the partition refinement. Owned: the refinement it is
    /// read from lives on the *opened* codomain, which is built here and does not outlive
    /// the match.
    key_fn: Expr,
    /// The key binder the group's predicate closes over, taken from the outer Pi. It
    /// has to ride the rebuilt arrow as a Pi for that `𝑘` to stay bound.
    key_binder: Option<Name>,
    /// The **extracted** key type — bare `𝐾`. The key morphism `c ≫ key` produces
    /// plain keys: which of them are present is a fact about the partition, not about
    /// what the extraction yields.
    key_ty: Type,
    /// The partition's domain — `𝐾` refined by this site's present-key domain. What
    /// `Converse` *produces* is exactly the present keys, so this is the honest domain
    /// of the rebuilt chain and the type it is stamped at.
    key_dom: Type,
    /// The element index set carrying every refinement **except** the consumed grouping
    /// equation. An ordinary filter on the grouped collection rides in the same set and is
    /// not this rewrite's to drop, so it travels on the key stream's domain.
    value_idx_ty: Type,
    /// The group's refined index set `{𝐼 | key(𝑖) == 𝑘}`. A group holds the members
    /// sharing one key, and for a data function the domain *is* the data, so the bare
    /// `𝐼` would claim every element belongs to every group.
    group_idx_ty: Type,
    value_ty: Type,
}

fn match_pointful_site(head: &Expr) -> Option<PointfulSite<'_>> {
    let TypedExprNode::Apply {
        argument: cast_expr,
        function: const_fn,
    } = &head.node
    else {
        return None;
    };
    if !is_builtin(const_fn, Builtin::Const) {
        return None;
    }
    let TypedExprNode::Cast {
        value: collection, ..
    } = &cast_expr.node
    else {
        return None;
    };
    // head.ty = (k: K) ⇒ ({I | pred} ⇒ V) — read the types name-agnostically. The
    // outer arrow's domain is the key domain `{K | k ▷ (𝑚 ▷ collection_contains)}` when the source
    // came through `reify` (the keyed-collection `groupby` realization).
    // `Converse`'s key-extraction morphism `c ≫ key` produces plain keys, so strip
    // refinements here: the group key type is the bare `K`, the "present" identity
    // being emergent from `Converse` rather than carried on the extracted key. (The
    // key domain on the *result* stays on downstream consumer types — it faithfully
    // names the present-key domain — and is never executed as a filter; see
    // `src/ccl/design/collections.md`.)
    let Type::Fun {
        name: key_binder,
        domain: key_ty,
        codomain: inner,
        ..
    } = &head.ty
    else {
        return None;
    };
    // Descent opens (`src/ccl/design/type-inference.md`, "Where the conversions
    // run"): the family is stored closed, so `pred`'s reference to the key is an
    // index until the codomain is read under the binder. The match below is
    // structural on that reference being a free `Var`.
    let inner = crate::ccl::subst::open_codomain(&head.ty, inner);
    let Type::Fun {
        domain: refined_dom,
        codomain: value_ty,
        ..
    } = &inner
    else {
        return None;
    };
    // A domain carries a refinement **set**, and the grouping equation is one member of
    // it: an ordinary filter on the grouped collection rides alongside, and is not this
    // rewrite's to consume. Nothing distinguishes the grouping refinement positionally —
    // the set is unordered — which is why the recognizer asks what a refinement *says*.
    let Type::Refinement(idx_ty, refinements) = refined_dom.as_ref() else {
        return None;
    };
    let (key_eq, partition) = refinements
        .iter()
        .enumerate()
        .find_map(|(i, r)| partition_key_of(&r.predicate).map(|p| (i, p)))?;

    // The rebuild below composes `key_fn` onto *this site's* `collection`, so the
    // partition's element path must be exactly `__elem ▷ collection` — the element binder
    // applied to that same collection, one stage. A multi-stage
    // `__elem ▷ c ▷ key1 ▷ key2` would peel only the outer `key2` and silently drop
    // `key1`, miscompiling the grouping.
    //
    // Eliminating the path first is what makes the two copies comparable: the head's came
    // through `lambda_elim` and is point-free, while a copy living inside a *type* did not,
    // so for anything but a bare literal they are the same collection at different stages.
    // The comparison is then the type-blind predicate relation, the copies still differing
    // in inference metadata.
    let TypedExprNode::Apply {
        argument: elem,
        function: path_of,
    } = &partition.elem_path.node
    else {
        return None;
    };
    if !matches!(&elem.node, TypedExprNode::Var(n) if n.is_elem()) {
        return None;
    }
    let path_pf = lambda_elim::run((**path_of).clone()).ok()?;
    if !crate::ccl::eq_refinement_predicate(&path_pf, collection) {
        return None;
    }

    Some(PointfulSite {
        collection,
        key_binder: key_binder.clone(),
        key_fn: partition.key_fn.clone(),
        key_ty: ccl_utils::strip_refinements(key_ty),
        key_dom: (**key_ty).clone(),
        value_idx_ty: Type::refined(
            (**idx_ty).clone(),
            refinements
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != key_eq)
                .map(|(_, r)| r.clone())
                .collect(),
        ),
        group_idx_ty: (**refined_dom).clone(),
        value_ty: (**value_ty).clone(),
    })
}

/// Pointful group-by recognizer (design §6.5): rewrite a matched
/// [`PointfulSite`] to the bucketize chain [`emit_groupby`] builds. `expr` is a
/// `Compose` whose head is the source; the head is replaced and the tail (the
/// per-group aggregate) kept.
fn convert_groupby_pointful(expr: &Expr) -> Option<Expr> {
    match &expr.node {
        // Consumed in place: `groupby(c, key) ≫ <per-group aggregate>`. Replace the head
        // and keep the tail.
        TypedExprNode::Compose(elts) => {
            let grouped = rewrite_groupby_source(elts.first()?)?;
            let mut new_elts = vec![grouped];
            new_elts.extend(elts.iter().skip(1).cloned());
            Some(typed_compose(new_elts).with_ty(expr.ty.clone()))
        }
        // **Not** consumed in place — a `let`-bound grouping, whose uses are per-key
        // lookups or iterations of the grouping itself. Matching it here is what lets it
        // stay bound and be shared: the generic fallback would try to iterate its *key*
        // domain, which is an element type rather than an index set.
        _ => rewrite_groupby_source(expr),
    }
}

/// The group-by source rewrite: recognize the pointful site and return the equivalent
/// bucketize chain. See [`convert_groupby_pointful`].
fn rewrite_groupby_source(head: &Expr) -> Option<Expr> {
    let site = match_pointful_site(head)?;
    // Compile the pointful key function to a point-free morphism V ⇒ K, then
    // build `keys = c ≫ key : I ⇒ K` and `values = c : I ⇒ V`.
    // This lifts a term out of a *type* — the refined domain's predicate — into
    // the term tree. A predicate interior may already alias a live main-tree id
    // (lowering shares a comprehension's source term between the generator and
    // the guard), so a lift can land ids that are already in use. `lambda_elim::run`
    // rebuilds the term, re-minting every node, which is what makes the crossing
    // safe; `groupby_recognition_lifts_the_key_without_aliasing` pins the property
    // rather than the mechanism.
    let key_pf = lambda_elim::run(site.key_fn).ok()?;
    // The key stream: the collection read through its key function, so it is a
    // collection too, and it carries the kind of the source it is a read of. Its domain
    // keeps every refinement except the consumed grouping equation — dropping them here
    // would silently discard a filter.
    let keys = compose(site.collection.clone(), key_pf).with_ty(Type::fun_like(
        &site.collection.ty,
        site.value_idx_ty.clone(),
        site.key_ty.clone(),
    ));
    Some(emit_groupby(
        keys,
        site.collection.clone(),
        site.group_idx_ty,
        site.key_binder,
        site.key_dom,
        site.value_ty,
    ))
}

/// Is `e` the element-extraction `__elem ▷ …` — an application whose innermost
/// argument is the refinement element binder?
fn side_extracts_element(e: &Expr) -> bool {
    match &e.node {
        TypedExprNode::Apply { argument, .. } => {
            matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem())
                || side_extracts_element(argument)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::*;
    use crate::ccl::context::assert_unique_node_ids;
    use crate::ccl::{Name, Refinement};
    use std::rc::Rc;

    #[test]
    fn test_recognize_groupby_sites_on_var() {
        let mut expr = var("x");
        recognize_groupby_sites(&mut expr);
        // Should remain unchanged
        assert!(matches!(expr.node, TypedExprNode::Var(ref v) if v.base() == "x"));
    }

    /// `const(cast(c)) : (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)` composed with a
    /// tail — the pointful group-by source the recognizer matches, with the key
    /// morphism deliberately **shared** between the predicate and the tail.
    ///
    /// The sharing is built by hand because it is the case the lift has to
    /// survive, not one the pipeline hands over: a term reached through a type
    /// carrying the ids of a live main-tree term. Recognition must re-mint rather
    /// than assume the two are already distinct.
    fn groupby_source_sharing_its_key(key: &Expr) -> Expr {
        let idx = Type::UIntRange(4);
        let int = int_ty();
        let c = var("c").with_ty(fun_ty(idx.clone(), int.clone()));

        // pred = (__elem ▷ c ▷ key) == k
        let elem = Expr::var(Name::elem()).with_ty(idx.clone());
        let elem_c = Expr::apply(elem, c.clone()).with_ty(int.clone());
        let extract = Expr::apply(elem_c, key.clone()).with_ty(int.clone());
        let pred = Expr::binop(
            extract,
            BinOpKind::Compare(CompareKind::Equals),
            var("k").with_ty(int.clone()),
        )
        .with_ty(bool_ty());

        let head_ty = fun_ty(
            int.clone(),
            fun_ty(refined_ty(idx.clone(), pred), int.clone()),
        );
        let cast = Expr::cast(c.clone(), fun_ty(idx, int)).with_ty(c.ty.clone());
        let head = apply_builtin(cast, Builtin::Const, Type::Hole, head_ty.clone());
        // The tail stands in for the live main-tree occurrence of the shared key.
        Expr::compose(vec![head, key.clone()]).with_ty(head_ty)
    }

    /// Recognition lifts the key extraction out of a *type* and into the term
    /// tree, and the lifted copy must not carry ids that are still live
    /// elsewhere. Today `lambda_elim::run` provides that by rebuilding the term;
    /// this pins the *property* rather than the mechanism, so an elim that
    /// started preserving ids fails here instead of at a pane pair's fold.
    #[test]
    fn groupby_recognition_lifts_the_key_without_aliasing() {
        let key = var("key").with_ty(fun_ty(int_ty(), int_ty()));
        let mut expr = groupby_source_sharing_its_key(&key);
        recognize_groupby_sites(&mut expr);

        assert!(
            !matches!(&expr.node, TypedExprNode::Compose(elts)
                if matches!(&elts[0].node, TypedExprNode::Apply { function, .. }
                    if is_builtin(function, Builtin::Const))),
            "the recognizer must have rewritten the source: {}",
            symbolic(&expr)
        );
        assert_unique_node_ids(&expr, "planning::groupby");
    }

    // --- `partition_key_of`: the durable half ---------------------------------
    //
    // These test the *analysis* directly rather than through a compiled program,
    // because it is the piece meant to grow: a new pattern should be able to state
    // what it does and does not recognize here, not have it inferred from an
    // end-to-end golden that only says "the plan changed".

    /// `__elem ▷ c ▷ key` — the element reaching a key morphism through the
    /// refinement binder.
    fn extraction(collection: &str, key: &str) -> Expr {
        Expr::apply(
            Expr::apply(Expr::var(Name::elem()), var(collection)),
            var(key),
        )
    }

    fn equals(left: Expr, right: Expr) -> Expr {
        Expr::binop(left, BinOpKind::Compare(CompareKind::Equals), right)
    }

    #[test]
    fn partition_key_reads_the_key_morphism_from_either_orientation() {
        for pred in [
            equals(extraction("c", "key"), var("k")),
            // The comparison is symmetric, and lowering does not guarantee a side.
            equals(var("k"), extraction("c", "key")),
        ] {
            let p = partition_key_of(&pred).expect("an equality against a free binder partitions");
            assert!(
                matches!(&p.key_fn.node, TypedExprNode::Var(n) if n.base() == "key"),
                "key morphism should be the outermost application"
            );
            assert!(
                matches!(&p.elem_path.node, TypedExprNode::Apply { argument, .. }
                    if matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem())),
                "element path should start at the refinement binder"
            );
        }
    }

    #[test]
    fn partition_key_rejects_non_partitions() {
        let cases: Vec<(&str, Expr)> = vec![
            (
                "not an equality — an ordinary filter refinement",
                Expr::binop(
                    Expr::var(Name::elem()),
                    BinOpKind::Compare(CompareKind::Less),
                    Expr::lit(Lit::Int(2)),
                ),
            ),
            (
                "neither side reaches the element — no partitioning at all",
                equals(var("a"), var("b")),
            ),
            (
                "both sides extract: a self-join condition, not a key partition",
                equals(extraction("c", "key1"), extraction("c", "key2")),
            ),
            (
                "the other side is the element too, so nothing names the partition",
                equals(extraction("c", "key"), Expr::var(Name::elem())),
            ),
        ];
        for (why, pred) in cases {
            assert!(partition_key_of(&pred).is_none(), "{why}");
        }
    }

    /// A partitioning refinement at a site the rewriter cannot rebuild from is a
    /// **near miss**: the analysis says yes, the site match says no, and the plan
    /// falls back rather than miscompiling. Pins that the two halves are genuinely
    /// independent — the whole point of the split.
    #[test]
    fn a_partition_at_an_unrecognized_site_falls_back() {
        let pred = equals(extraction("c", "key"), var("k"));
        assert!(partition_key_of(&pred).is_some());

        // The head is a bare var, not `const(cast(c))`, so there is nothing to read
        // the collection off of.
        let refined = Type::refined_one(int_ty(), Refinement::born(Rc::new(pred)));
        let head = var("src").with_ty(fun_ty(int_ty(), fun_ty(refined, int_ty())));
        assert!(
            match_pointful_site(&head).is_none(),
            "an unrecognized site must decline, not guess"
        );

        let mut expr = Expr::compose(vec![head, var("agg")]);
        let before = symbolic(&expr);
        recognize_groupby_sites(&mut expr);
        assert_eq!(
            symbolic(&expr),
            before,
            "a near miss must leave the term alone"
        );
    }
}

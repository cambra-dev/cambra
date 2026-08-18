//! Pointful group-by recognizer/rewrite (design §6.5).
//!
//! [`recognize_groupby_sites`] walks the tree before the iteration-site
//! materialisation walk and rewrites each group-by source (the dependent
//! refinement `const(cast(c)) : (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)`) to the
//! bucketize-and-aggregate chain `converse(c ≫ key) ≫ map(c)` built by
//! [`emit_groupby`].

use super::*;
use crate::ccl::Refinement;
use crate::ccl::ty::FunKind;

/// Recognize group-by sites and rewrite them to the bucketize chain.
///
/// Group-by lowers to the dependent-refinement source `const(cast(c)) :
/// (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)`; [`convert_groupby_pointful`] matches
/// that **pointful** form (design §6.5) and rewrites it to
/// `converse(c ≫ key) ≫ map(c)`. Walks the tree, rewriting every such site
/// (a rewritten site's tail may contain further sites).
pub(super) fn recognize_groupby_sites(expr: &mut Expr) {
    // The recording names the composition site — the term-tree node the
    // bucketize chain replaces — and deliberately not the key morphism the
    // rewrite lifts out of the refined domain's predicate. The composition is
    // what the user's `groupby(...)` became and what the chain now stands in
    // for; the lifted key keeps its own parentage, since a clone's copy carries
    // the predicate node it was freshened from rather than the node named here.
    // `Nature::Expansion` for the same reason.
    //
    // Scoped to the *attempt* and closed before the child walk. Recursing under
    // it would make a nested site's products descend from this one; a
    // non-matching node mints nothing, so wrapping the attempt costs a push and
    // a pop.
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
    expr.walk_children_mut(recognize_groupby_sites);
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
    key_ty: Type,
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
        Some(k) => Type::pi_kinded(k.clone(), key_ty.clone(), codomain, FunKind::Data),
        None => Type::data_fun(key_ty.clone(), codomain),
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

/// Pointful group-by recognizer (design §6.5). Match the source
/// `const(cast(c)) : (k) ⇒ ({i: I | i ▷ c ▷ key == k} ⇒ V)` — the form
/// lambda-elim now produces for `groupby(c, key)` — and rewrite it to the same
/// bucketize chain `emit_groupby` builds. The group-by **key binder** is
/// identified structurally as the free variable on one side of the predicate's
/// equality (not by a Pi-name match, which the comprehension's discharge may
/// have stripped). `expr` is a `Compose` whose head is the source; the head is
/// replaced and the tail (the per-group aggregate) kept. Returns `None` if the
/// shape doesn't match.
fn convert_groupby_pointful(expr: &Expr) -> Option<Expr> {
    match &expr.node {
        // Consumed in place: `groupby(c, key) ≫ <per-group aggregate>`. Replace
        // the head and keep the tail.
        TypedExprNode::Compose(elts) => {
            let grouped = rewrite_groupby_source(elts.first()?)?;
            let mut new_elts = vec![grouped];
            new_elts.extend(elts.iter().skip(1).cloned());
            Some(typed_compose(new_elts).with_ty(expr.ty.clone()))
        }
        // **Not** consumed in place — a `let`-bound grouping, whose uses are
        // per-key lookups or iterations of the grouping itself. Matching it here
        // is what lets it stay bound and be shared: the generic fallback would
        // try to iterate its *key* domain, which is an element type rather than
        // an index set.
        _ => rewrite_groupby_source(expr),
    }
}

/// The group-by source rewrite: match `const(cast(c)) : (k) ⇒ ({i: I | i ▷ c ▷ key == k} ⇒ V)`
/// and return the equivalent bucketize chain. See [`convert_groupby_pointful`].
fn rewrite_groupby_source(head: &Expr) -> Option<Expr> {
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
    let TypedExprNode::Cast { value: c, .. } = &cast_expr.node else {
        return None;
    };
    // head.ty = (k: K) ⇒ ({I | pred} ⇒ V) — read the types (name-agnostic).
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
    let Type::Refinement(idx_ty, refinements) = refined_dom.as_ref() else {
        return None;
    };
    // Find the refinement that *is* the grouping equation, by its shape. The domain
    // may carry other refinements (an ordinary filter on the grouped collection);
    // they are not this rewrite's to consume, so they ride along on the index
    // type below. Nothing distinguishes the grouping refinement positionally — the
    // set is unordered — which is exactly why the recognizer asks what a refinement
    // *says* rather than where it sits.
    let (key_eq, extract) = refinements
        .iter()
        .enumerate()
        .find_map(|(i, r)| groupby_key_extraction(r).map(|e| (i, e)))?;
    // extract = r ▷ c ▷ key = Apply { argument: Apply { argument: Var(r), .. }, function: key }
    let TypedExprNode::Apply {
        function: key_expr,
        argument: extract_arg,
    } = &extract.node
    else {
        return None;
    };
    // The group-by lowering only ever emits a *single-stage* key extraction
    // `r ▷ c ▷ key`, so `extract_arg` (what `key` is applied to) must be exactly
    // `r ▷ c` — its own argument the bare element binder. A multi-stage
    // extraction (`r ▷ c ▷ key1 ▷ key2`) would peel only the outermost `key`
    // and silently drop the inner stage(s) below, miscompiling the grouping;
    // like every other shape mismatch in this recognizer, fall back to the
    // generic iterate/restrict lowering instead. (`keys` below is built from
    // the head's `c`, trusting it matches the `c` inside this extraction —
    // also a lowering invariant.)
    if !matches!(&extract_arg.node, TypedExprNode::Apply { argument: a, .. } if matches!(&a.node, TypedExprNode::Var(n) if n.is_elem()))
    {
        return None;
    }

    // Compile the pointful key function to a point-free morphism V ⇒ K, then
    // build `keys = c ≫ key : I ⇒ K` and `values = c : I ⇒ V`.
    // This lifts a term out of a *type* — the refined domain's predicate — into
    // the term tree, while the predicate keeps its own copy on the type. Landing
    // the lifted ids as they are would put one id-set on two live terms, which
    // the predicate uniqueness walk reports at the next phase boundary.
    // `lambda_elim::run` rebuilds the term, re-minting every node, which is what
    // makes the crossing safe; `groupby_recognition_lifts_the_key_without_aliasing`
    // pins the property rather than the mechanism.
    let key_pf = lambda_elim::run((**key_expr).clone()).ok()?;
    // Every refinement except the consumed grouping equation stays on the index
    // domain — dropping them here would silently discard a filter.
    let value_idx_ty = Type::refined(
        (**idx_ty).clone(),
        refinements
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != key_eq)
            .map(|(_, r)| r.clone())
            .collect(),
    );
    let keys =
        compose((**c).clone(), key_pf).with_ty(Type::fun(value_idx_ty.clone(), (**key_ty).clone()));
    let grouped_values = emit_groupby(
        keys,
        (**c).clone(),
        (**refined_dom).clone(),
        key_binder.clone(),
        (**key_ty).clone(),
        (**value_ty).clone(),
    );

    Some(grouped_values)
}

/// Read a refinement as a group-by key equation, yielding its element-extraction
/// side: the bare predicate binds the implicit `REFINEMENT_BINDER` as the
/// element, so the grouping refinement reads `(__elem ▷ c ▷ key) == <key binder>` —
/// one side extracting from the element, the other a free key binder.
fn groupby_key_extraction(r: &Refinement) -> Option<&Expr> {
    let TypedExprNode::BinOp {
        left,
        op: BinOpKind::Compare(CompareKind::Equals),
        right,
    } = &r.predicate.node
    else {
        return None;
    };
    let (left, right) = (left.as_ref(), right.as_ref());
    if side_extracts_element(left) && is_free_var(right) {
        Some(left)
    } else if side_extracts_element(right) && is_free_var(left) {
        Some(right)
    } else {
        None
    }
}

/// Is `e` the element-extraction `__elem ▷ c ▷ key` — an application whose
/// innermost argument is the refinement element binder?
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
}

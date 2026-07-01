//! Pointful group-by recognizer/rewrite (design §6.5).
//!
//! [`recognize_groupby_sites`] walks the tree before the iteration-site
//! materialisation walk and rewrites each group-by source (the dependent
//! refinement `const(cast(c)) : (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)`) to the
//! bucketize-and-aggregate chain `converse(c ≫ key) ≫ map(c)` built by
//! [`emit_groupby`].

use super::*;

/// Recognize group-by sites and rewrite them to the bucketize chain.
///
/// Group-by lowers to the dependent-refinement source `const(cast(c)) :
/// (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)`; [`convert_groupby_pointful`] matches
/// that **pointful** form (design §6.5) and rewrites it to
/// `converse(c ≫ key) ≫ map(c)`. Walks the tree, rewriting every such site
/// (a rewritten site's tail may contain further sites).
pub(super) fn recognize_groupby_sites(expr: &mut Expr) {
    if let Some(rewritten) = convert_groupby_pointful(expr) {
        *expr = rewritten;
        expr.walk_children_mut(recognize_groupby_sites);
        return;
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
    value_idx_ty: Type,
    key_ty: Type,
    value_ty: Type,
) -> Expr {
    let converse_ty = Type::fun(
        key_ty.clone(),
        Type::fun(value_idx_ty.clone(), value_idx_ty.clone()),
    );
    let grouped = apply_primitive(keys, Builtin::Converse, converse_ty);
    typecheck(&grouped).expect("Bad group expr");
    let values_fn = apply_primitive(
        values,
        Builtin::Map,
        Type::fun(
            Type::fun(value_idx_ty.clone(), value_idx_ty.clone()),
            Type::fun(value_idx_ty.clone(), value_ty.clone()),
        ),
    );
    let grouped_values_ty = Type::fun(key_ty, Type::fun(value_idx_ty, value_ty));
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
    let TypedExprNode::Compose(elts) = &expr.node else {
        return None;
    };
    let head = elts.first()?;
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
        domain: key_ty,
        codomain: inner,
        ..
    } = &head.ty
    else {
        return None;
    };
    let Type::Fun {
        domain: refined_dom,
        codomain: value_ty,
        ..
    } = inner.as_ref()
    else {
        return None;
    };
    let Type::Refinement(idx_ty, refinement) = refined_dom.as_ref() else {
        return None;
    };
    // The bare predicate binds the implicit REFINEMENT_BINDER as the element:
    //   pred = (__elem ▷ c ▷ key) == <key binder>
    let pred = &*refinement.predicate;
    let TypedExprNode::BinOp {
        left,
        op: BinOpKind::Compare(CompareKind::Equals),
        right,
    } = &pred.node
    else {
        return None;
    };
    // Identify which side is the element-extraction `__elem ▷ c ▷ key` and which
    // is the free key binder (a `Var` not bound by the element).
    let extract = if side_extracts_element(left) && is_free_var(right) {
        left
    } else if side_extracts_element(right) && is_free_var(left) {
        right
    } else {
        return None;
    };
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
    let key_pf = lambda_elim::run((**key_expr).clone()).ok()?;
    let value_idx_ty = (**idx_ty).clone();
    let keys =
        compose((**c).clone(), key_pf).with_ty(Type::fun(value_idx_ty.clone(), (**key_ty).clone()));
    let grouped_values = emit_groupby(
        keys,
        (**c).clone(),
        value_idx_ty,
        (**key_ty).clone(),
        (**value_ty).clone(),
    );

    let mut new_elts = vec![grouped_values];
    new_elts.extend(elts.iter().skip(1).cloned());
    Some(typed_compose(new_elts).with_ty(expr.ty.clone()))
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

    #[test]
    fn test_recognize_groupby_sites_on_var() {
        let mut expr = var("x");
        recognize_groupby_sites(&mut expr);
        // Should remain unchanged
        assert!(matches!(expr.node, TypedExprNode::Var(ref v) if v.base() == "x"));
    }
}

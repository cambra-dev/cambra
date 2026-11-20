//! Refinement erasure: the phase after [`crate::ccl::mut_elim::run`] that drops every
//! refinement except those inside a data function's domain.
//!
//! A data function's domain refinement is the extent planning and op-conversion iterate, so the
//! phase keeps it. No phase below reads any other refinement. Every check from this phase on runs
//! in [`crate::ccl::infer::CheckMode::RefinementBlind`], which compares refinements only between
//! the domains of two data functions. A proven lookup's `match` relies on an erased refinement,
//! so the phase rewrites it into the application it denotes. See
//! `src/ccl/design/optimization.md`, "Refinement Erasure (`ccl/erase_refinements.rs`)".

use crate::ccl::{Expr, Type, TypedExprNode};

/// Run the phase over a post-`mut_elim` tree.
pub fn run(mut expr: Expr) -> Expr {
    erase_refinements(&mut expr);
    apply_proven_lookups(&mut expr);
    expr
}

/// Rewrite each proven lookup into the application it denotes:
/// `match ((𝑐, 𝑘) ▷ lookup?) { Option::some(𝑝) → body }  ⟹  let 𝑝 = 𝑘 ▷ 𝑐 in body`, where the
/// match has no other arm and refutes `Option::none`.
///
/// Inference refutes `none` from the lookup's refinement, which states that `𝑘` lies in `𝑐`'s
/// domain (`src/ccl/design/collections.md`, "The checked lookup's refinement"). Where `𝑘` lies
/// in the domain, the lookup answers `some(𝑘 ▷ 𝑐)`. This phase erases the refinement that holds
/// the proof, so the `match` is rewritten here, where no type states a fact about the lookup.
/// The application converts for any codomain, and the checked lookup's operator carries only a
/// scalar payload.
///
/// A-normalization binds the lookup before the `match` reads it, so the rewrite also takes the
/// form `let 𝑎 = (𝑐, 𝑘) ▷ lookup? in … match 𝑎 { … } …` where `𝑎` has no other use, and drops
/// the binding.
fn apply_proven_lookups(expr: &mut Expr) {
    expr.walk_children_mut(apply_proven_lookups);
    if let TypedExprNode::Case {
        scrutinee: Some(scrutinee),
        ..
    } = &expr.node
        && let Some((collection, key)) = lookup_pair(scrutinee)
    {
        let (collection, key) = (
            collection.clone_preserving_ids(),
            key.clone_preserving_ids(),
        );
        if let Some(applied) = applied_arm(expr, collection, key) {
            *expr = applied;
        }
        return;
    }
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut expr.node
    else {
        return;
    };
    let Some((collection, key)) = lookup_pair(bound_expr) else {
        return;
    };
    if crate::ccl::ccl_utils::count_free_in_value(&binding.name, body) != 1 {
        return;
    }
    let (collection, key) = (
        collection.clone_preserving_ids(),
        key.clone_preserving_ids(),
    );
    let name = binding.name.clone();
    if rewrite_use(body, &name, &collection, &key) {
        let body = std::mem::replace(body.as_mut(), Expr::throwaway(TypedExprNode::Error));
        *expr = body;
    }
}

/// Rewrite the one `match` on `name` in `expr` that [`applied_arm`] answers, reporting whether
/// one was.
fn rewrite_use(expr: &mut Expr, name: &crate::ccl::Name, collection: &Expr, key: &Expr) -> bool {
    if let TypedExprNode::Case {
        scrutinee: Some(scrutinee),
        ..
    } = &expr.node
        && matches!(&scrutinee.node, TypedExprNode::Var(n) if n == name)
    {
        return match applied_arm(
            expr,
            collection.clone_preserving_ids(),
            key.clone_preserving_ids(),
        ) {
            Some(applied) => {
                *expr = applied;
                true
            }
            None => false,
        };
    }
    let mut rewritten = false;
    expr.walk_children_mut(|child| {
        rewritten |= !rewritten && rewrite_use(child, name, collection, key)
    });
    rewritten
}

/// `(𝑐, 𝑘)` where `e` is `(𝑐, 𝑘) ▷ lookup?`.
fn lookup_pair(e: &Expr) -> Option<(&Expr, &Expr)> {
    let TypedExprNode::Apply { function, argument } = &e.node else {
        return None;
    };
    if !matches!(
        function.node,
        TypedExprNode::Builtin(crate::ccl::Builtin::LookupChecked)
    ) {
        return None;
    }
    let TypedExprNode::Tuple(pair) = &argument.node else {
        return None;
    };
    let [collection, key] = pair.as_slice() else {
        return None;
    };
    Some((collection, key))
}

/// `let 𝑝 = 𝑘 ▷ 𝑐 in body` for `case`, a `match` whose one arm is `Option::some(𝑝) → body` and
/// which refutes `Option::none`; `None` for any other `match`.
fn applied_arm(case: &Expr, collection: Expr, key: Expr) -> Option<Expr> {
    let TypedExprNode::Case {
        branches, refuted, ..
    } = &case.node
    else {
        return None;
    };
    let [branch] = branches.as_slice() else {
        return None;
    };
    let pattern = branch.pattern.as_ref()?;
    let is_option_arm = |label: crate::ccl::Label| {
        matches!(&pattern.head, crate::ccl::PatternHead::Constructor { decl, ctor }
            if *decl == crate::ccl::nominal::option() && *ctor == label.name())
    };
    if !is_option_arm(crate::ccl::V_SOME)
        || !matches!(
            branch.guard.node,
            TypedExprNode::Lit(crate::ccl::Lit::Bool(true))
        )
        || refuted.as_slice() != [crate::ccl::V_NONE]
    {
        return None;
    }
    let _g = crate::ccl::provenance::enter(
        case.node_id(),
        "erase_refinements.proven_lookup",
        crate::ccl::provenance::Nature::Machinery,
    );
    let applied = Expr::apply(key, collection).with_ty(pattern.binding.ty.clone());
    let body = branch.body.clone_preserving_ids();
    let mut bound = Expr::let_bind(
        pattern.binding.name.clone(),
        pattern.binding.occurrence.clone(),
        applied,
        body,
    )
    .with_ty(case.ty.clone());
    if let TypedExprNode::Let { binding, .. } = &mut bound.node {
        binding.ty = pattern.binding.ty.clone();
    }
    Some(bound)
}

/// Erase the refinements of every type slot in `expr` per [`erase_in_type`].
///
/// A lambda whose type is a data function binds its parameter at that function's domain, so the
/// parameter keeps the domain's refinements. Lambda elimination rebuilds the lambda's type from
/// the parameter's and asserts the two agree.
fn erase_refinements(expr: &mut Expr) {
    expr.walk_type_slots_mut(erase_in_type);
    if let TypedExprNode::Lambda { param, .. } = &mut expr.node
        && let Type::Fun {
            fun_kind, domain, ..
        } = expr.ty.peel_refinements()
        && fun_kind.resolved().is_data()
    {
        param.ty = (**domain).clone();
    }
    expr.walk_children_mut(erase_refinements);
}

/// Remove every [`Type::Refinement`] layer from `ty` at any depth, except inside a data
/// function's domain, which stays as it stands.
///
/// A domain keeps the refinements on its components as well as its own: a nested
/// comprehension's domain is a product whose component carries the inner comprehension's
/// guard, and join planning reads that component's refinement. A Σ's witness kinds stay as they
/// stand, since each candidate is a data function's domain.
fn erase_in_type(ty: &mut Type) {
    match ty {
        Type::Refinement(base, _) => {
            *ty = std::mem::replace(base.as_mut(), Type::Hole);
            erase_in_type(ty);
        }
        Type::Fun {
            fun_kind,
            domain,
            codomain,
            ..
        } => {
            if !fun_kind.resolved().is_data() {
                erase_in_type(domain);
            }
            erase_in_type(codomain);
        }
        // A nominal type's argument is a data function's domain wherever its parameter is one
        // in the declaration, as `K` is in `(k: K) |=> V(k)`, so the arguments stay as they
        // stand. A refinement kept outside a domain is one no check reads.
        Type::Nominal(..) => {}
        // A component reads an earlier one only through a refinement, so the erased components
        // may read none, and a dependent tuple whose components read none is the plain tuple.
        Type::DepTuple(components) => {
            let mut components = std::mem::take(components);
            for (_, component) in &mut components {
                erase_in_type(component);
            }
            *ty = Type::closed_dep_tuple(components);
        }
        other => other.walk_children_mut(erase_in_type),
    }
}

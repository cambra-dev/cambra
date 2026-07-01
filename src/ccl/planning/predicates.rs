//! Refinement-predicate compilation (design §6.3 / §6.5).
//!
//! Predicates ride the pipeline as bare expressions over the implicit
//! `REFINEMENT_BINDER`; planning compiles each to point-free form by running
//! the lambda-elim → simplify sub-pipeline on it. [`compile_refinement_predicates`]
//! is the whole-tree pass; [`fn_of_bare_predicate`] is the inverse of
//! [`crate::ccl::ccl_utils::bare_predicate_of_fn`] that the iterate/restrict and
//! op-conversion lowering consume.

use std::collections::HashMap;
use std::rc::Rc;

use super::*;

/// Identity key for a refinement predicate — the `Rc<Expr>` address. Keyed on
/// object identity, not [`crate::ccl::RefinementId`]: a substituted/discharged
/// refinement keeps its id but holds an independently rebuilt predicate that
/// must be compiled on its own (keying by id would skip it and leave it in
/// lambda form). Maps each original predicate to its compiled, point-free
/// rebuild so every occurrence that shared one term is re-pointed at the same
/// compiled `Rc` (and compiled exactly once).
///
/// Like the value-rewrite memos elsewhere (see
/// [`ccl_utils::walk_refined_predicates_mut`]), this is a **performance /
/// structural-sharing optimization, not a correctness requirement** — verified:
/// the full suite passes with this dedup disabled. Compilation is effectively a
/// value function for comparison purposes: `lambda_elim` mints a fresh `__pair`
/// `Uid` in its nested-lambda rule, but that binder is *eliminated* within the
/// same run, so the compiled output is point-free and carries no minted binder
/// — two independent compilations of one predicate yield structurally-equal
/// terms. (The convention this rests on — no pass leaves a re-minted bound
/// binder in a term that equality later compares — is what keeps by-name
/// equality coincide with α-equivalence; `lambda_elim` upholds it by
/// eliminating `__pair` rather than the equality having to be α-aware.)
pub(super) type PredMemo = HashMap<*const Expr, Rc<Expr>>;

/// True if a `__pair` binder ([`Name::is_synthetic_pair`]) appears anywhere in
/// the **term** `e` — its node and child *expressions*, never its type slots.
///
/// Type slots are skipped on purpose: lambda elimination leaves `__pair` only
/// as a `Fun.name` Pi binder in a type slot, which every equality path ignores
/// (`eq_refinement_predicate` is type-blind; the structural reconcile strips Pi
/// names via `without_pi_names`). The invariant this backs is purely about the
/// compared term. Only reached from a `debug_assert!`, but it must compile in
/// release too (the macro still type-checks its argument), so it is not gated.
fn term_mentions_pair_binder(e: &Expr) -> bool {
    let here = match &e.node {
        TypedExprNode::Var(n) => n.is_synthetic_pair(),
        TypedExprNode::Lambda { param, .. } => param.name.is_synthetic_pair(),
        TypedExprNode::Let { binding, .. } => binding.name.is_synthetic_pair(),
        TypedExprNode::Loop { params, .. } => params.iter().any(|p| p.name.is_synthetic_pair()),
        TypedExprNode::Case { branches, .. } => branches.iter().any(|b| {
            b.pattern
                .as_ref()
                .is_some_and(|p| p.binding.name.is_synthetic_pair())
        }),
        _ => false,
    };
    if here {
        return true;
    }
    let mut found = false;
    e.walk_children(|c| found |= term_mentions_pair_binder(c));
    found
}

/// Compile every refinement predicate reachable from `expr` by running the
/// lambda-elim → simplify sub-pipeline on it (design §6.3/§6.5).
///
/// Refinement predicates ride the pipeline as bare expressions over the implicit
/// `REFINEMENT_BINDER`; this normalizes each to `__elem ▷ p` with a point-free
/// `p`, the form the recognizers and op-conversion's `Restrict` consume (it
/// recovers `p` via `fn_of_bare_predicate` and re-wraps). Each distinct predicate
/// `Rc` is compiled once.
///
/// Every type slot a node carries is compiled, not just `expr.ty`: a `Cast`'s
/// `target` and the binder-declared types (lambda param, `let` binding, etc.)
/// carry their own predicate `Rc`s. They are independent (immutable) terms, so
/// each must be normalized. For the common predicate (no nested lambdas)
/// compilation is deterministic, so a `target` and its parallel `expr.ty`
/// normalize to structurally-equal point-free predicates and still
/// match under refinement equality; for the nested-lambda case the per-`Rc`
/// memo keeps shared occurrences equal despite `lambda_elim`'s `__pair` minting
/// (see [`PredMemo`]).
pub(crate) fn compile_refinement_predicates(expr: &mut Expr, memo: &mut PredMemo) {
    compile_predicates_in_type(&mut expr.ty, memo);
    if let Some(annotation) = &mut expr.user_annotation {
        compile_predicates_in_type(annotation, memo);
    }
    match &mut expr.node {
        TypedExprNode::Lambda { param, .. } => compile_predicates_in_type(&mut param.ty, memo),
        TypedExprNode::Cast { target, .. } => compile_predicates_in_type(target, memo),
        TypedExprNode::Let { binding, .. } => compile_predicates_in_type(&mut binding.ty, memo),
        TypedExprNode::Case { branches, .. } => {
            for b in branches.iter_mut() {
                if let Some(p) = &mut b.pattern {
                    compile_predicates_in_type(&mut p.binding.ty, memo);
                }
            }
        }
        TypedExprNode::Loop { params, .. } => {
            for p in params.iter_mut() {
                compile_predicates_in_type(&mut p.ty, memo);
            }
        }
        _ => {}
    }
    expr.walk_children_mut(|child| compile_refinement_predicates(child, memo));
}

/// The point-free predicate function `p : base ⇒ Bool` underlying a refinement's
/// bare predicate `__elem ▷ p` (the inverse of [`ccl_utils::bare_predicate_of_fn`]).
/// Fast-pathed when the bare predicate is already that single application;
/// otherwise η-expands to `λ __elem → bare` and lambda-eliminates to point-free.
pub(crate) fn fn_of_bare_predicate(base: &Type, bare: &Expr) -> Expr {
    if let TypedExprNode::Apply { argument, function } = &bare.node
        && matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem())
    {
        return (**function).clone();
    }
    lambda_elim::run(Expr::lambda(Name::elem(), base.clone(), bare.clone()))
        .expect("lambda-elim of refinement predicate")
}

fn compile_predicates_in_type(ty: &mut Type, memo: &mut PredMemo) {
    if let Type::Refinement(base, refinement) = ty {
        let original = Rc::as_ptr(&refinement.predicate);
        if let Some(compiled) = memo.get(&original) {
            refinement.predicate = Rc::clone(compiled);
        } else {
            // Normalize the bare predicate to `__elem ▷ p` with `p` point-free:
            // recover the predicate function and re-wrap it. This keeps the
            // stored predicate in the single bare form while pinning a
            // point-free core, so the iterate/restrict producers (built from
            // the same `p`) carry a structurally-identical refinement to the
            // cast demand they satisfy.
            let p = fn_of_bare_predicate(base, &refinement.predicate);
            let mut compiled = ccl_utils::bare_predicate_of_fn(base, p);
            // The compiled predicate's own sub-expressions can carry *nested*
            // refinements (a filter over an already-filtered source: the inner
            // refinement rides a sub-expression's type slot inside this
            // predicate). `Type::walk_children_mut` below does not descend into
            // a predicate term, so compile those here, sharing the memo.
            compile_refinement_predicates(&mut compiled, memo);
            // The producer/consumer refinement match (`sum`'s domain vs. its
            // feed, a compose adjacency) compares *distinct* predicate `Rc`s —
            // the memo only dedups occurrences sharing one `Rc`. That match
            // rests on compilation being a deterministic value function, which
            // requires that lambda elimination's freshly-minted `__pair`
            // (`Uid::fresh()`) never survive into the compared *term*. It
            // legitimately survives as a `Fun.name` Pi binder in a type slot
            // (which `eq_refinement_predicate` is type-blind to), so the check
            // is term-only. Assert that load-bearing invariant rather than
            // leaving it argued.
            debug_assert!(
                !term_mentions_pair_binder(&compiled),
                "a `__pair` binder survived into a compiled predicate term, \
                 breaking the value-function property the structural \
                 producer/consumer match relies on: {}",
                symbolic(&compiled)
            );
            let compiled = Rc::new(compiled);
            memo.insert(original, Rc::clone(&compiled));
            refinement.predicate = compiled;
        }
    }
    // Recurse into structural type children (refinement base, function
    // domain/codomain, tuple/record/variant elements).
    ty.walk_children_mut(|child| compile_predicates_in_type(child, memo));
}

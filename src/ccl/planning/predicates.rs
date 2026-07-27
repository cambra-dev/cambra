//! Refinement-predicate compilation (design §6.3 / §6.5).
//!
//! Predicates ride the pipeline as bare expressions over the implicit
//! `REFINEMENT_BINDER`; planning compiles each to point-free form by running
//! the lambda-elim → simplify sub-pipeline on it. [`compile_refinement_predicates`]
//! is the whole-tree pass; [`fn_of_bare_predicate`] is the inverse of
//! [`crate::ccl::ccl_utils::bare_predicate_of_fn`] that the iterate/restrict and
//! op-conversion lowering consume.

use super::*;

// Predicate compilation is a predicate-*rebuilding* pass like any other, so it
// memoizes with the shared [`ccl_utils::PredMemo`] — including its keepalive
// discipline, which is load-bearing rather than incidental here: overwriting
// `refinement.predicate` with the compiled result drops the *original* `Rc` if
// that was its last strong reference, and the freed address can be handed
// straight back to an unrelated `Rc::new` later in the same walk — including one
// of `compile_predicates_in_type`'s own allocations — so an unrelated predicate
// starting life at that address would collide and inherit this entry's compiled
// form. Observed in practice: two structurally unrelated join predicates from
// different call sites landed on the same freed address and the second silently
// inherited the first's compiled form.
//
// Dedup itself is a **performance / structural-sharing optimization, not a
// correctness requirement** — verified: the full suite passes with dedup
// disabled (i.e. recompiling every occurrence independently). Compilation is
// effectively a value function for comparison purposes: `lambda_elim` mints a
// fresh `__pair` `Uid` in its nested-lambda rule, but that binder is
// *eliminated* within the same run, so the compiled output is point-free and
// carries no minted binder — two independent compilations of one predicate yield
// structurally-equal terms. (The convention this rests on — no pass leaves a
// re-minted bound binder in a term that equality later compares — is what makes
// by-name equality coincide with α-equivalence; `lambda_elim` upholds it by
// eliminating `__pair` rather than the equality having to be α-aware.)
//
// Keying on the `Rc` address rather than a refinement id is deliberate: a
// substituted/discharged refinement keeps its id but holds an independently
// rebuilt predicate that must be compiled on its own, so keying by id would skip
// it and leave it in lambda form.

/// The predicate-compilation memo, plus the precondition that makes reusing an
/// entry sound.
///
/// Compilation reads the refinement's **base** (`fn_of_bare_predicate` eta-expands
/// `λ __elem : base → bare`; `bare_predicate_of_fn` stamps `base` on the element
/// var), and the base is *not* part of [`PredMemo`]'s key. That puts this pass in
/// the same position as constraint emission — see [`PredMemo`]'s note on
/// context-determined transforms — with one difference that lets it keep the
/// skipping protocol: `base` only reaches the compiled term's **type slots**, and
/// refinement identity is type-blind, so two occurrences of one predicate `Rc`
/// compile to terms that compare equal regardless. Reusing one is therefore sound
/// *provided the bases actually agree*, which holds because a shared `Rc` is only
/// ever created by copying one refinement — but nothing in the types enforces it,
/// and if it ever failed the symptom would be an element type quietly borrowed
/// from another occurrence.
///
/// So debug builds record each entry's base and check it on the hit path. That is
/// the whole reason this wrapper exists; release builds are exactly a `PredMemo`.
pub(crate) struct CompileMemo {
    preds: PredMemo,
    #[cfg(debug_assertions)]
    bases: std::collections::HashMap<crate::ccl::PredicateId, Type>,
}

impl CompileMemo {
    pub(crate) fn new() -> Self {
        Self {
            preds: PredMemo::new(),
            #[cfg(debug_assertions)]
            bases: std::collections::HashMap::new(),
        }
    }

    /// Record the base this predicate was compiled against.
    fn record_base(&mut self, id: crate::ccl::PredicateId, base: &Type) {
        #[cfg(debug_assertions)]
        self.bases.insert(id, base.clone());
        let _ = (id, base);
    }

    /// On a memo hit, check that this occurrence's base matches the one the
    /// entry was compiled against (see the type-level note).
    fn assert_base_agrees(&self, id: crate::ccl::PredicateId, base: &Type) {
        #[cfg(debug_assertions)]
        if let Some(compiled_against) = self.bases.get(&id) {
            debug_assert!(
                ccl_utils::strip_refinements(compiled_against)
                    == ccl_utils::strip_refinements(base),
                "predicate-compilation memo hit across differing refinement bases: this \
                 occurrence is over `{base}` but the entry was compiled against \
                 `{compiled_against}`. Compilation reads the base, so the reused term \
                 carries the other occurrence's element type — see `CompileMemo`."
            );
        }
        let _ = (id, base);
    }
}

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
        TypedExprNode::LetRec { bindings, .. } => {
            bindings.iter().any(|(b, _)| b.name.is_synthetic_pair())
        }
        TypedExprNode::For { target, .. } => target.name.is_synthetic_pair(),
        TypedExprNode::MutWrite { name, .. } => name.is_synthetic_pair(),
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
/// Every type slot a node carries is compiled, not just `expr.ty`
/// ([`Expr::walk_type_slots_mut`]): a `Cast`'s `target` and the binder-declared
/// types (lambda param, `let` binding, etc.) carry their own predicate `Rc`s.
/// They are independent (immutable) terms, so each must be normalized. For the
/// common predicate (no nested lambdas) compilation is deterministic, so a
/// `target` and its parallel `expr.ty` normalize to structurally-equal point-free
/// predicates and still match under refinement equality; for the nested-lambda
/// case the per-`Rc` memo keeps shared occurrences equal despite `lambda_elim`'s
/// `__pair` minting (see [`PredMemo`]).
pub(crate) fn compile_refinement_predicates(expr: &mut Expr, memo: &mut CompileMemo) {
    expr.walk_type_slots_mut(|ty| compile_predicates_in_type(ty, memo));
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

fn compile_predicates_in_type(ty: &mut Type, memo: &mut CompileMemo) {
    if let Type::Refinement(base, refinement) = ty {
        let id = refinement.predicate_id();
        let Some((origin, bare)) = memo.preds.begin(refinement) else {
            // Hit: the entry's compiled term is reused, which is only sound while
            // the bases agree.
            memo.assert_base_agrees(id, base);
            ty.walk_children_mut(|child| compile_predicates_in_type(child, memo));
            return;
        };
        // Normalize the bare predicate to `__elem ▷ p` with `p` point-free:
        // recover the predicate function and re-wrap it. This keeps the stored
        // predicate in the single bare form while pinning a point-free core, so
        // the iterate/restrict producers (built from the same `p`) carry a
        // structurally-identical refinement to the cast demand they satisfy.
        let p = fn_of_bare_predicate(base, &bare);
        let mut compiled = ccl_utils::bare_predicate_of_fn(base, p);
        // The compiled predicate's own sub-expressions can carry *nested*
        // refinements (a filter over an already-filtered source: the inner
        // refinement rides a sub-expression's type slot inside this predicate).
        // `Type::walk_children_mut` below does not descend into a predicate term,
        // so compile those here, sharing the memo.
        compile_refinement_predicates(&mut compiled, memo);
        // The producer/consumer refinement match (`sum`'s domain vs. its feed, a
        // compose adjacency) compares *distinct* predicate `Rc`s — the memo only
        // dedups occurrences sharing one `Rc`. That match rests on compilation
        // being a deterministic value function, which requires that lambda
        // elimination's freshly-minted `__pair` (`Uid::fresh()`) never survive
        // into the compared *term*. It legitimately survives as a `Fun.name` Pi
        // binder in a type slot (which `eq_refinement_predicate` is type-blind
        // to), so the check is term-only. Assert that load-bearing invariant
        // rather than leaving it argued.
        debug_assert!(
            !term_mentions_pair_binder(&compiled),
            "a `__pair` binder survived into a compiled predicate term, \
             breaking the value-function property the structural \
             producer/consumer match relies on: {}",
            symbolic(&compiled)
        );
        memo.record_base(id, base);
        memo.preds.finish(refinement, origin, compiled);
    }
    // Recurse into structural type children (refinement base, function
    // domain/codomain, tuple/record/variant elements).
    ty.walk_children_mut(|child| compile_predicates_in_type(child, memo));
}

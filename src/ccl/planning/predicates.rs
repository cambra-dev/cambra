//! Refinement-predicate compilation (design §6.3 / §6.5).
//!
//! Predicates ride the pipeline as bare expressions over the implicit
//! `REFINEMENT_BINDER`; planning compiles each to point-free form by running
//! the lambda-elim → simplify sub-pipeline on it. [`compile_refinement_predicates`]
//! is the whole-tree pass; [`fn_of_bare_predicate`] is the inverse of
//! [`crate::ccl::ccl_utils::bare_predicate_of_fn`] that the iterate/restrict and
//! op-conversion lowering consume.

use super::*;
use crate::ccl::RefinementSet;

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

// The refinement's **base** is the memo's context (`PredMemo<Type>`), because
// compilation reads it: `fn_of_bare_predicate` eta-expands `λ __elem : base →
// bare`, and `bare_predicate_of_fn` stamps it on the element var. An entry is
// therefore reused only for an occurrence over an equal base. That holds in
// practice — a shared `Rc` is only ever created by copying one refinement — but
// nothing enforces it, and keying on the base means a mismatch *recompiles*
// rather than silently borrowing another occurrence's element type.
//
// Cost of a `Type` context: a lookup compares bases structurally, and `PartialEq`
// for a refined `Type` descends into predicate terms. Two things keep that cheap.
// The base is the type being *refined*, so it sits below the refinement rather
// than containing it — comparing `{Int | p}`'s base compares `Int`, never `p` —
// and the entry list for one key is a singleton in every shape measured, so a hit
// is one compare of a small type. The clone per refinement node is the same
// shallow value. Measured against the pre-context memo the difference is in the
// noise; a base that ever became large enough to matter would be a signal about
// the types, not about this key.

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
pub(crate) fn compile_refinement_predicates(expr: &mut Expr, memo: &PredMemo<Type>) {
    // A `Cast`'s target refinements are assertions on the cast's *value*: the
    // checker types them with `__elem` bound at the value's domain (see
    // `emit_cast`), which carries the value's own refinements. Compile them against
    // that same base — a target holds only the cast's *born* refinements, so
    // deriving the element type from the target alone would stamp `__elem`
    // bare and fail the checker's argument edge against a predicate function
    // whose domain the value's refinements narrow.
    if let TypedExprNode::Cast { value, target } = &mut expr.node {
        let value_dom = value.ty.domain();
        compile_cast_target(target, value_dom, memo);
        compile_predicates_in_type(&mut expr.ty, memo, &[]);
        compile_refinement_predicates(value, memo);
        return;
    }
    expr.walk_type_slots_mut(|ty| compile_predicates_in_type(ty, memo, &[]));
    expr.walk_children_mut(|child| compile_refinement_predicates(child, memo));
}

/// Compile a cast target's domain refinements against the value's domain (the
/// assertion base — see [`compile_refinement_predicates`]), then the rest of
/// the target generically. The top-level domain refinement must not be
/// revisited by the generic walk: recompiling it against the target's bare
/// base would re-stamp `__elem` with the narrower context lost.
fn compile_cast_target(target: &mut Type, value_dom: Option<Type>, memo: &PredMemo<Type>) {
    if let Type::Fun {
        domain, codomain, ..
    } = target
    {
        if let Type::Refinement(base, refinements) = domain.as_mut() {
            let assert_base = value_dom.unwrap_or_else(|| (**base).clone());
            compile_refinements(refinements, &assert_base, memo, &[]);
            compile_predicates_in_type(base, memo, &[]);
        } else {
            compile_predicates_in_type(domain, memo, &[]);
        }
        compile_predicates_in_type(codomain, memo, &[]);
    } else {
        compile_predicates_in_type(target, memo, &[]);
    }
}

/// The point-free predicate function `p : base ⇒ Bool` underlying a refinement's
/// bare predicate `__elem ▷ p` (the inverse of [`ccl_utils::bare_predicate_of_fn`]).
/// Fast-pathed when the bare predicate is already that single application;
/// otherwise η-expands to `λ __elem → bare` and lambda-eliminates to point-free.
///
/// `slot` is the binder telescope `base` is written under — the Σ of the collection this
/// refinement refines. A predicate over a witness-domained collection is a collection over
/// that witness (`src/ccl/design/type-inference.md`,
/// "A refinement predicate is a data function"),
/// and the η-expanded form is where that is said: the binder is the one place a kind is
/// written, so a predicate left at `Compute` names a witness nothing binds.
pub(crate) fn fn_of_bare_predicate(
    base: &Type,
    bare: &Expr,
    slot: &[crate::ccl::ty::Witness],
) -> Expr {
    if let TypedExprNode::Apply { argument, function } = &bare.node
        && matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem())
    {
        return (**function).clone();
    }
    let lam = Expr::lambda(Name::elem(), base.clone(), bare.clone());
    // **A predicate over a witness-domained collection is a collection over that witness** —
    // the boolean column the runtime `Restrict` evaluates over the extent. `Expr::lambda`
    // stamps `Compute`, which carries no binder slot, so the witness in `base` would come out
    // unbound: a reference names no kind, and the binder is the one place a kind is written
    // (`src/ccl/design/type-inference.md`, "The witness context").
    let lam = if slot.is_empty() {
        lam
    } else {
        lam.with_ty(Type::Fun {
            name: None,
            fun_kind: crate::ccl::ty::FunKind::Data(Some(std::rc::Rc::new(slot.to_vec()))),
            domain: Box::new(base.clone()),
            codomain: Box::new(Type::Base(BaseType::Bool)),
        })
    };
    lambda_elim::run(lam).expect("lambda-elim of refinement predicate")
}

fn compile_predicates_in_type(
    ty: &mut Type,
    memo: &PredMemo<Type>,
    slot: &[crate::ccl::ty::Witness],
) {
    let here = ty.sum().unwrap_or(&[]).to_vec();
    let extended: Vec<crate::ccl::ty::Witness> = if here.is_empty() {
        slot.to_vec()
    } else {
        slot.iter().cloned().chain(here).collect()
    };
    let slot = extended.as_slice();
    if let Type::Refinement(base, refinements) = ty {
        let base = base.clone();
        compile_refinements(refinements, &base, memo, slot);
    }
    // Recurse into structural type children (refinement base, function
    // domain/codomain, tuple/record/variant elements).
    // Not `walk_children_mut`: it descends into a `FunKind`'s witness candidates, and a
    // predicate typed as a collection over a witness carries the source's candidate types in
    // its own kind — walking them re-enters the refinements this predicate came out of.
    // A binder's candidates are compiled where the binder's own type is.
    match ty {
        Type::Fun {
            domain, codomain, ..
        } => {
            compile_predicates_in_type(domain, memo, slot);
            compile_predicates_in_type(codomain, memo, slot);
        }
        _ => ty.walk_children_mut(|child| compile_predicates_in_type(child, memo, slot)),
    }
}

/// Compile each refinement of a set against the element type it sees in the restrict
/// pipeline planning will build for this domain — `base` narrowed by the refinements
/// applied before it. `wrap_with_iterate` builds that pipeline from the same
/// application order, so the compiled predicates and the pipeline's types
/// agree. For a cast target's refinements, `base` is the cast value's domain (the
/// assertion base — see [`compile_refinement_predicates`]).
fn compile_refinements(
    refinements: &mut RefinementSet,
    base: &Type,
    memo: &PredMemo<Type>,
    slot: &[crate::ccl::ty::Witness],
) {
    // Indexed by physical position (`application_elem_types`), because the
    // rewrite below walks the set in place and the application order is a
    // *permutation* of the physical one.
    let elem_tys = crate::ccl::application_elem_types(refinements.as_slice(), base);
    refinements.rewrite_each(|i, refinement| {
        let base_ctx = elem_tys[i].clone();
        memo.rebuild(refinement, &base_ctx, |bare| {
            // Normalize the bare predicate to `__elem ▷ p` with `p` point-free:
            // recover the predicate function and re-wrap it. This keeps the stored
            // predicate in the single bare form while pinning a point-free core, so
            // the iterate/restrict producers (built from the same `p`) carry a
            // structurally-identical refinement to the cast demand they satisfy.
            let p = fn_of_bare_predicate(&base_ctx, bare, slot);
            let mut compiled = ccl_utils::bare_predicate_of_fn(&base_ctx, p);
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
            *bare = compiled;
            true
        });
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::ccl_utils::trivially_true_predicate;
    use crate::ccl::context::Phase;
    use crate::ccl::provenance::{NodeId, PhaseScope, ProvenanceTable, TableSession};
    use crate::ccl::{BaseType, Lit, Name};
    use std::collections::HashSet;

    /// Every id reachable from `e`, main tree only.
    fn ids_of(e: &Expr) -> HashSet<NodeId> {
        let mut out = HashSet::new();
        fn go(e: &Expr, out: &mut HashSet<NodeId>) {
            out.insert(e.node_id());
            e.walk_children(&mut |c| go(c, out));
        }
        go(e, &mut out);
        out
    }

    /// Whether walking `parents` back from `id` reaches an id in `roots` before
    /// running out of rows.
    fn resolves_into(table: &ProvenanceTable, id: NodeId, roots: &HashSet<NodeId>) -> bool {
        let mut frontier = vec![id];
        let mut seen = HashSet::new();
        while let Some(n) = frontier.pop() {
            if roots.contains(&n) {
                return true;
            }
            if !seen.insert(n) {
                continue;
            }
            frontier.extend_from_slice(table.parents(n));
        }
        false
    }

    /// Raise `bare` out of a predicate under a recording naming `site`, and
    /// report which of the result's nodes reach the predicate and which reach
    /// the site.
    fn raise(bare: &Expr, site: NodeId) -> (ProvenanceTable, Expr, HashSet<NodeId>) {
        let pred_ids = ids_of(bare);
        let session = TableSession::install();
        let raised = {
            let _scope = PhaseScope::enter(Phase::Planning);
            let _g = provenance::enter(site, "test.raise", provenance::Nature::Machinery);
            // No witness slot: the base is a scalar, so the raised function is over no
            // index a Σ named.
            fn_of_bare_predicate(&Type::Base(BaseType::Int), bare, &[])
        };
        (session.into_table(), raised, pred_ids)
    }

    /// **Both paths of `fn_of_bare_predicate` attribute the raised predicate to
    /// the predicate**, never to the term-tree site the recording names.
    ///
    /// The fast path clones, and a clone's copy names the node it was freshened
    /// from, so the predicate's parentage rides along by construction. The slow
    /// path η-expands and lambda-eliminates, minting a `Lambda` that descends
    /// from the site — but that wrapper is consumed by the elimination rather
    /// than placed, so it composes away as a transient and every node that
    /// reaches the output still resolves into the predicate.
    ///
    /// This is what makes the two agree. Before `lambda_elim` recorded, the
    /// slow path's whole product landed on the site, because the sub-run's
    /// mints fell through to the enclosing recording.
    #[test]
    fn both_raising_paths_attribute_the_predicate_to_the_predicate() {
        let int_ty = Type::Base(BaseType::Int);
        let bool_ty = Type::Base(BaseType::Bool);
        let elem = || Expr::var(Name::elem()).with_ty(int_ty.clone());
        // A real `𝐷 ⇒ Bool`, so the deep typechecker accepts the η-expansion the
        // slow path builds.
        let pred_fn = |domain: Type| trivially_true_predicate(domain);

        // Fast path: already `__elem ▷ p`, so the raise is a single clone of `p`.
        let fast = Expr::apply(elem(), pred_fn(int_ty.clone())).with_ty(bool_ty.clone());
        // Slow path, constant: `__elem` is not free, so elimination emits
        // `const(e)` and the η-wrapper never reaches the output.
        let slow_const = Expr::lit(Lit::Bool(false)).with_ty(bool_ty.clone());
        // Slow path, `__elem` free: `__elem ▷ p ▷ q`, whose outer argument is an
        // application rather than the bare `__elem`, so the fast path declines.
        let slow_free = Expr::apply(
            Expr::apply(elem(), pred_fn(int_ty.clone())).with_ty(bool_ty.clone()),
            pred_fn(bool_ty.clone()),
        )
        .with_ty(bool_ty.clone());

        for (name, bare) in [
            ("fast", fast),
            ("slow/constant", slow_const),
            ("slow/free", slow_free),
        ] {
            let site = NodeId::fresh();
            let (table, raised, pred_ids) = raise(&bare, site);
            let site_only = HashSet::from([site]);
            for id in ids_of(&raised) {
                assert!(
                    resolves_into(&table, id, &pred_ids),
                    "{name}: {id:?} does not resolve into the predicate",
                );
                assert!(
                    !resolves_into(&table, id, &site_only),
                    "{name}: {id:?} resolves to the term-tree site instead",
                );
            }
        }
    }
}

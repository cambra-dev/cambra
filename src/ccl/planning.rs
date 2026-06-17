use std::collections::{BTreeSet, HashMap, VecDeque};
use std::fmt::Debug;
use std::mem::take;
use std::rc::Rc;

use log::trace;

use crate::ccl::ccl_utils::{
    self, apply_function, make_iterate, make_restrict, refine_codomain, set_codomain,
    trivially_true_predicate, typed_compose,
};
use crate::ccl::{
    BaseType, BinOpKind, Builtin, CompareKind, Expr, Lit, LogicKind, Name, ProjKey, Type,
    TypedExprNode,
    ccl_utils::apply_primitive,
    infer::typecheck,
    lambda_elim::{self, compose, id},
    simplify::simplify,
    symbolic::{symbolic, symbolic_typed},
};

/// Returns `true` if `expr` directly references the given built-in primitive.
fn is_builtin(expr: &Expr, b: Builtin) -> bool {
    matches!(&expr.node, TypedExprNode::Builtin(x) if *x == b)
}

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
type PredMemo = HashMap<*const Expr, Rc<Expr>>;

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
fn compile_refinement_predicates(expr: &mut Expr, memo: &mut PredMemo) {
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
fn fn_of_bare_predicate(base: &Type, bare: &Expr) -> Expr {
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

/// Materialize every iteration site in the post-lambda-elim CCL, choosing
/// an efficient implementation strategy at each one.
///
/// At each iteration site (aggregate arguments, mutation-loop sources,
/// `LastOrDefault` streams, value-position `Record` fields, `CollectionUnion`
/// operands, the program's top-level function-valued result, top-level
/// let-bound function values, and a few other shapes enumerated by
/// [`insert_iterate_recurse`]), [`insert_iterate_markers`] dispatches via
/// [`wrap_with_iterate`] to:
///
/// 1. **Hash-join rewrite** ([`try_hash_join_rewrite`]) when the site's
///    domain is a refined tuple whose predicate decomposes into equality
///    join conditions.  Emitted as a `JoinPlan::Hash` / `JoinPlan::Loop`
///    tree compiled to a CCL chain whose leaves are iteration-bearing.
/// 2. **Iterate-then-restricts chain** otherwise — build the source by
///    *applying* one `restrict(p)` filter per refinement layer (innermost
///    first) to a chain-head `Apply(true ▷ const, Iterate)`, then compose
///    the value-producing body onto it: `(iterate ▷ (p_inner ▷ restrict)
///    ▷ … ▷ (p_outer ▷ restrict)) ≫ body`.  Each `restrict` *applies* to
///    its upstream — it is a function transformer, not a morphism composed
///    with the source (its honest type makes the composed form ill-typed;
///    see [`make_restrict`]).  Unrefined sites get just the chain-head
///    iterate.
///
/// Hash join is the specialised strategy; the iterate-then-restricts
/// chain is the default.  Both branches are materialising the same
/// iteration site — folding them into a single walk lets hash-join
/// planning fire at every site (not just the program root, as an earlier
/// pass did).
///
/// Also: the pointful group-by rewrite for keyed aggregates
/// ([`recognize_groupby_sites`] / [`convert_groupby_pointful`]) runs before the
/// materialisation walk.
pub fn run(mut expr: Expr) -> Expr {
    // Refinement predicates travel through inference and lambda-elim as bare
    // expressions over the implicit `REFINEMENT_BINDER` (design §6.3) and are
    // compiled to point-free form only when a refined type is iterated (§6.5).
    // The group-by recognizer runs first and matches the bare predicate
    // directly; the generic filter / hash-join paths compile the predicate
    // lazily at each iteration site (see `wrap_with_iterate`).
    recognize_groupby_sites(&mut expr);
    let mut expr = simplify(expr);
    insert_iterate_markers(&mut expr);
    // Normalize every remaining bare predicate tree-wide to point-free form.
    // `wrap_with_iterate` compiles each iteration *site*'s predicate, but a
    // refinement also rides **consumer contracts** that sit outside any site —
    // an aggregate's domain (`sum : ({D | p} ⇒ Int) ⇒ Int`), a composition
    // adjacency — carrying the same predicate as the producer they validate
    // against. With immutable predicate terms those are independent `Rc`s, so
    // the per-site compilation doesn't reach them; this whole-tree pass (one
    // shared memo) compiles them to the *same* point-free form, so the
    // post-planning typecheck's structural refinement match holds. It runs
    // after the recognizers (which already consumed the bare shapes they
    // match) and is idempotent on already-compiled predicates.
    compile_refinement_predicates(&mut expr, &mut PredMemo::new());
    // Re-run `simplify` to absorb the `id` leaves and nested `Compose`
    // boilerplate that [`try_hash_join_rewrite`] emits via
    // [`replace_tuple_project_with_id`].  `simplify` is marker-aware: its
    // structural-discard rules self-guard against dropping or relocating
    // the `Apply(_, Iterate)` / `Apply(_, Restrict)` markers just inserted,
    // so the only rules that fire here are the always-safe cleanups (plus
    // any reduction of a fully marker-free sub-tree, which is sound).
    let mut expr = simplify(expr);
    // Compilation rebuilt the immutable predicate on each node's `expr.ty`;
    // re-sync every `Cast`'s `target` slot so the post-planning typecheck's
    // reconstruction (which reads `target`) matches the compiled recorded type.
    ccl_utils::sync_cast_targets(&mut expr);
    expr
}

/// Walks `expr` and materializes every iteration site, choosing the best
/// available implementation strategy at each one.
///
/// "Iteration site" means any position where op-conversion would otherwise
/// compile with `input=None` and the expression is function-typed —
/// aggregate arguments, the stream side of `LastOrDefault`, mutation-loop
/// sources, value-position `Record` fields, `CollectionUnion` operands,
/// the program's top-level function-valued result, top-level let-bound
/// function values, and a few other shapes enumerated by
/// [`insert_iterate_recurse`].  At each site the pass dispatches via
/// [`wrap_with_iterate`]:
///
/// 1. **Hash-join rewrite** ([`try_hash_join_rewrite`]) when the site's
///    domain is a refined tuple whose predicate decomposes into equality
///    join conditions.  The emitted chain is itself iteration-bearing
///    (its `JoinPlan::Loop` leaves emit `Apply(true ▷ const, Iterate)`),
///    so no extra marker is added.
/// 2. **Iterate-then-restricts chain** (the [`wrap_with_iterate`]
///    fallback) — build the source by *applying* one `restrict(p)`
///    filter per refinement layer (innermost first) to a chain-head
///    `Apply(true ▷ const, Iterate)`, then compose the body onto it:
///    `(iterate ▷ (p_inner ▷ restrict) ▷ … ▷ (p_outer ▷ restrict)) ≫
///    body`.  Each `restrict` *applies* to its upstream (it is a
///    function transformer, not a composed morphism — see
///    [`make_restrict`]).  Unrefined sites get just the chain-head
///    iterate.
///
/// Hash join is the specialised strategy; the iterate-then-restricts
/// chain is the default.  Folding hash-join dispatch into the
/// iteration-site walk (rather than running it as a separate
/// top-level-only pass) automatically extends hash-join coverage to
/// every iteration site — see [`try_hash_join_rewrite`] for the full
/// list.
///
/// The pass is idempotent on already-iteration-bearing chains via
/// [`is_iteration_bearing`], which treats `Apply(_, Iterate)` at a head
/// — and, on a refined site, the outer `restrict` filter
/// `Apply(_, Apply(_, Restrict))` — plus the other iteration-
/// internalising builtins (`MapDomain`, `Uncurry`, `CollectionUnion`,
/// `Converse`, the nested `PermuteDomain` / `FlattenDomain` shapes) as
/// already providing iteration — avoiding the double-wrap that would
/// otherwise feed those `input=None` arms an unwanted upstream stream
/// (or, for a refined site, stack a second iteration source onto a
/// still-refined domain).
///
/// Op-conversion relies on this pass: the only term that creates
/// iteration without an upstream input is [`Builtin::Iterate`].  Any
/// other input-less term reaching op-conversion (after this pass) is a
/// planner bug.
fn insert_iterate_markers(expr: &mut Expr) {
    insert_iterate_recurse(expr);
    // In addition to any deeper iteration sites materialised by the
    // recursion, the program root itself may also be an iteration site.
    wrap_with_iterate(expr);
}

/// Recursively walks `expr` and materializes every iteration site that
/// op-conversion's `input=None` arms expose.
///
/// Op-conversion's combinator arms split into two groups:
///
/// - **Input-internalising** (`Sum`/`Max`/`LastOrDefault`, `Converse`,
///   `MapDomain`, `Uncurry`, `FlattenDomain`, `PermuteDomain`,
///   `CollectionUnion`, plus `Iterate` itself): these arms require
///   `input=None` and compile their argument (or each operand, in
///   `CollectionUnion`'s case) with `input=None`.  The argument is a
///   function-typed sub-expression that is iterated by the surrounding
///   tile operator, so it is an iteration site — its chain head must
///   be iteration-bearing (`Apply(_, Iterate)` in the default case; a
///   hash-join chain when the site's domain matches a join pattern).
/// - **Input-threading** (`Const`, `Zip`, `Map`, `Restrict`): these
///   accept an upstream `input` and thread it (or fan it out, in
///   `Zip`'s case) into their argument's compilation, so their
///   argument is not an iteration site.
///
/// This pass walks the AST and calls [`wrap_with_iterate`] on each
/// argument of an input-internalising arm.  `wrap_with_iterate` then
/// picks the materialisation strategy (hash join when applicable, else
/// the uniform `iterate(true) ▷ (p₁ ▷ restrict) ▷ … ▷ (pₙ ▷ restrict)`
/// source — each `restrict` applied to its upstream, not composed —
/// with the body composed onto it).  Structural recursion covers the
/// rest of the tree — every iteration site reachable from the program
/// root is reached.
fn insert_iterate_recurse(expr: &mut Expr) {
    // Special-case `Apply(Tuple|Record, Zip)`: op-conversion's `Zip` arm
    // fans the outer input out to each tuple/record field, so each field
    // is compiled with `input=Some(fan_out_branch)`.  Field wrapping
    // would still be semantically safe (the wrapped `iterate`'s
    // trivially-true predicate just passes the input through), but it
    // produces redundant operators and churns golden tests.  Recurse into
    // each field without firing the value-position `Tuple`/`Record` case
    // below.
    if let TypedExprNode::Apply { argument, function } = &mut expr.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::Zip))
    {
        match &mut argument.node {
            TypedExprNode::Tuple(elts) => {
                for elt in elts.iter_mut() {
                    insert_iterate_recurse(elt);
                }
            }
            TypedExprNode::Record(fields) => {
                for (_, field) in fields.iter_mut() {
                    insert_iterate_recurse(field);
                }
            }
            _ => insert_iterate_recurse(argument),
        }
        insert_iterate_recurse(function);
        return;
    }

    expr.walk_children_mut(insert_iterate_recurse);
    match &mut expr.node {
        // `LastOrDefault` takes `Tuple([stream, default])` — only `stream`
        // is iterated; the `default` is a scalar consumed when the stream
        // is empty.
        TypedExprNode::Apply { argument, function }
            if matches!(
                &function.node,
                TypedExprNode::Builtin(Builtin::LastOrDefault)
            ) =>
        {
            if let TypedExprNode::Tuple(elts) = &mut argument.node
                && let Some(stream) = elts.first_mut()
            {
                wrap_with_iterate(stream);
            }
        }
        // `CollectionUnion`'s function form: argument is `Tuple(ops...)`
        // and op-conversion compiles each operand with `input=None` — wrap
        // each.
        TypedExprNode::Apply { argument, function }
            if matches!(
                &function.node,
                TypedExprNode::Builtin(Builtin::CollectionUnion)
            ) =>
        {
            if let TypedExprNode::Tuple(elts) = &mut argument.node {
                for elt in elts.iter_mut() {
                    wrap_with_iterate(elt);
                }
            }
        }
        // `CollectionUnion`'s value form: each operand is compiled with
        // `input=None`.
        TypedExprNode::CollectionUnion(operands) => {
            for operand in operands.iter_mut() {
                wrap_with_iterate(operand);
            }
        }
        // The remaining input-internalising builtins all compile their
        // (single) argument with `input=None` — wrap it uniformly.
        TypedExprNode::Apply { argument, function }
            if is_internalising_builtin_function(function) =>
        {
            wrap_with_iterate(argument);
        }
        // Mutation-loop sources are iterated internally by [`Recurse`];
        // op-conversion's `Loop` arm compiles `source` with `input=None`.
        TypedExprNode::Loop { source, .. } => {
            wrap_with_iterate(source);
        }
        // Value-position `Record` literals (not the special-cased
        // `Apply(Record, Zip)` form, which `Zip`'s arm handles via fan-out):
        // op-conversion's `Record` arm compiles each field with
        // `input=None`, so every function-typed field is an iteration site.
        // The fan-out form is unaffected because `walk_children_mut`
        // visits the `Record` inside `Apply(_, Zip)` but the outer `Apply`
        // does its own input-threading there.
        TypedExprNode::Record(fields) => {
            for (_, field) in fields.iter_mut() {
                if matches!(&field.ty, Type::Fun { .. }) {
                    wrap_with_iterate(field);
                }
            }
        }
        _ => {}
    }
}

/// Returns `true` if `func` is a function position that op-conversion
/// compiles by treating its argument as an `input=None` iteration site.
///
/// Used by [`insert_iterate_recurse`] to enumerate the input-internalising
/// arms.  The actual policy lives on [`Builtin::iterates_arg`]; this
/// helper just handles the structural cases (direct builtin vs the
/// nested `PermuteDomain` / `FlattenDomain` shape).
fn is_internalising_builtin_function(func: &Expr) -> bool {
    builtin_at_function_position(func).is_some_and(Builtin::iterates_arg)
}

/// Extract the [`Builtin`] in `func`'s function position, handling both
/// the direct `Builtin(_)` form and the nested
/// `Apply { function: Builtin(_), .. }` form used by `PermuteDomain` and
/// `FlattenDomain`.
fn builtin_at_function_position(func: &Expr) -> Option<Builtin> {
    match &func.node {
        TypedExprNode::Builtin(b) => Some(*b),
        TypedExprNode::Apply {
            function: inner, ..
        } => match &inner.node {
            TypedExprNode::Builtin(b) => Some(*b),
            _ => None,
        },
        _ => None,
    }
}

/// Materialize the iteration site at `expr`, picking the best available
/// implementation strategy.
///
/// Dispatch order:
///
/// 1. `Let` is structural — recurse into the bound expression and body
///    (op-conversion's `Let` arm threads its `input=None` to both).
/// 2. If the chain at `expr` already provides iteration ([`is_iteration_bearing`]),
///    return — wrapping would either be redundant or break op-conversion.
/// 3. Try the hash-join rewrite ([`try_hash_join_rewrite`]) when `expr`'s
///    domain is a refined tuple whose predicate decomposes into equality
///    join conditions.  On success the rewrite replaces `expr` with the
///    hash-join chain (whose leaves are themselves iteration-bearing) and
///    returns.
/// 4. Otherwise fall through to the default strategy: walk every nested
///    `Type::Refinement` layer of the domain, lift each predicate, and
///    build the iteration source by *applying* one `restrict(p)` filter
///    per layer (innermost first) to a single chain-head `Apply(true ▷
///    const, Iterate)` over the unrefined base, then compose the body
///    onto it — `(iterate ▷ (p_inner ▷ restrict) ▷ … ▷ (p_outer ▷
///    restrict)) ≫ body`.  There is exactly one `iterate` (the base
///    source); the per-layer filters are `restrict`s *applied* to it, not
///    additional iterates and not morphisms composed with it (its honest
///    type makes the composed form ill-typed — see [`make_restrict`]).
///    Unrefined sites get just the chain-head iterate with a single
///    trivially-true predicate (`true ▷ const`) so op-conversion still
///    sees an explicit iteration marker; the trivially-true form is
///    recognised by op-conversion and compiles to a bare `IterateExtent`
///    with no filter tile.
///
/// The hash-join branch and the default branch are *both* materialising
/// the same iteration site — hash join is just the specialised strategy
/// when the type structure permits.  In both cases the result is a chain
/// whose head provides iteration, so the surrounding op-conversion arm
/// can compile its argument with `input=None` without erroring.
fn wrap_with_iterate(expr: &mut Expr) {
    // `Let` nodes pass input through to both children — op-conversion's
    // `Let` arm threads its `input` into bound_expr and body.  At a
    // top-level Let (the only context that calls into this function with
    // a Let), both children are at `input=None` positions, so recurse
    // into them rather than prepending iterate to the Let itself.  This
    // arm runs before [`is_iteration_bearing`]'s early-return below
    // because Let isn't recognised as iteration-bearing on its own.
    //
    // No matching `Record` arm here: [`insert_iterate_recurse`]'s value-
    // position `Record` case already wraps function-typed fields wherever
    // a Record appears in the AST (top-level, Let-bound, Apply-arg-of-
    // catch-all), so a redundant descent here would just re-visit
    // already-iterate-led fields.
    if let TypedExprNode::Let {
        bound_expr, body, ..
    } = &mut expr.node
    {
        // Every function-typed bound expr is made iteration-bearing,
        // whether or not `body` uses it: op-conversion's `Let` arm
        // compiles `bound_expr` unconditionally, so an unused,
        // non-iteration-bearing function-typed binding would otherwise
        // hit an `input=None` arm and error.  This wrap is the workaround
        // for that eager compilation — #232 tracks making iteration
        // use-driven so a dead binding is dropped rather than wrapped.
        if matches!(&bound_expr.ty, Type::Fun { .. }) {
            wrap_with_iterate(bound_expr);
        }
        wrap_with_iterate(body);
        return;
    }
    if is_iteration_bearing(expr) {
        return;
    }
    let Some(domain_ty) = expr.ty.domain() else {
        // Non-function expressions can't be iterated; leave them alone.
        return;
    };
    // Specialised iteration strategies come first: try the hash/loop-join
    // rewrite when the domain is a refined tuple whose **pointful** predicate
    // decomposes into equality join conditions (design §6.5 — the recognizer
    // matches the lambda form directly). Both this and the default
    // `iterate(predicate)` fall-through are choosing how to materialise the same
    // iteration site — hash join is just a more efficient strategy when the type
    // structure permits.
    if try_hash_join_rewrite(expr, &domain_ty) {
        return;
    }
    // Generic fallback. Now compile the site's refinement predicates (design
    // §6.5: "run the lambda-elim → simplify sub-pipeline on the lifted predicate
    // when a refined type is iterated") so the iterate/restrict lowering below
    // consumes point-free predicates. (Group-by and join sites matched the
    // pointful form and were already rewritten.)
    //
    // NOT YET HANDLED here: §6.5's binder-*lifting* for the loop-join fallback —
    // hoisting an enclosing `Fun`-binder that is *not* in scope at the iteration
    // site into the predicate's parameter list (matrix case F: a returned filter
    // capting an outer binder, iterated outside that binder's scope). The
    // recognized shapes (group-by, hash/loop join, in-scope filters: matrix
    // cases A–E, G, H) are covered and tested; case F has no lowering that
    // reaches it today and is deferred with the opaque/polymorphic
    // dependent-function work (proposal O3). A predicate that *did* reach here
    // with a free outer binder would surface as a surviving free var, not a
    // silent miscompile.
    //
    // The `memo` dedups predicates *within* this site's subtree (a predicate
    // `Rc` shared across positions is compiled once, all occurrences re-pointed
    // at the same rebuild). It is fresh per site, so a predicate reachable from
    // two sibling sites may be compiled again; that is safe because
    // `lambda_elim::run` is idempotent on an already-point-free predicate
    // (re-running finds no lambdas to eliminate).
    compile_refinement_predicates(expr, &mut PredMemo::new());
    let Some(domain_ty) = expr.ty.domain() else {
        return;
    };
    // Walk every nested `Type::Refinement` layer (innermost ⊇ outermost,
    // each layer's predicate must hold), collecting the predicates
    // outer-to-inner; reverse to inner-to-outer.  Then emit a uniform
    // chain: one chain-head `iterate(true)` over the unrefined base
    // (op-conversion's `IterateExtent`), followed by one
    // `restrict(p_inner)`, `restrict(p_next)`, … per refinement layer,
    // narrowing the domain layer by layer.  Unrefined sites get just
    // the iterate.
    // Recover each layer's point-free predicate function from its bare
    // `__elem ▷ p` form — that is what `make_restrict` filters with (the
    // refinement type it then re-stamps stays bare).
    let mut preds: Vec<Expr> = Vec::new();
    let mut current = &domain_ty;
    while let Type::Refinement(base, refinement) = current {
        preds.push(fn_of_bare_predicate(base.as_ref(), &refinement.predicate));
        current = base.as_ref();
    }
    preds.reverse();
    let body = take(expr);
    // Build the iteration source by applying one `restrict(p)` per
    // refinement layer (innermost first) to a chain-head `iterate(true)`
    // over the unrefined base.  Each `restrict` is a function transformer
    // *applied* to its upstream (not composed): `make_restrict` narrows
    // the domain layer by layer while preserving the codomain, so `source`
    // ends with type `{{…{D | p_inner} …} | p_outer} ⇒ D` — the full
    // refinement on the domain.  The value-producing `body` is then
    // composed onto that source as a genuine CCC morphism.
    let site_ty = body.ty.clone();
    let source = preds.into_iter().fold(
        make_iterate(trivially_true_predicate(current.clone())),
        |upstream, pred| make_restrict(pred, upstream),
    );
    // An iteration source produces the refined extent it iterates, so its
    // codomain is the *site's* refined domain `{D | p}`, mirroring
    // `make_iterate`'s `{D | p} ⇒ {D | p}` symmetry. Surfacing the refinement
    // on the codomain lets the value-producing `body` — which `cast`s each
    // element to the refined element type — compose against a producer that
    // *already* carries `{D | p}`, rather than acquiring it from a bare
    // codomain (`make_restrict` refines only the domain). We use `domain_ty`
    // rather than the built source's domain because `make_restrict` drops a
    // *trivially-true* layer (`if True`): the source then iterates a bare base,
    // but the body's cast still demands the site's `{D | true}`, so the
    // codomain must reflect the site domain to match it. Unrefined sites keep a
    // bare `D ⇒ D`.
    let source = if matches!(domain_ty, Type::Refinement(..)) {
        set_codomain(source, domain_ty.clone())
    } else {
        source
    };
    let mut elts: Vec<Expr> = vec![source];
    match body.node {
        TypedExprNode::Compose(existing) => {
            elts.extend(existing);
        }
        _ => elts.push(body),
    }
    // The override is now redundant — `source`'s domain already carries
    // the full refinement structure, so `typed_compose` derives the
    // correct `{…} ⇒ T`.  Keep it as a defensive pin on the site's own
    // type: predicates are immutable terms, so the layers `make_restrict`
    // re-mints (each rebuilt as a fresh `Rc`) compare equal structurally,
    // and nothing downstream depends on which term instance the codomain
    // holds.
    *expr = typed_compose(elts).with_ty(site_ty);
}

/// Returns `true` if `expr` (or the first element of `expr` if it's a
/// `Compose`) already provides iteration — i.e. wrapping it with
/// `iterate` would either be redundant or break op-conversion.
///
/// The check covers three groups:
///
/// 1. Already iterate-led: `Apply(_, Iterate)` at head — or
///    `restrict`-led, `Apply(_, Apply(_, Restrict))` at head.  A
///    `restrict` application always sits on an iteration source by
///    construction ([`make_restrict`] only ever wraps an
///    iteration-bearing upstream), so a refined site whose head is the
///    outermost `restrict` filter is iteration-bearing just as its
///    unrefined `iterate`-led counterpart is.
/// 2. Self-iterating builtins ([`Builtin::iterates_arg`]): the
///    iteration-internalising group — `MapDomain`, `Uncurry`,
///    `Converse`, `CollectionUnion`, plus the nested `PermuteDomain` /
///    `FlattenDomain` shapes.  (Sum / Max / LastOrDefault are also in
///    `iterates_arg`, but they produce scalars; [`wrap_with_iterate`]'s
///    `expr.ty.domain()` check filters them out independently.)  Plus
///    the catch-all `Apply` with a non-builtin function (`Proj`, `Var`,
///    curried `Apply`, …) — op-conversion's catch-all arm rejects
///    `input=Some`.  Plus value-position `Tuple` / `Record` literals
///    (also reject `input=Some`).
/// 3. Function-typed `Var` references — op-conversion's `Var` arm
///    returns its bound op directly under `input=None`, and that bound
///    op was itself iterate-wrapped at its let-bind site.
fn is_iteration_bearing(expr: &Expr) -> bool {
    let head = match &expr.node {
        TypedExprNode::Compose(elts) if !elts.is_empty() => &elts[0],
        _ => expr,
    };
    match &head.node {
        TypedExprNode::CollectionUnion(_) | TypedExprNode::Tuple(_) | TypedExprNode::Record(_) => {
            true
        }
        TypedExprNode::Var(_) if matches!(&head.ty, Type::Fun { .. }) => true,
        TypedExprNode::Apply { function, .. } => match builtin_at_function_position(function) {
            // `Iterate` is the canonical head marker; `Restrict` heads a
            // refined site whose upstream is itself iteration-bearing
            // (`make_restrict` only wraps an iteration source), so a
            // restrict-led chain must be recognised too — otherwise
            // re-running the marker pass would double-wrap refined sites.
            Some(b) => matches!(b, Builtin::Iterate | Builtin::Restrict) || b.iterates_arg(),
            // Non-builtin function position (`Proj`, `Var`, curried
            // `Apply`, …): op-conversion's catch-all `Apply` arm
            // rejects `input=Some`, so wrapping would break compilation.
            None => true,
        },
        _ => false,
    }
}

/// Recognize group-by sites and rewrite them to the bucketize chain.
///
/// Group-by lowers to the dependent-refinement source `const(cast(c)) :
/// (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)`; [`convert_groupby_pointful`] matches
/// that **pointful** form (design §6.5) and rewrites it to
/// `converse(c ≫ key) ≫ map(c)`. Walks the tree, rewriting every such site
/// (a rewritten site's tail may contain further sites).
fn recognize_groupby_sites(expr: &mut Expr) {
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

/// Is `e` a bare `Var` other than the element binder (the free key binder)?
fn is_free_var(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Var(n) if !n.is_elem())
}

// Returns whether the given expression is a constant, or a function of a constant.
fn is_constant(expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::Const) => true,
        TypedExprNode::Compose(elts) => elts.first().is_some_and(is_constant),
        _ => false,
    }
}

// Replaces the domain type of a constant expression with a new domain type.
// Requires `is_constant(expr)` to be true.
fn replace_constant_domain_type(expr: &mut Expr, ty: &Type) {
    set_domain_ty(&mut expr.ty, ty);
    match &mut expr.node {
        TypedExprNode::Apply { .. } => {
            let output_ty = expr.ty.clone();
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert!(is_builtin(function, Builtin::Const));
                argument.clone()
            } else {
                unreachable!()
            };

            *expr = apply_primitive(*arg, Builtin::Const, output_ty)
        }
        TypedExprNode::Compose(elts) => {
            if let Some(e) = elts.first_mut() {
                replace_constant_domain_type(e, ty);
            }
        }
        _ => unreachable!(),
    };
}

// Returns whether the given expression relies only on a single arm of its input tuple type,
// and returns the index of that arm if so.
fn is_function_of_single_tuple_arm(expr: &Expr) -> Option<usize> {
    match &expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => Some(*i),
        TypedExprNode::Compose(elts) => elts.first().and_then(is_function_of_single_tuple_arm),
        TypedExprNode::Apply { function, argument } if is_builtin(function, Builtin::Zip) => {
            is_function_of_single_tuple_arm(argument)
        }
        TypedExprNode::Tuple(elts) => {
            let mut result = None;
            for elt in elts.iter() {
                if is_constant(elt) {
                    continue;
                }
                if let Some(idx) = is_function_of_single_tuple_arm(elt) {
                    if result.is_some_and(|x| x != idx) {
                        return None;
                    }
                    result = Some(idx);
                } else {
                    return None;
                }
            }
            result
        }
        _ => None,
    }
}

fn set_domain_ty(fun_ty: &mut Type, ty: &Type) {
    match fun_ty {
        Type::Fun {
            domain,
            codomain: _,
            ..
        } => {
            **domain = ty.clone();
        }
        _ => panic!("Not function type: {}", fun_ty),
    }
}

// Converts an expression that only reads a single arm of its input
// (as determined by is_function_of_single_tuple_arm) to a function
// of just that arm.
fn replace_tuple_project_with_id(expr: &mut Expr, ty: &Type) {
    match &mut expr.node {
        TypedExprNode::Proj(ProjKey::Index(_)) => {
            *expr = id().with_ty(Type::fun(ty.clone(), ty.clone()))
        }
        TypedExprNode::Compose(_) => {
            set_domain_ty(&mut expr.ty, ty);
            if let TypedExprNode::Compose(elts) = &mut expr.node
                && let Some(first) = elts.first_mut()
            {
                replace_tuple_project_with_id(first, ty);
            }
        }
        TypedExprNode::Apply { .. } => {
            let mut output_ty = expr.ty.clone();
            set_domain_ty(&mut output_ty, ty);
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert!(is_builtin(function, Builtin::Zip));
                replace_tuple_project_with_id(argument, ty);
                argument.clone()
            } else {
                unreachable!()
            };
            *expr = apply_primitive(*arg, Builtin::Zip, output_ty);
        }
        TypedExprNode::Tuple(_) => {
            if let Type::Tuple(elts) = &mut expr.ty {
                elts.iter_mut().for_each(|elt| match elt {
                    Type::Fun {
                        domain,
                        codomain: _,
                        ..
                    } => {
                        **domain = ty.clone();
                    }
                    _ => panic!(),
                });
            }
            if let TypedExprNode::Tuple(elts) = &mut expr.node {
                for elt in elts.iter_mut() {
                    if is_constant(elt) {
                        replace_constant_domain_type(elt, ty);
                    } else {
                        replace_tuple_project_with_id(elt, ty);
                    }
                }
            }
        }
        _ => {}
    };
}

/// Splits a (pointful) join predicate into equality join conditions and
/// residual predicates, each compiled to a point-free morphism over the tuple
/// domain (design §6.5).
///
/// The predicate is **bare** — the refinement binds the implicit
/// REFINEMENT_BINDER as the record `rec`, of type `rec_ty` — and has the shape
/// `rec.0 ▷ l0 ▷ (λ v0 → … rec.k ▷ lk ▷ (λ vk → <bool over v0…vk>))`:
/// each `rec.i ▷ li` binds the element `vi` of arm `i`, and the innermost
/// boolean is a conjunction of `==` conditions and residual predicates over
/// those element binders. We build the `vi ↦ rec.i ▷ li` environment,
/// decompose the boolean (`and` / `==` / other), and for each side substitute
/// the environment and lambda-eliminate `λ rec → side` to recover the
/// combinator morphism over `rec` that [`plan_loop_join`] consumes.
fn split_join_conditions(refinement: &Expr, rec_ty: &Type) -> (Vec<(Expr, Expr)>, Vec<Expr>) {
    let mut eq_conds = Vec::new();
    let mut other_preds = Vec::new();
    // A bare predicate is `Bool`-typed; a function-typed expression here is not a
    // decomposable join predicate, so treat the whole thing as one residual (no
    // join forms — plan_loop_join then bails on the empty equality set).
    if refinement.ty.domain().is_some() {
        other_preds.push(refinement.clone());
        return (eq_conds, other_preds);
    }
    // env: element binder name → its extraction morphism `rec.i ▷ li` (over rec).
    let mut env: Vec<(Name, Expr)> = Vec::new();
    let mut cur = refinement;
    while let TypedExprNode::Apply { argument, function } = &cur.node
        && let TypedExprNode::Lambda {
            param, body: inner, ..
        } = &function.node
    {
        env.push((param.name.clone(), (**argument).clone()));
        cur = inner.as_ref();
    }
    decompose_join_bool(
        cur,
        &env,
        &Name::elem(),
        rec_ty,
        &mut eq_conds,
        &mut other_preds,
    );
    (eq_conds, other_preds)
}

/// Decompose the innermost boolean of a join predicate into equality conditions
/// (`==`, recorded as a pair of compiled sides) and residual predicates,
/// splitting top-level conjunctions.
fn decompose_join_bool(
    e: &Expr,
    env: &[(Name, Expr)],
    rec_name: &Name,
    rec_ty: &Type,
    eq_conds: &mut Vec<(Expr, Expr)>,
    other_preds: &mut Vec<Expr>,
) {
    match &e.node {
        TypedExprNode::BinOp {
            left,
            op: BinOpKind::BoolLogic(LogicKind::And),
            right,
        } => {
            decompose_join_bool(left, env, rec_name, rec_ty, eq_conds, other_preds);
            decompose_join_bool(right, env, rec_name, rec_ty, eq_conds, other_preds);
        }
        TypedExprNode::BinOp {
            left,
            op: BinOpKind::Compare(CompareKind::Equals),
            right,
        } => {
            let ka = compile_join_side(left, env, rec_name, rec_ty);
            let kb = compile_join_side(right, env, rec_name, rec_ty);
            eq_conds.push((ka, kb));
        }
        _ => other_preds.push(compile_join_side(e, env, rec_name, rec_ty)),
    }
}

/// Substitute the element-binder environment into `side` (an expression over
/// the element binders) and lambda-eliminate `λ rec → side` to the point-free
/// morphism over the tuple domain.
fn compile_join_side(side: &Expr, env: &[(Name, Expr)], rec_name: &Name, rec_ty: &Type) -> Expr {
    let mut body = side.clone();
    for (var, morph) in env {
        body = lambda_elim::substitute(body, var, morph);
    }
    let side_ty = body.ty.clone();
    let lam =
        Expr::lambda(rec_name, rec_ty.clone(), body).with_ty(Type::fun(rec_ty.clone(), side_ty));
    lambda_elim::run(lam).expect("lambda-elim of join-condition side")
}

/// Collects the original arm indices accessed by `expr` at domain-accessing positions.
///
/// Follows the same structural rules as [`is_function_of_single_tuple_arm`] but collects
/// all arm indices rather than requiring exactly one.
fn collect_arms_used(expr: &Expr, result: &mut BTreeSet<usize>) {
    match &expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => {
            result.insert(*i);
        }
        TypedExprNode::Compose(elts) => {
            if let Some(first) = elts.first() {
                collect_arms_used(first, result);
            }
        }
        TypedExprNode::Apply { function, argument } if is_builtin(function, Builtin::Zip) => {
            collect_arms_used(argument, result);
        }
        TypedExprNode::Tuple(elts) => {
            for elt in elts {
                if !is_constant(elt) {
                    collect_arms_used(elt, result);
                }
            }
        }
        _ => {}
    }
}

/// Rewrites domain-accessing Proj nodes in a predicate to match a new flat domain ordering.
///
/// `arm_order[j]` is the original arm index at position `j` in the new flat domain.
/// Only rewrites positions that access the tuple domain (Proj at the start of Compose chains,
/// arguments of `zip` applications, elements of domain-valued Tuples).  Domain types throughout
/// the expression are updated to `new_domain_ty`; codomains are left unchanged.
///
/// Mirrors the structural traversal of [`replace_tuple_project_with_id`].
fn reindex_for_domain(expr: &mut Expr, new_domain_ty: &Type, arm_order: &[usize]) {
    // Constant expressions ignore their domain; just update the type.
    if is_constant(expr) {
        replace_constant_domain_type(expr, new_domain_ty);
        return;
    }
    match &mut expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => {
            *i = arm_order
                .iter()
                .position(|&a| a == *i)
                .expect("arm index not in arm_order");
            set_domain_ty(&mut expr.ty, new_domain_ty);
        }
        TypedExprNode::Compose(_) => {
            set_domain_ty(&mut expr.ty, new_domain_ty);
            if let TypedExprNode::Compose(elts) = &mut expr.node
                && let Some(first) = elts.first_mut()
            {
                reindex_for_domain(first, new_domain_ty, arm_order);
            }
        }
        TypedExprNode::Apply { .. } => {
            // Only zip applications appear at domain-accessing positions.
            let mut output_ty = expr.ty.clone();
            set_domain_ty(&mut output_ty, new_domain_ty);
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert!(
                    is_builtin(function, Builtin::Zip),
                    "unexpected Apply at domain position: {:?}",
                    function.node
                );
                reindex_for_domain(argument, new_domain_ty, arm_order);
                argument.clone()
            } else {
                unreachable!()
            };
            *expr = apply_primitive(*arg, Builtin::Zip, output_ty);
        }
        TypedExprNode::Tuple(_) => {
            if let Type::Tuple(tys) = &mut expr.ty {
                for ty in tys.iter_mut() {
                    if matches!(ty, Type::Fun { .. }) {
                        set_domain_ty(ty, new_domain_ty);
                    }
                }
            }
            if let TypedExprNode::Tuple(elts) = &mut expr.node {
                for elt in elts.iter_mut() {
                    if is_constant(elt) {
                        replace_constant_domain_type(elt, new_domain_ty);
                    } else {
                        reindex_for_domain(elt, new_domain_ty, arm_order);
                    }
                }
            }
        }
        _ => {
            if matches!(expr.ty, Type::Fun { .. }) {
                set_domain_ty(&mut expr.ty, new_domain_ty);
            }
        }
    }
}

/// Combines two optional predicates over the same flat domain with a logical AND.
fn combine_predicates(a: Option<Expr>, b: Option<Expr>) -> Option<Expr> {
    match (a, b) {
        (None, None) => None,
        (Some(p), None) | (None, Some(p)) => Some(p),
        (Some(pa), Some(pb)) => {
            let flat_domain_ty = pa.ty.domain().unwrap().clone();
            let bool_ty = Type::Base(BaseType::Bool);
            let zip_input_ty = Type::Tuple(vec![pa.ty.clone(), pb.ty.clone()]);
            let zip_out_ty = Type::fun(
                flat_domain_ty.clone(),
                Type::Tuple(vec![bool_ty.clone(), bool_ty.clone()]),
            );
            let preds_tuple = Expr::tuple(vec![pa, pb]).with_ty(zip_input_ty);
            let zipped = apply_function(preds_tuple, Expr::builtin(Builtin::Zip), zip_out_ty);
            Some(typed_compose(vec![
                zipped,
                Expr::builtin(Builtin::BinOp(BinOpKind::BoolLogic(LogicKind::And))).with_ty(
                    Type::fun(Type::Tuple(vec![bool_ty.clone(), bool_ty.clone()]), bool_ty),
                ),
            ]))
        }
    }
}

/// Runs a BFS over the join condition graph and returns the spanning-tree children list.
///
/// `conditions` is a list of `(arm_a, arm_b, key_expr_a, key_expr_b)` tuples representing
/// undirected edges between arms.  `n` is the total number of arms (nodes in the graph).
///
/// The returned `Vec` has one slot per arm; `result[i]` lists the BFS children of arm `i`
/// in discovery order.  Returns `None` if the graph is disconnected (not all `n` arms are
/// reachable from arm 0).
fn spanning_tree_children(
    conditions: &[(usize, usize, Expr, Expr)],
    n: usize,
) -> Option<Vec<Vec<usize>>> {
    if n == 0 {
        return None;
    }
    let mut visited = vec![false; n];
    let mut children: Vec<Vec<usize>> = vec![vec![]; n];
    let mut queue = VecDeque::new();
    visited[0] = true;
    queue.push_back(0);
    while let Some(node) = queue.pop_front() {
        for &(a, b, _, _) in conditions.iter() {
            let neighbor = if a == node && !visited[b] {
                Some(b)
            } else if b == node && !visited[a] {
                Some(a)
            } else {
                None
            };
            if let Some(nbr) = neighbor {
                visited[nbr] = true;
                children[node].push(nbr);
                queue.push_back(nbr);
            }
        }
    }
    visited.iter().all(|&v| v).then_some(children)
}

/// A tree of joins.  Hash joins are two-way joins with an equality predicate between the two sides,
/// and loop joins are iteration of a tuple of inputs, along with a predicate over those inputs.
/// The leafs of the tree are always Loop joins (ideally the trivial case containing a single input).
#[allow(clippy::large_enum_variant)]
enum JoinPlan {
    Loop {
        /// Which of the original input arms need to be iterated
        arms: Vec<usize>,
        /// Optionally, a predicate to apply after iteration.
        /// The predicate must only rely on the arms present in the loop join.
        predicate: Option<Expr>,
    },
    Hash {
        /// Build side of the join.  May itself be the output of another join.
        build: Box<JoinPlan>,
        /// Probe side of the join.  May itself be the output of another join.
        probe: Box<JoinPlan>,
        /// Index of the build-side key in the type of the build side.  This does not correspond
        /// directly with the indices in the original, unplanned tuple type.
        build_key_idx: Option<usize>,
        /// Expression which is a function from domain type to key type for the build side. This
        /// does not contain the projection to extract the domain value from the input tuple type;
        /// that needs to be constructed as part of translating the join plan to CCL.
        build_key_expr: Expr,
        /// Index of the probe-side key in the type of the probe side.  This does not correspond
        /// directly with the indices in the original, unplanned tuple type.
        probe_key_idx: Option<usize>,
        /// Expression which is a function from domain type to key type for the probe side. This
        /// does not contain the projection to extract the domain value from the input tuple type;
        /// that needs to be constructed as part of translating the join plan to CCL.
        probe_key_expr: Expr,
        /// Additional, non-hash-join, predicate to apply to the result of the join.
        predicate: Option<Expr>,
    },
}

impl Debug for JoinPlan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            JoinPlan::Loop { arms, predicate } => f
                .debug_struct("Loop")
                .field("arms", arms)
                .field(
                    "predicate",
                    &predicate.as_ref().map(symbolic).unwrap_or("None".into()),
                )
                .finish(),
            JoinPlan::Hash {
                build,
                probe,
                build_key_idx,
                build_key_expr,
                probe_key_idx,
                probe_key_expr,
                predicate,
            } => f
                .debug_struct("Hash")
                .field("build", build)
                .field("probe", probe)
                .field("build_key_idx", build_key_idx)
                .field("build_key_expr", &symbolic(build_key_expr))
                .field("probe_key_idx", probe_key_idx)
                .field("probe_key_expr", &symbolic(probe_key_expr))
                .field(
                    "predicate",
                    &predicate.as_ref().map(symbolic).unwrap_or("None".into()),
                )
                .finish(),
        }
    }
}

/// Returns all arm indices in the BFS subtree rooted at `node`, in pre-order.
///
/// `children[i]` is the list of direct children of arm `i` in the spanning tree (as
/// produced by [`spanning_tree_children`]).
fn subtree_arms(node: usize, children: &[Vec<usize>]) -> Vec<usize> {
    let mut arms = vec![node];
    for &child in &children[node] {
        arms.extend(subtree_arms(child, children));
    }
    arms
}

/// Builds a residual predicate expression from extra (non-spanning-tree) join conditions.
///
/// `extra` is a slice of `(arm_a, arm_b, key_a, key_b)` conditions that were not used as
/// hash-join keys.  `arm_order[i]` gives the canonical arm index at flat-domain position `i`;
/// it is used to compute the tuple projections.  `arm_types` provides the type of each arm.
///
/// Each condition becomes an equality check `(proj_a ≫ key_a, proj_b ≫ key_b) ▷ zip ≫ eq`
/// over the flat domain tuple; multiple conditions are combined with `and`.
fn build_residual_predicate(
    extra: &[&(usize, usize, Expr, Expr)],
    arm_order: &[usize],
    arm_types: &[Type],
) -> Option<Expr> {
    if extra.is_empty() {
        return None;
    }

    let flat_domain_ty = Type::Tuple(arm_order.iter().map(|&i| arm_types[i].clone()).collect());
    let bool_ty = Type::Base(BaseType::Bool);

    let preds: Vec<Expr> = extra
        .iter()
        .map(|(arm_a, arm_b, key_a, key_b)| {
            let pos_a = arm_order.iter().position(|&a| a == *arm_a).unwrap();
            let pos_b = arm_order.iter().position(|&a| a == *arm_b).unwrap();

            let arm_ty_a = key_a.ty.domain().unwrap().clone();
            let arm_ty_b = key_b.ty.domain().unwrap().clone();
            let key_ty = key_a.ty.codomain().unwrap().clone();

            let proj_a =
                Expr::proj_index(pos_a).with_ty(Type::fun(flat_domain_ty.clone(), arm_ty_a));
            let lhs = typed_compose(vec![proj_a, key_a.clone()]);

            let proj_b =
                Expr::proj_index(pos_b).with_ty(Type::fun(flat_domain_ty.clone(), arm_ty_b));
            let rhs = typed_compose(vec![proj_b, key_b.clone()]);

            // (lhs, rhs) ▷ zip ≫ eq : flat_domain_ty → Bool
            let zip_input_ty = Type::Tuple(vec![
                Type::fun(flat_domain_ty.clone(), key_ty.clone()),
                Type::fun(flat_domain_ty.clone(), key_ty.clone()),
            ]);
            let zip_out_ty = Type::fun(
                flat_domain_ty.clone(),
                Type::Tuple(vec![key_ty.clone(), key_ty.clone()]),
            );
            let zip_args = Expr::tuple(vec![lhs, rhs]).with_ty(zip_input_ty);
            let zipped = apply_function(zip_args, Expr::builtin(Builtin::Zip), zip_out_ty);

            typed_compose(vec![
                zipped,
                Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals))).with_ty(
                    Type::fun(Type::Tuple(vec![key_ty.clone(), key_ty]), bool_ty.clone()),
                ),
            ])
        })
        .collect();

    if preds.len() == 1 {
        preds.into_iter().next()
    } else {
        // (pred_1, ..., pred_n) ▷ zip ≫ and : flat_domain_ty → Bool
        let n = preds.len();
        let preds_tuple_ty = Type::Tuple(
            (0..n)
                .map(|_| Type::fun(flat_domain_ty.clone(), bool_ty.clone()))
                .collect(),
        );
        let zip_out_ty = Type::fun(
            flat_domain_ty.clone(),
            Type::Tuple((0..n).map(|_| bool_ty.clone()).collect()),
        );
        let preds_tuple = Expr::tuple(preds).with_ty(preds_tuple_ty);
        let zipped = apply_function(preds_tuple, Expr::builtin(Builtin::Zip), zip_out_ty);
        let bool_tuple_ty = Type::Tuple((0..n).map(|_| bool_ty.clone()).collect());
        Some(typed_compose(vec![
            zipped,
            Expr::builtin(Builtin::BinOp(BinOpKind::BoolLogic(LogicKind::And)))
                .with_ty(Type::fun(bool_tuple_ty, bool_ty)),
        ]))
    }
}

/// Recursively builds a [`JoinPlan`] from a BFS spanning-tree, rooted at `node`.
///
/// `children[i]` lists the direct children of arm `i` in the spanning tree (see
/// [`spanning_tree_children`]).  `conditions` is the full list of equality conditions
/// `(arm_a, arm_b, key_expr_a, key_expr_b)`.  `arm_types[i]` is the type of arm `i`.
///
/// Starting from `node`, each of its BFS children is joined onto the accumulated
/// probe side in order, producing a left-deep sequence of hash joins.  For each
/// child, ALL conditions straddling the current probe side and the child's subtree
/// are identified: the first drives the hash join key, and any remaining ones become
/// a residual predicate applied at this node.
///
/// `other_predicates` contains non-equality predicates (as original-domain expressions paired
/// with their required arm sets) that should be pushed to the lowest join node where all
/// required arms are present.  Predicates entirely within a child subtree are forwarded to
/// that child's recursive call; predicates that straddle or depend on the current probe side
/// are applied at the first hash join where all their arms are available.
///
/// Returns `(plan, arm_order)` where `arm_order[i]` is the canonical arm index at output
/// position `i` of the plan's domain tuple, or `None` if any required condition is missing.
fn build_join_plan(
    node: usize,
    children: &[Vec<usize>],
    conditions: &[(usize, usize, Expr, Expr)],
    arm_types: &[Type],
    other_predicates: &[(Expr, BTreeSet<usize>)],
) -> Option<(JoinPlan, Vec<usize>)> {
    let mut probe_plan = JoinPlan::Loop {
        arms: vec![node],
        predicate: None,
    };
    let mut probe_arms = vec![node];
    let mut remaining_preds: Vec<(Expr, BTreeSet<usize>)> = other_predicates.to_vec();

    // Build a left-deep sequence of hash joins: for each BFS child, hash-join its subtree
    // (build side) onto the accumulated probe side.  The first straddling condition drives
    // the hash key; any remaining ones become a residual predicate at this node.
    for &child in &children[node] {
        let build_arms = subtree_arms(child, children);

        // Predicates whose required arms are entirely within the child subtree are pushed
        // into the child's plan.  Constant predicates (empty arms_used) are kept at the
        // current level so they can be applied once a flat domain exists.
        let mut child_preds: Vec<(Expr, BTreeSet<usize>)> = Vec::new();
        remaining_preds.retain(|(pred, arms_used)| {
            if !arms_used.is_empty() && arms_used.iter().all(|a| build_arms.contains(a)) {
                child_preds.push((pred.clone(), arms_used.clone()));
                false
            } else {
                true
            }
        });

        let (build_plan, _) =
            build_join_plan(child, children, conditions, arm_types, &child_preds)?;

        // Collect all conditions straddling the current probe side and the child's subtree.
        let straddling: Vec<&(usize, usize, Expr, Expr)> = conditions
            .iter()
            .filter(|(a, b, _, _)| {
                (probe_arms.contains(a) && build_arms.contains(b))
                    || (probe_arms.contains(b) && build_arms.contains(a))
            })
            .collect();

        // The first straddling condition drives the hash join key.
        let (arm_a, arm_b, key_a, key_b) = *straddling.first()?;

        // Orient so that probe_arm is on the probe side.
        let (probe_arm, build_arm, probe_key_expr, build_key_expr) = if probe_arms.contains(arm_a) {
            (*arm_a, *arm_b, key_a.clone(), key_b.clone())
        } else {
            (*arm_b, *arm_a, key_b.clone(), key_a.clone())
        };

        let probe_key_idx = probe_arms.iter().position(|&a| a == probe_arm)?;
        let build_key_idx = build_arms.iter().position(|&a| a == build_arm)?;

        let probe_len_before = probe_arms.len();
        let build_len = build_arms.len();

        // Extend probe_arms to the combined arm order before building the predicate,
        // so that projections reference the correct positions in the flat domain.
        probe_arms.extend(build_arms.iter().copied());

        // Residual equality conditions beyond the first straddling one.
        let mut predicate = build_residual_predicate(&straddling[1..], &probe_arms, arm_types);

        // Apply any other predicates now that all their required arms are available.
        // Build the flat domain type lazily — only when there are other predicates to adapt.
        let applicable: Vec<Expr> = if remaining_preds.is_empty() {
            Vec::new()
        } else {
            let flat_domain_ty =
                Type::Tuple(probe_arms.iter().map(|&i| arm_types[i].clone()).collect());
            let mut app = Vec::new();
            remaining_preds.retain(|(pred, arms_used)| {
                if arms_used.iter().all(|a| probe_arms.contains(a)) {
                    let mut adapted = pred.clone();
                    reindex_for_domain(&mut adapted, &flat_domain_ty, &probe_arms);
                    app.push(adapted);
                    false
                } else {
                    true
                }
            });
            app
        };
        for adapted in applicable {
            predicate = combine_predicates(predicate, Some(adapted));
        }

        probe_plan = JoinPlan::Hash {
            probe: Box::new(probe_plan),
            build: Box::new(build_plan),
            probe_key_idx: if probe_len_before == 1 {
                None
            } else {
                Some(probe_key_idx)
            },
            probe_key_expr,
            build_key_idx: if build_len == 1 {
                None
            } else {
                Some(build_key_idx)
            },
            build_key_expr,
            predicate,
        };
    }

    // For leaf nodes (no children were joined), remaining predicates whose arms are all within
    // the current probe set can be applied directly to the loop plan's predicate field.  This
    // covers the case where a predicate depends only on a single arm (e.g. `y < 2` for an arm
    // `y`), and that arm is itself a leaf with no children to push it into.
    if !remaining_preds.is_empty() {
        let leaf_ty = arm_types[probe_arms[0]].clone();
        let mut leaf_pred: Option<Expr> = None;
        remaining_preds.retain(|(pred, arms_used)| {
            if arms_used.iter().all(|a| probe_arms.contains(a)) {
                let mut adapted = pred.clone();
                replace_tuple_project_with_id(&mut adapted, &leaf_ty);
                leaf_pred = combine_predicates(leaf_pred.take(), Some(adapted));
                false
            } else {
                true
            }
        });
        if let Some(p) = leaf_pred
            && let JoinPlan::Loop { predicate, .. } = &mut probe_plan
        {
            *predicate = combine_predicates(predicate.take(), Some(p));
        }
    }

    assert!(
        remaining_preds.is_empty(),
        "other predicates not placed: {:?}",
        remaining_preds
            .iter()
            .map(|(p, _)| symbolic(p))
            .collect::<Vec<_>>()
    );

    Some((probe_plan, probe_arms))
}

/// Analyzes a loop-join refinement and returns a [`JoinPlan`] if it can be converted to
/// hash joins, or `None` otherwise.
///
/// `arm_types` is the ordered list of types for each arm of the loop join (length ≥ 2).
/// `refinement` is the join predicate over the n-tuple domain; it must decompose into
/// single-arm equality conditions (see [`collect_join_conditions`]).  Returns `None` if the
/// condition graph is disconnected or any condition spans more than one arm per side.
fn plan_loop_join(arm_types: &[Type], refinement: &Expr) -> Option<(JoinPlan, Vec<usize>)> {
    let n = arm_types.len();
    if n < 2 {
        trace!("plan_loop_join: tuple has {} elements, need at least 2", n);
        return None;
    }

    let (eq_conditions_raw, other_preds_raw) =
        split_join_conditions(refinement, &Type::Tuple(arm_types.to_vec()));

    if eq_conditions_raw.is_empty() {
        trace!("plan_loop_join: no equality conditions, cannot build hash join");
        return None;
    }

    // For each equality condition, determine which arms each side depends on and strip the
    // tuple projection, leaving a function of just that arm's type.
    let mut processed: Vec<(usize, usize, Expr, Expr)> = Vec::new();

    for (raw_a, raw_b) in &eq_conditions_raw {
        let arm_a = is_function_of_single_tuple_arm(raw_a)?;
        let arm_b = is_function_of_single_tuple_arm(raw_b)?;

        if arm_a == arm_b {
            trace!("plan_loop_join: condition has both keys on same arm {arm_a}");
            return None;
        }
        if arm_a >= n || arm_b >= n {
            trace!("plan_loop_join: arm index out of range ({arm_a}, {arm_b}) for n={n}");
            return None;
        }

        let mut key_a = raw_a.clone();
        let mut key_b = raw_b.clone();
        replace_tuple_project_with_id(&mut key_a, &arm_types[arm_a]);
        typecheck(&key_a).ok()?;
        replace_tuple_project_with_id(&mut key_b, &arm_types[arm_b]);
        typecheck(&key_b).ok()?;

        trace!(
            "plan_loop_join: condition arm{arm_a}={} : {}  arm{arm_b}={} : {}",
            symbolic(&key_a),
            key_a.ty,
            symbolic(&key_b),
            key_b.ty,
        );

        processed.push((arm_a, arm_b, key_a, key_b));
    }

    let children = spanning_tree_children(&processed, n)?;

    // Pair each other predicate with the set of arms it depends on.
    let other_predicates: Vec<(Expr, BTreeSet<usize>)> = other_preds_raw
        .into_iter()
        .map(|pred| {
            let mut arms = BTreeSet::new();
            collect_arms_used(&pred, &mut arms);
            // TODO support constant predicates by constant-folding them away
            assert!(
                !arms.is_empty(),
                "TODO support constant predicates in joins"
            );
            (pred, arms)
        })
        .collect();

    build_join_plan(0, &children, &processed, arm_types, &other_predicates)
}

/// Concatenates two types into a single flat tuple type.
///
/// `indices_to_flatten` controls which arguments are unpacked: if `0` is present, `a` is
/// flattened (its tuple elements are spliced in directly); if `1` is present, `b` is
/// flattened; otherwise the type is treated as a single-element contribution.  Used to
/// compute the flat output domain of a hash join.
fn flatten_tuple_types(indices_to_flatten: &[i64], a: &Type, b: &Type) -> Type {
    let mut elts: Vec<Type> = match a {
        Type::Tuple(v) if indices_to_flatten.contains(&0) => v.clone(),
        other => vec![other.clone()],
    };
    match b {
        Type::Tuple(v) if indices_to_flatten.contains(&1) => elts.extend(v.clone()),
        other => elts.push(other.clone()),
    }
    Type::Tuple(elts)
}

/// Generates a CCL expression from a [`JoinPlan`].
///
/// `types[i]` is the type of the i-th original input arm.  `plan` is the tree of
/// [`JoinPlan::Hash`] and [`JoinPlan::Loop`] nodes produced by [`build_join_plan`].
fn join_plan_to_expr(plan: &JoinPlan, types: &[Type]) -> Expr {
    match plan {
        // For loop joins (including the trivial one-branch sort), iterate a tuple
        // type consisting of the types of just the arms in this join.
        //
        // The leaf emission is always `iterate(pred)` — the iteration-site
        // marker that op-conversion compiles to an `IterateExtent` (plus a
        // `Restrict` filter when `pred` is non-trivial).  When the loop has
        // its own residual predicate, it is composed with the base
        // identity and passed as `iterate`'s predicate; when there is no
        // predicate, the trivially-true predicate `true ▷ const` is used
        // and op-conversion recognises it as a filter-free iteration.
        JoinPlan::Loop { arms, predicate } => {
            let base_iteration = (|| {
                if arms.len() == 1 {
                    if let Type::Refinement(base_ty, refinement) = &types[arms[0]] {
                        // `convert_loop_join` only reads the predicate (it
                        // builds a new expr), so borrow the immutable term
                        // rather than clone it.
                        let pred = &*refinement.predicate;
                        trace!("Attempting loop join conversion inside iteration");
                        if let Some(transformed) = convert_loop_join(base_ty, pred) {
                            trace!(
                                "Converted iteration to {} : {}",
                                symbolic(&transformed),
                                transformed.ty
                            );
                            return transformed;
                        }
                    }
                    make_iterate(trivially_true_predicate(types[arms[0]].clone()))
                } else {
                    let ty = Type::Tuple(arms.iter().map(|&i| types[i].clone()).collect());
                    make_iterate(trivially_true_predicate(ty))
                }
            })();
            if let Some(predicate) = predicate {
                // Apply `restrict(predicate)` to the base iteration source as
                // a downstream filter step.  `restrict(p)` is the transformer
                // `(D ⇒ T) ⇒ ({d : D | p(d)} ⇒ T)`; applying it to
                // `base_iteration` narrows the domain and yields
                // `{D | predicate} ⇒ T`.  Op-conversion compiles this via the
                // generic applied-combinator arm: `base_iteration` is the
                // upstream (`input=None`), then the Restrict arm consumes it
                // (`input=Some(_)`) and emits a `Restrict` tile.
                make_restrict(predicate.clone(), base_iteration)
            } else {
                base_iteration
            }
        }

        // For hash joins, recursively build up the expressions for the build side and probe
        // side, then combine them as follows:
        //
        // Compute the build key:
        //    build_key = build ≫ .build_key_idx ≫ build_key_expr
        // Compute the probe key:
        //    probe_key: probe ≫ .probe_key_idx ≫ probe_key_expr
        // Run the hash join by conversing the build key, composing that with the probe key,
        // then massaging the domain to get back to the expected tuple structure:
        //    (probe_key ≫ build_key ▷ converse) ▷ uncurry ▷ flatten_domain ▷ map_domain
        //
        // Using the full probe/build output tuple types (not just the scalar key-arm types)
        // ensures that `flatten_domain` correctly flattens a tuple-of-tuples domain into a
        // single flat tuple, which `map_domain` then exposes as the final iteration domain.
        JoinPlan::Hash {
            build,
            probe,
            build_key_idx,
            build_key_expr,
            probe_key_idx,
            probe_key_expr,
            predicate,
        } => {
            let key_ty = build_key_expr
                .ty
                .codomain()
                .expect("build key must be a function")
                .clone();

            // Build side: group by the build key using converse.
            // Use the full build output tuple type so that converse groups entire
            // build tuples (not just the key arm), preserving all arms through the join.
            let build_input = join_plan_to_expr(build, types);
            let build_output_ty = build_input.ty.codomain().unwrap().clone();
            let build_key = if let Some(build_key_idx) = build_key_idx {
                typed_compose(vec![
                    build_input,
                    Expr::proj_index(*build_key_idx).with_ty(Type::fun(
                        build_output_ty.clone(),
                        build_key_expr.ty.domain().unwrap().clone(),
                    )),
                    build_key_expr.clone(),
                ])
            } else {
                typed_compose(vec![build_input, build_key_expr.clone()])
            };

            let converse_ty = Type::fun(
                key_ty.clone(),
                Type::fun(build_output_ty.clone(), build_output_ty.clone()),
            );
            let build_side = apply_primitive(build_key, Builtin::Converse, converse_ty);
            typecheck(&build_side).expect("Bad build expr");

            trace!(
                "join_plan_to_expr: build_side={} : {}",
                symbolic(&build_side),
                build_side.ty
            );

            // Probe side: compose the probe key with the build side lookup.
            // Use the full probe output tuple type for the same reason.
            let probe_input = join_plan_to_expr(probe, types);
            let probe_output_ty = probe_input.ty.codomain().unwrap().clone();
            let probe_key = if let Some(probe_key_idx) = probe_key_idx {
                typed_compose(vec![
                    probe_input,
                    Expr::proj_index(*probe_key_idx).with_ty(Type::fun(
                        probe_output_ty.clone(),
                        probe_key_expr.ty.domain().unwrap().clone(),
                    )),
                    probe_key_expr.clone(),
                ])
            } else {
                typed_compose(vec![probe_input, probe_key_expr.clone()])
            };

            let probe_expr = typed_compose(vec![probe_key, build_side]);
            typecheck(&probe_expr).expect("Bad probe expr");

            trace!(
                "join_plan_to_expr: probe={} : {}",
                symbolic(&probe_expr),
                probe_expr.ty
            );

            // uncurry: (probe_output_ty, build_output_ty) -> build_output_ty
            let uncurry = apply_primitive(
                probe_expr,
                Builtin::Uncurry,
                Type::fun(
                    Type::Tuple(vec![probe_output_ty.clone(), build_output_ty.clone()]),
                    build_output_ty.clone(),
                ),
            );

            trace!(
                "join_plan_to_expr: uncurry={} : {}",
                symbolic(&uncurry),
                uncurry.ty
            );

            // For each join input that is itself a Hash join, we need to flatten its domain
            // tuple into the result domain tuple.
            let mut indices_to_flatten = Vec::<i64>::new();
            if probe_key_idx.is_some() {
                indices_to_flatten.push(0);
            }
            if build_key_idx.is_some() {
                indices_to_flatten.push(1);
            }
            let flattened = if indices_to_flatten.is_empty() {
                uncurry
            } else {
                let flat_ty =
                    flatten_tuple_types(&indices_to_flatten, &probe_output_ty, &build_output_ty);
                let flatten_func = apply_primitive(
                    Expr::list(
                        indices_to_flatten
                            .iter()
                            .map(|i| Expr::lit(Lit::Int(*i)).with_ty(Type::Base(BaseType::Int)))
                            .collect(),
                    )
                    .with_ty(Type::fun(
                        Type::UIntRange(indices_to_flatten.len()),
                        Type::Base(BaseType::Int),
                    )),
                    Builtin::FlattenDomain,
                    Type::fun(
                        Type::fun(
                            Type::Tuple(vec![probe_output_ty.clone(), build_output_ty.clone()]),
                            build_output_ty.clone(),
                        ),
                        Type::fun(flat_ty.clone(), build_output_ty.clone()),
                    ),
                );
                let flattened = apply_function(
                    uncurry,
                    flatten_func,
                    Type::fun(flat_ty.clone(), build_output_ty.clone()),
                );

                trace!(
                    "join_plan_to_expr: flattened={} : {}",
                    symbolic(&flattened),
                    flattened.ty
                );
                flattened
            };

            let final_domain_ty = flattened.ty.domain().unwrap().clone();
            // map_domain: replace the codomain with Scalar(domain), yielding flat_ty -> flat_ty.
            let map_domain = apply_primitive(
                flattened,
                Builtin::MapDomain,
                Type::fun(final_domain_ty.clone(), final_domain_ty.clone()),
            );

            let result = if let Some(predicate) = predicate {
                // Apply `restrict(predicate)` to `map_domain` (the iteration
                // source over the joined flat-tuple domain) as a downstream
                // filter step.  `map_domain` is the upstream value-producer
                // that `restrict` consumes — op-conversion converts it with
                // `input=None` (preserving the invariant `MapDomain`
                // requires), then the Restrict arm filters the joined output.
                make_restrict(predicate.clone(), map_domain)
            } else {
                map_domain
            };

            typecheck(&result).expect("Bad hash join expr");
            result
        }
    }
}

/// Converts a loop-join refinement pattern into a hash-join expression.
///
/// Delegates to [`plan_loop_join`] to build a [`JoinPlan`], then to [`join_plan_to_expr`]
/// to generate the CCL output. Returns `None` if the pattern does not match.
fn convert_loop_join(base_ty: &Type, refinement: &Expr) -> Option<Expr> {
    trace!(
        "convert_loop_join: base_ty={}, refinement={} : {}",
        base_ty,
        symbolic(refinement),
        refinement.ty
    );
    trace!("typed refinement\n{}", symbolic_typed(refinement));

    let Type::Tuple(arm_types) = base_ty else {
        trace!("convert_loop_join: base_ty is not a tuple");
        return None;
    };
    let (plan, arm_order) = plan_loop_join(arm_types, refinement)?;
    trace!("convert_loop_join: planning succeeded. Plan:\n{plan:#?}");
    let expr = join_plan_to_expr(&plan, arm_types);

    // The morphism produces the join-satisfying extent; surface that on its
    // codomain so downstream consumers (e.g. a `cast({base | r} ⇒ …)` reading
    // the produced tuples) see the refinement they expect. A hash join folds
    // its equi-conditions into the key structure with no residual `Restrict`,
    // so the codomain would otherwise be bare — see [`refine_codomain`]. Apply
    // it to whichever morphism is returned (the refinement is the extent's,
    // independent of the BFS arm permutation, which only reorders the domain).

    // If BFS produced arms out of canonical order, undo the permutation so that the
    // output domain matches the original tuple type expected by the caller.
    let canonical: Vec<usize> = (0..arm_types.len()).collect();
    if arm_order == canonical {
        return Some(refine_codomain(expr, refinement));
    }

    // perm[j] = position of canonical arm j in arm_order (i.e. where to find it in actual).
    // permute_domain(perm)(f : actual → X) : canonical → X
    let actual_ty = Type::Tuple(arm_order.iter().map(|&i| arm_types[i].clone()).collect());
    let canonical_ty = Type::Tuple(arm_types.to_vec());
    let perm: Vec<i64> = canonical
        .iter()
        .map(|&j| arm_order.iter().position(|&a| a == j).unwrap() as i64)
        .collect();

    let perm_arg = Expr::list(
        perm.iter()
            .map(|&i| Expr::lit(Lit::Int(i)).with_ty(Type::Base(BaseType::Int)))
            .collect(),
    )
    .with_ty(Type::fun(
        Type::UIntRange(perm.len()),
        Type::Base(BaseType::Int),
    ));

    // permute_domain is polymorphic in the morphism it rearranges: it takes
    // `expr` (the join morphism, whose domain may carry the join-condition
    // refinement) and produces a canonical-ordered morphism. Declare its input
    // as `expr`'s *actual* type, not a bare `actual_ty ⇒ actual_ty`. Otherwise
    // `apply_function` re-stamps `permute_func`'s recorded type to
    // `fun(expr.ty, …)` (carrying expr's refinement) while its inner
    // `PermuteDomain` builtin keeps the bare declaration — an internally
    // inconsistent node the post-inference reconstruction can't rebuild
    // (the refinement rides the morphism's invariant domain⇒codomain position).
    let morphism_ty = expr.ty.clone();
    let permute_func = apply_primitive(
        perm_arg,
        Builtin::PermuteDomain,
        Type::fun(
            morphism_ty,
            Type::fun(canonical_ty.clone(), actual_ty.clone()),
        ),
    );
    let permuted = apply_function(
        expr,
        permute_func,
        Type::fun(canonical_ty.clone(), actual_ty.clone()),
    );
    let result = apply_primitive(
        permuted,
        Builtin::MapDomain,
        Type::fun(canonical_ty.clone(), canonical_ty.clone()),
    );
    let result = refine_codomain(result, refinement);
    typecheck(&result).expect("Bad permute_domain expr");
    Some(result)
}

/// Try the hash-join rewrite at an iteration site whose domain is `domain_ty`.
///
/// Called from [`wrap_with_iterate`] before its iterate-then-restricts
/// fallback: hash join is the specialised iteration strategy when the site's
/// domain is a refined tuple whose predicate decomposes into equality join
/// conditions (the recogniser is implemented by [`plan_loop_join`] /
/// [`convert_loop_join`]).  Returns `true` and rewrites `expr` to
/// `Compose([transformed, original])` on success, leaving `expr` untouched
/// and returning `false` otherwise.  `transformed` is itself iteration-bearing
/// at its leaves (`JoinPlan::Loop` emits `Apply(true ▷ const, Iterate)`),
/// so the resulting chain already has explicit iterate markers — no
/// further wrap is needed.
///
/// Loop joins can occur anywhere an iteration site appears: at the program
/// root, at sink-bound `Record` fields, at aggregate arguments, at
/// `LastOrDefault` streams, at `Loop` sources, at `CollectionUnion`
/// operands, or as a let-bound function value.
///
/// Supports n-way joins (n ≥ 2) when all arms are connected via equality
/// conditions that form a spanning tree.  Build/probe assignment follows
/// the BFS order of that spanning tree.  For now, predicates must be
/// expressed as conjunctions of single-arm equality conditions.
fn try_hash_join_rewrite(expr: &mut Expr, domain_ty: &Type) -> bool {
    let Type::Refinement(base, refinement) = domain_ty else {
        return false;
    };
    // `convert_loop_join` only reads the predicate (it builds a new expr), so
    // borrow the immutable term rather than clone it.
    let pred = &*refinement.predicate;
    trace!(
        "Attempting hash-join rewrite at iteration site: {}",
        symbolic(expr),
    );
    let Some(transformed) = convert_loop_join(base, pred) else {
        trace!("Hash-join pattern did not match");
        return false;
    };
    trace!(
        "Hash-join rewrite succeeded: {} : {}",
        symbolic(&transformed),
        transformed.ty,
    );
    let codomain = expr.ty.codomain().expect("function-typed iteration site");
    let result_ty = Type::fun(
        transformed
            .ty
            .domain()
            .expect("convert_loop_join output must be function-typed"),
        codomain,
    );
    *expr = compose(transformed, take(expr)).with_ty(result_ty);
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::simple_sub::FieldKey;
    use crate::ccl::{BaseType, Expr};

    fn var(name: &str) -> Expr {
        Expr::var(name)
    }

    fn proj_idx(n: usize) -> Expr {
        Expr::proj_index(n)
    }

    fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    fn fun_ty(domain: Type, codomain: Type) -> Type {
        Type::Fun {
            name: None,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    fn tuple_ty(tys: Vec<Type>) -> Type {
        Type::Tuple(tys)
    }

    fn compose(elts: Vec<Expr>) -> Expr {
        Expr::compose(elts)
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_projection() {
        let expr = proj_idx(0);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_second_index() {
        let expr = proj_idx(1);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_var() {
        let expr = var("x");
        assert_eq!(is_function_of_single_tuple_arm(&expr), None);
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_compose_with_projection_first() {
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![proj_idx(1).with_ty(proj0_ty), var("f").with_ty(f_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_compose_without_projection() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![var("f").with_ty(f_ty), var("g").with_ty(g_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&expr), None);
    }

    #[test]
    fn test_apply_primitive_basic() {
        let int_ty_val = int_ty();
        let expr = var("f").with_ty(int_ty_val.clone());
        let output_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let result = apply_primitive(expr, Builtin::Map, output_ty.clone());

        // Check that result is an apply expression
        assert!(matches!(result.node, TypedExprNode::Apply { .. }));
        // Check that the type is correct
        assert_eq!(result.ty, output_ty);
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_projection() {
        let int_ty_val = int_ty();
        let mut expr = proj_idx(0);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should be identity function
        assert!(matches!(expr.node, TypedExprNode::Builtin(Builtin::Id)));
        assert_eq!(expr.ty, fun_ty(int_ty_val.clone(), int_ty_val));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_compose() {
        let int_ty_val = int_ty();
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let mut expr = compose(vec![
            proj_idx(1).with_ty(proj0_ty),
            var("f").with_ty(f_ty.clone()),
        ])
        .with_ty(f_ty);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, first element should be identity
        if let TypedExprNode::Compose(elts) = &expr.node {
            assert!(matches!(elts[0].node, TypedExprNode::Builtin(Builtin::Id)));
        } else {
            panic!("Expected Compose node");
        }
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_recognize_groupby_sites_on_var() {
        let mut expr = var("x");
        recognize_groupby_sites(&mut expr);
        // Should remain unchanged
        assert!(matches!(expr.node, TypedExprNode::Var(ref v) if v.base() == "x"));
    }

    // Tests for convert_loop_join function
    #[test]
    fn test_convert_loop_join_rejects_non_tuple_base_type() {
        let int_ty_val = int_ty();
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Base type is not a tuple, should return None
        let result = convert_loop_join(&int_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_wrong_tuple_size() {
        let int_ty_val = int_ty();
        let triple_tuple = tuple_ty(vec![
            int_ty_val.clone(),
            int_ty_val.clone(),
            int_ty_val.clone(),
        ]);
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Refinement is not a valid join condition, should return None
        let result = convert_loop_join(&triple_tuple, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_compose_refinement() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Refinement is not a compose, should return None
        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_wrong_compose_size() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create a compose with 3 elements (not 2)
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty.clone()),
            var("g").with_ty(f_ty.clone()),
            var("h").with_ty(f_ty),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_eq_second_element() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create a compose where second element is not "eq"
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty),
            var("ne").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_missing_zip_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create a compose where first element is not an Apply
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty),
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_zip_function() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create an apply with function that is not "zip"
        let args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(int_ty_val.clone()),
            proj_idx(1).with_ty(int_ty_val.clone()),
        ]);
        let non_zip_apply = Expr::apply(
            args_tuple,
            var("not_zip").with_ty(fun_ty(tuple_ty_val.clone(), tuple_ty_val.clone())),
        )
        .with_ty(fun_ty(tuple_ty_val.clone(), tuple_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            non_zip_apply,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_zip_with_non_tuple_args() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create an apply where argument is not a tuple
        let non_tuple_apply = Expr::apply(
            var("arg").with_ty(int_ty_val.clone()),
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(int_ty_val.clone(), tuple_ty_val.clone())),
        )
        .with_ty(fun_ty(int_ty_val.clone(), tuple_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            non_tuple_apply,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_mismatched_zip_args() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create zip with only 1 argument (not 2)
        let args_tuple = Expr::tuple(vec![proj_idx(0).with_ty(int_ty_val.clone())]);
        let zip_apply = Expr::apply(
            args_tuple,
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(int_ty_val.clone(), int_ty_val.clone())),
        )
        .with_ty(fun_ty(int_ty_val.clone(), int_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            zip_apply,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_same_key_index() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create zip where both args project from same tuple element
        let args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let zip_apply = Expr::apply(
            args_tuple,
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            zip_apply,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    /// Build a **bare** 2-arm join predicate `__elem.0 ▷ (λ x → __elem.1 ▷
    /// (λ y → <mk_bool(x, y)>))` over `(scalar, scalar)` — the implicit
    /// REFINEMENT_BINDER form `split_join_conditions` decomposes (the element
    /// binder is the refinement's own, no enclosing `λ rec`).
    fn pointful_2arm_pred(scalar: &Type, mk_bool: impl FnOnce(Expr, Expr) -> Expr) -> Expr {
        let b = Type::Base(BaseType::Bool);
        let rec_ty = tuple_ty(vec![scalar.clone(), scalar.clone()]);
        let rec_arm = |i: usize| {
            Expr::apply(
                Expr::var(Name::elem()).with_ty(rec_ty.clone()),
                proj_idx(i).with_ty(fun_ty(rec_ty.clone(), scalar.clone())),
            )
            .with_ty(scalar.clone())
        };
        let body = mk_bool(
            var("x").with_ty(scalar.clone()),
            var("y").with_ty(scalar.clone()),
        );
        let inner =
            Expr::lambda("y", scalar.clone(), body).with_ty(fun_ty(scalar.clone(), b.clone()));
        let mid = Expr::apply(rec_arm(1), inner).with_ty(b.clone());
        let outer =
            Expr::lambda("x", scalar.clone(), mid).with_ty(fun_ty(scalar.clone(), b.clone()));
        Expr::apply(rec_arm(0), outer).with_ty(b)
    }

    #[test]
    fn test_convert_loop_join_succeeds_with_valid_input() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Pointful predicate: λ rec → rec.0 ▷ (λ x → rec.1 ▷ (λ y → x == y)).
        let refinement = pointful_2arm_pred(&int_ty_val, |x, y| {
            Expr::binop(x, BinOpKind::Compare(CompareKind::Equals), y)
                .with_ty(Type::Base(BaseType::Bool))
        });

        // Should successfully convert
        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert!(
            result.is_some(),
            "convert_loop_join should succeed with valid hash join pattern"
        );

        assert_eq!(
            symbolic(&result.unwrap()),
            "(iterate ≫ id ≫ (iterate ≫ id) ▷ converse) ▷ uncurry ▷ map_domain"
        );
    }

    // Tests for is_function_of_single_tuple_arm with zip applications
    #[test]
    fn test_is_function_of_single_tuple_arm_on_zip_with_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty(), int_ty()]),
            tuple_ty(vec![int_ty(), int_ty()]),
        );
        // zip(proj(0), ...) should return 0
        let arg = proj_idx(0).with_ty(proj_ty);
        let zip_app = Expr::apply(arg, Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty));
        assert_eq!(is_function_of_single_tuple_arm(&zip_app), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_zip_with_second_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty(), int_ty()]),
            tuple_ty(vec![int_ty(), int_ty()]),
        );
        // zip(proj(1), ...) should return 1
        let arg = proj_idx(1).with_ty(proj_ty);
        let zip_app = Expr::apply(arg, Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty));
        assert_eq!(is_function_of_single_tuple_arm(&zip_app), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_zip_without_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty(), int_ty()]),
            tuple_ty(vec![int_ty(), int_ty()]),
        );
        // zip(f, ...) where f is not a projection should return None
        let arg = var("f").with_ty(f_ty);
        let zip_app = Expr::apply(arg, Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty));
        assert_eq!(is_function_of_single_tuple_arm(&zip_app), None);
    }

    // Tests for is_function_of_single_tuple_arm with tuples
    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_single_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        // A tuple containing a single projection should return that projection's index
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let tuple_expr = Expr::tuple(vec![proj_idx(0).with_ty(proj_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_all_same_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple where all non-constant elements use the same projection
        let tuple_expr = Expr::tuple(vec![
            proj_idx(0).with_ty(proj_ty.clone()),
            proj_idx(0).with_ty(proj_ty.clone()),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_different_projections() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple where elements use different projections should return None
        let tuple_expr = Expr::tuple(vec![
            proj_idx(0).with_ty(proj_ty.clone()),
            proj_idx(1).with_ty(proj_ty.clone()),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), None);
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_with_constants() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple with a projection and constant expressions should ignore constants
        let tuple_expr = Expr::tuple(vec![
            proj_idx(0).with_ty(proj_ty),
            apply_primitive(var("c").with_ty(int_ty()), Builtin::Const, const_fn_ty),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_no_projections() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        // A tuple with no projections (non-constant) should return None
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let tuple_expr = Expr::tuple(vec![var("f").with_ty(f_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), None);
    }

    // Tests for is_constant helper
    #[test]
    fn test_is_constant_on_const_apply() {
        let int_ty_val = int_ty();
        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            int_ty_val,
        );
        assert!(is_constant(&const_expr));
    }

    #[test]
    fn test_is_constant_on_non_const_apply() {
        let int_ty_val = int_ty();
        let non_const_expr = apply_primitive(
            var("f").with_ty(int_ty_val.clone()),
            Builtin::Map,
            int_ty_val,
        );
        assert!(!is_constant(&non_const_expr));
    }

    #[test]
    fn test_is_constant_on_compose_with_const() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let g_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );
        let compose_expr = compose(vec![const_expr, var("g").with_ty(g_ty)])
            .with_ty(fun_ty(tuple_ty_val, int_ty_val));
        // A compose where the first element is const is considered constant
        assert!(is_constant(&compose_expr));
    }

    #[test]
    fn test_is_constant_on_var() {
        let expr = var("x");
        assert!(!is_constant(&expr));
    }

    // Tests for replace_tuple_project_with_id with Apply expressions
    #[test]
    fn test_replace_tuple_project_with_id_on_zip_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        );

        let mut expr = Expr::apply(
            proj_idx(0).with_ty(proj_ty),
            Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty.clone()),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should be Apply with zip function
        assert!(matches!(expr.node, TypedExprNode::Apply { .. }));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    // Tests for replace_tuple_project_with_id with Tuple expressions
    #[test]
    fn test_replace_tuple_project_with_id_on_tuple() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());

        let mut expr = Expr::tuple(vec![
            proj_idx(0).with_ty(proj_ty.clone()),
            proj_idx(0).with_ty(proj_ty),
        ])
        .with_ty(tuple_ty(vec![
            fun_ty(tuple_ty_val.clone(), int_ty_val.clone()),
            fun_ty(tuple_ty_val, int_ty_val.clone()),
        ]));

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should still be a Tuple
        assert!(matches!(expr.node, TypedExprNode::Tuple(_)));

        // Check that the tuple type's function domains have been updated
        if let Type::Tuple(ref elts) = expr.ty {
            for elt in elts {
                match elt {
                    Type::Fun {
                        domain,
                        codomain: _,
                        ..
                    } => {
                        assert_eq!(**domain, int_ty_val);
                    }
                    _ => panic!("Expected function type in tuple"),
                }
            }
        } else {
            panic!("Expected tuple type");
        }
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_tuple_with_constants() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());

        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty.clone(),
        );

        let mut expr =
            Expr::tuple(vec![proj_idx(0).with_ty(proj_ty), const_expr]).with_ty(tuple_ty(vec![
                fun_ty(tuple_ty_val.clone(), int_ty_val.clone()),
                const_fn_ty,
            ]));

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should still be a Tuple
        assert!(matches!(expr.node, TypedExprNode::Tuple(_)));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_constant_domain_type_on_const_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val, int_ty_val.clone());

        let mut expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun {
            domain,
            codomain: _,
            ..
        } = &expr.ty
        {
            assert_eq!(**domain, int_ty_val);
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn test_replace_constant_domain_type_on_compose_with_const() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let g_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());

        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );

        let mut expr = compose(vec![const_expr, var("g").with_ty(g_ty)])
            .with_ty(fun_ty(tuple_ty_val, int_ty_val.clone()));

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun {
            domain,
            codomain: _,
            ..
        } = &expr.ty
        {
            assert_eq!(**domain, int_ty_val);
        } else {
            panic!("Expected function type");
        }
    }

    /// Builds a dummy condition tuple; the Expr fields are placeholders since
    /// `spanning_tree_children` and `build_join_plan` only inspect the arm indices.
    fn cond(a: usize, b: usize) -> (usize, usize, Expr, Expr) {
        (a, b, var("k"), var("k"))
    }

    // --- spanning_tree_children ---

    #[test]
    fn test_spanning_tree_n_zero_returns_none() {
        assert_eq!(spanning_tree_children(&[], 0), None);
    }

    #[test]
    fn test_spanning_tree_n_one_single_leaf() {
        // No edges needed; the single node is already its own spanning tree.
        let children = spanning_tree_children(&[], 1).unwrap();
        assert_eq!(children, vec![vec![]]);
    }

    #[test]
    fn test_spanning_tree_two_arm_linear() {
        let children = spanning_tree_children(&[cond(0, 1)], 2).unwrap();
        assert_eq!(children, vec![vec![1], vec![]]);
    }

    #[test]
    fn test_spanning_tree_three_arm_linear() {
        // 0-1-2 chain; BFS from 0 should visit 1 then 2.
        let children = spanning_tree_children(&[cond(0, 1), cond(1, 2)], 3).unwrap();
        assert_eq!(children, vec![vec![1], vec![2], vec![]]);
    }

    #[test]
    fn test_spanning_tree_star_canonical_condition_order() {
        // Hub 0 connects to 1 then 2; conditions listed 0-1 before 0-2.
        let children = spanning_tree_children(&[cond(0, 1), cond(0, 2)], 3).unwrap();
        assert_eq!(children, vec![vec![1, 2], vec![], vec![]]);
    }

    #[test]
    fn test_spanning_tree_star_reversed_condition_order() {
        // Same topology but 0-2 listed first; BFS picks up 2 before 1.
        let children = spanning_tree_children(&[cond(0, 2), cond(0, 1)], 3).unwrap();
        assert_eq!(children, vec![vec![2, 1], vec![], vec![]]);
    }

    #[test]
    fn test_spanning_tree_two_level_branching() {
        // 0 -> {1, 2}, 1 -> {3, 4}: branching at root and at an intermediate node.
        let children =
            spanning_tree_children(&[cond(0, 1), cond(0, 2), cond(1, 3), cond(1, 4)], 5).unwrap();
        assert_eq!(
            children,
            vec![vec![1, 2], vec![3, 4], vec![], vec![], vec![]]
        );
    }

    #[test]
    fn test_spanning_tree_cyclic_graph() {
        // Triangle 0-1-2-0: BFS from 0 reaches 1 via cond(0,1) and 2 via cond(2,0) in the
        // same round, so the cycle edge cond(1,2) is pruned and all nodes are still reached.
        let children = spanning_tree_children(&[cond(0, 1), cond(1, 2), cond(2, 0)], 3).unwrap();
        assert_eq!(children, vec![vec![1, 2], vec![], vec![]]);
    }

    #[test]
    fn test_spanning_tree_disconnected_returns_none() {
        // Only arm 0 and 1 are connected; arm 2 is unreachable.
        assert_eq!(spanning_tree_children(&[cond(0, 1)], 3), None);
    }

    // --- subtree_arms ---

    #[test]
    fn test_subtree_arms_single_leaf() {
        let children = vec![vec![]];
        assert_eq!(subtree_arms(0, &children), vec![0]);
    }

    #[test]
    fn test_subtree_arms_linear_chain_from_root() {
        // 0 -> 1 -> 2
        let children = vec![vec![1], vec![2], vec![]];
        assert_eq!(subtree_arms(0, &children), vec![0, 1, 2]);
    }

    #[test]
    fn test_subtree_arms_linear_chain_from_middle() {
        // Starting at node 1 should only include 1 and 2.
        let children = vec![vec![1], vec![2], vec![]];
        assert_eq!(subtree_arms(1, &children), vec![1, 2]);
    }

    #[test]
    fn test_subtree_arms_star() {
        // 0 -> {1, 2}; all three arms should appear.
        let children = vec![vec![1, 2], vec![], vec![]];
        assert_eq!(subtree_arms(0, &children), vec![0, 1, 2]);
    }

    // --- build_join_plan ---

    #[test]
    fn test_build_join_plan_two_arms_canonical_order() {
        let conditions = vec![cond(0, 1)];
        let children = vec![vec![1], vec![]];
        let (plan, arm_order) = build_join_plan(0, &children, &conditions, &[], &[]).unwrap();
        assert_eq!(arm_order, vec![0, 1]);
        // Single join: no tuple projection needed on either side.
        let JoinPlan::Hash {
            probe_key_idx,
            build_key_idx,
            ..
        } = plan
        else {
            panic!("expected Hash");
        };
        assert_eq!(probe_key_idx, None);
        assert_eq!(build_key_idx, None);
    }

    #[test]
    fn test_build_join_plan_three_arm_linear_canonical_order() {
        // 0-1-2 chain; conditions x==y (0,1) then y==z (1,2).
        let conditions = vec![cond(0, 1), cond(1, 2)];
        let children = vec![vec![1], vec![2], vec![]];
        let (plan, arm_order) = build_join_plan(0, &children, &conditions, &[], &[]).unwrap();
        assert_eq!(arm_order, vec![0, 1, 2]);
        // Outer join probes with Loop([0]) (single arm → probe_key_idx=None) against the
        // inner Hash{Loop([1]),Loop([2])}.  The join key is arm 1, which sits at position 0
        // in the inner join's output arms [1,2], so build_key_idx=Some(0).
        let JoinPlan::Hash {
            probe_key_idx,
            build_key_idx,
            ..
        } = plan
        else {
            panic!("expected outer Hash");
        };
        assert_eq!(probe_key_idx, None);
        assert_eq!(build_key_idx, Some(0));
    }

    #[test]
    fn test_build_join_plan_star_out_of_order_produces_permuted_arm_order() {
        // x==z (0,2) listed before x==y (0,1); BFS visits arm 2 before arm 1.
        // arm_order must be [0,2,1], which triggers the permute_domain path.
        let conditions = vec![cond(0, 2), cond(0, 1)];
        let children = vec![vec![2, 1], vec![], vec![]];
        let (_, arm_order) = build_join_plan(0, &children, &conditions, &[], &[]).unwrap();
        assert_eq!(arm_order, vec![0, 2, 1]);
    }

    #[test]
    fn test_build_join_plan_no_straddling_condition_returns_none() {
        // children say arm 1 is a child of arm 0, but conditions only mention arms 0 and 2 —
        // no condition straddles the {0} / {1} split, so planning must fail.
        let conditions = vec![cond(0, 2)];
        let children = vec![vec![1], vec![], vec![]];
        assert!(build_join_plan(0, &children, &conditions, &[], &[]).is_none());
    }

    // --- split_join_conditions ---

    fn make_eq_cond(tup: &Type, scalar: &Type) -> Expr {
        let args = Expr::tuple(vec![
            proj_idx(0).with_ty(fun_ty(tup.clone(), scalar.clone())),
            proj_idx(1).with_ty(fun_ty(tup.clone(), scalar.clone())),
        ]);
        let zip_out = fun_ty(tup.clone(), tuple_ty(vec![scalar.clone(), scalar.clone()]));
        let zipped = Expr::apply(
            args,
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(
                tuple_ty(vec![scalar.clone(), scalar.clone()]),
                tuple_ty(vec![scalar.clone(), scalar.clone()]),
            )),
        )
        .with_ty(zip_out);
        compose(vec![
            zipped,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals))).with_ty(fun_ty(
                tuple_ty(vec![scalar.clone(), scalar.clone()]),
                scalar.clone(),
            )),
        ])
        .with_ty(fun_ty(tup.clone(), scalar.clone()))
    }

    fn make_filter_pred(tup: &Type, scalar: &Type, arm: usize) -> Expr {
        // proj(arm) ≫ filter_fn : tup -> scalar
        compose(vec![
            proj_idx(arm).with_ty(fun_ty(tup.clone(), scalar.clone())),
            var("filter_fn").with_ty(fun_ty(scalar.clone(), scalar.clone())),
        ])
        .with_ty(fun_ty(tup.clone(), scalar.clone()))
    }

    // `split_join_conditions` now decomposes the *pointful* predicate form
    // (`λ rec → rec.i ▷ li ▷ (λ vi → <bool>)`); it is exercised end-to-end by
    // the join goldens (`test_joins` — including the unsound-zip-substitution
    // probe — and the multi-arm AND/residual/permute cases in
    // `test_new_compile`), which run it on real inferred predicates rather than
    // hand-built combinator ASTs.

    // --- collect_arms_used ---

    #[test]
    fn test_collect_arms_used_single_proj() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let expr = proj_idx(1).with_ty(fun_ty(t, i));
        let mut arms = BTreeSet::new();
        collect_arms_used(&expr, &mut arms);
        assert_eq!(arms, BTreeSet::from([1]));
    }

    #[test]
    fn test_collect_arms_used_compose() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let expr = make_filter_pred(&t, &i, 0);
        let mut arms = BTreeSet::new();
        collect_arms_used(&expr, &mut arms);
        assert_eq!(arms, BTreeSet::from([0]));
    }

    #[test]
    fn test_collect_arms_used_zip_with_two_arms() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let eq_cond = make_eq_cond(&t, &i);
        // The eq condition uses arms 0 and 1 via the zip
        let mut arms = BTreeSet::new();
        collect_arms_used(&eq_cond, &mut arms);
        assert_eq!(arms, BTreeSet::from([0, 1]));
    }

    // --- convert_loop_join with mixed predicate ---

    #[test]
    fn test_convert_loop_join_succeeds_with_eq_plus_filter_predicate() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let b = Type::Base(BaseType::Bool);

        // Pointful: λ rec → rec.0 ▷ (λ x → rec.1 ▷ (λ y → x == y and x ▷ some_filter)).
        // The equality drives the join; `x ▷ some_filter` is a residual on arm 0.
        let refinement = pointful_2arm_pred(&i, |x, y| {
            let eq = Expr::binop(x.clone(), BinOpKind::Compare(CompareKind::Equals), y)
                .with_ty(b.clone());
            let filt = Expr::apply(x, var("some_filter").with_ty(fun_ty(i.clone(), b.clone())))
                .with_ty(b.clone());
            Expr::binop(eq, BinOpKind::BoolLogic(LogicKind::And), filt).with_ty(b.clone())
        });

        // Should succeed: eq condition drives the hash join, filter becomes a predicate.
        let result = convert_loop_join(&t, &refinement);
        assert!(
            result.is_some(),
            "convert_loop_join should succeed when eq conditions + extra filter are present"
        );

        // The output should contain "iterate" with the pushed-down filter attached
        // (filter predicates ride into the iteration via iterate(p) rather than the
        // legacy `restrict` builtin).
        let sym = symbolic(&result.unwrap());
        assert!(
            sym.contains("iterate"),
            "expected 'iterate' in output for pushed-down filter, got: {sym}"
        );
    }

    #[test]
    fn test_convert_loop_join_rejects_pure_non_eq_predicate() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let bool_ty_val = Type::Base(BaseType::Bool);

        // A pure filter predicate with no equality condition — cannot build hash join.
        let filter = compose(vec![
            proj_idx(0).with_ty(fun_ty(t.clone(), i.clone())),
            var("some_filter").with_ty(fun_ty(i.clone(), bool_ty_val.clone())),
        ])
        .with_ty(fun_ty(t.clone(), bool_ty_val));

        assert_eq!(
            convert_loop_join(&t, &filter),
            None,
            "should return None when no equality conditions are present"
        );
    }

    // -----------------------------------------------------------------
    // Helpers for the iteration-insertion test group.
    // -----------------------------------------------------------------

    use std::rc::Rc;

    use crate::ccl::Refinement;
    use crate::ccl::ccl_utils::is_trivially_true_predicate;
    use crate::ccl::symbolic::symbolic;

    fn bool_ty() -> Type {
        Type::Base(BaseType::Bool)
    }

    /// Build a [`Type::Refinement`] wrapping `base` with `predicate` as its
    /// predicate.  The predicate must have type `base ⇒ Bool` so the
    /// refinement is well-formed.
    fn refined_ty(base: Type, predicate: Expr) -> Type {
        Type::Refinement(
            Box::new(base),
            Refinement {
                predicate: Rc::new(predicate),
            },
        )
    }

    /// Build an `Apply { argument, function: <builtin> }` whose function
    /// position carries the supplied `function_ty`.  Used to construct
    /// arms-internalising shapes (`Sum`, `Converse`, `MapDomain`, …)
    /// without going through the full lambda-elim pipeline.
    fn apply_builtin(argument: Expr, builtin: Builtin, function_ty: Type, result_ty: Type) -> Expr {
        Expr::apply(argument, Expr::builtin(builtin).with_ty(function_ty)).with_ty(result_ty)
    }

    /// Build a finite list literal `[1, 2, 3]` typed `[0, 2] ⇒ Int`.
    fn list_123() -> Expr {
        let int = int_ty();
        Expr::list(vec![
            Expr::lit(Lit::Int(1)).with_ty(int.clone()),
            Expr::lit(Lit::Int(2)).with_ty(int.clone()),
            Expr::lit(Lit::Int(3)).with_ty(int.clone()),
        ])
        .with_ty(fun_ty(Type::UIntRange(3), int))
    }

    /// Returns `true` if `expr` is `Apply { function: Builtin::Iterate, .. }`
    /// at the top level — used by the assertions below to check that a
    /// wrap actually fired.
    fn is_iterate_apply(expr: &Expr) -> bool {
        let TypedExprNode::Apply { function, .. } = &expr.node else {
            return false;
        };
        matches!(&function.node, TypedExprNode::Builtin(Builtin::Iterate))
    }

    /// Returns the upstream value-producer if `expr` is `restrict(p)`
    /// *applied* to it — the term `Apply { argument: upstream, function:
    /// Apply(p, Restrict) }`.  `restrict` is a function transformer applied
    /// to its upstream (not composed), so the marker lives in the `function`
    /// position one level down.  Used to assert mid-chain filter emission
    /// and to walk down a stack of applied restricts.
    fn restrict_application_upstream(expr: &Expr) -> Option<&Expr> {
        let TypedExprNode::Apply { argument, function } = &expr.node else {
            return None;
        };
        let TypedExprNode::Apply {
            function: inner, ..
        } = &function.node
        else {
            return None;
        };
        matches!(&inner.node, TypedExprNode::Builtin(Builtin::Restrict)).then_some(argument)
    }

    /// Returns the leftmost element of `expr` if it is a [`Compose`], or
    /// `expr` itself otherwise.  Used to read the chain head out of a
    /// (possibly-wrapped) compose.
    fn chain_head(expr: &Expr) -> &Expr {
        match &expr.node {
            TypedExprNode::Compose(elts) => elts.first().unwrap_or(expr),
            _ => expr,
        }
    }

    // -----------------------------------------------------------------
    // is_iteration_bearing
    // -----------------------------------------------------------------

    #[test]
    fn test_is_iteration_bearing_iterate_apply() {
        // `Apply(true_pred, Iterate)` is the canonical marker — wrapping
        // would be redundant.
        let pred = trivially_true_predicate(int_ty());
        let iter_expr = make_iterate(pred);
        assert!(is_iteration_bearing(&iter_expr));
    }

    #[test]
    fn test_is_iteration_bearing_restrict_apply() {
        // A refined site's head is the outermost `restrict` filter
        // *applied* to an iterate source — `Apply(iterate, Apply(p,
        // Restrict))`.  It is iteration-bearing because its upstream is
        // (`make_restrict` only ever wraps an iteration source); without
        // this, a second marker pass would re-enter `wrap_with_iterate`
        // and double-iterate the refined collection.
        let iter_expr = make_iterate(trivially_true_predicate(int_ty()));
        // A non-trivial predicate (`false ▷ const`, structurally distinct
        // from the trivially-true one) so `make_restrict` actually wraps
        // the domain in a `Type::Refinement` — the refined-site shape.
        let pred = apply_primitive(
            Expr::lit(Lit::Bool(false)).with_ty(bool_ty()),
            Builtin::Const,
            fun_ty(int_ty(), bool_ty()),
        );
        let restricted = make_restrict(pred, iter_expr);
        // Sanity: the head really is a restrict applied to its upstream.
        assert!(restrict_application_upstream(&restricted).is_some());
        assert!(is_iteration_bearing(&restricted));
    }

    #[test]
    fn test_is_iteration_bearing_map_domain_apply() {
        // `Apply(_, MapDomain)` internalises iteration in op-conversion
        // (its arm asserts `input.is_none()`), so wrapping would break it.
        let int = int_ty();
        let inner = list_123();
        let expr = apply_builtin(
            inner,
            Builtin::MapDomain,
            fun_ty(
                fun_ty(Type::UIntRange(3), int.clone()),
                fun_ty(Type::UIntRange(3), int.clone()),
            ),
            fun_ty(Type::UIntRange(3), int),
        );
        assert!(is_iteration_bearing(&expr));
    }

    #[test]
    fn test_is_iteration_bearing_converse_apply() {
        // `Apply(_, Converse)` accepts `input=None` (it is itself an
        // iteration source) — recognising it prevents prepending an
        // outer iterate that would force an infinite extent over the
        // converse's input domain.
        let int = int_ty();
        let inner = list_123();
        let expr = apply_builtin(
            inner,
            Builtin::Converse,
            fun_ty(
                fun_ty(Type::UIntRange(3), int.clone()),
                fun_ty(int.clone(), fun_ty(Type::UIntRange(3), Type::UIntRange(3))),
            ),
            fun_ty(int, fun_ty(Type::UIntRange(3), Type::UIntRange(3))),
        );
        assert!(is_iteration_bearing(&expr));
    }

    #[test]
    fn test_is_iteration_bearing_const_apply_not_iteration_bearing() {
        // `Apply(_, Const)` is input-threading — wrapping it adds a real
        // iteration source.
        let int = int_ty();
        let const_apply = apply_builtin(
            Expr::lit(Lit::Int(5)).with_ty(int.clone()),
            Builtin::Const,
            fun_ty(int.clone(), fun_ty(int.clone(), int.clone())),
            fun_ty(int.clone(), int),
        );
        assert!(!is_iteration_bearing(&const_apply));
    }

    #[test]
    fn test_is_iteration_bearing_list_literal_not_iteration_bearing() {
        // List literals are iteration leaves; op-conversion's arm
        // requires an input stream, so planning must prepend iterate.
        assert!(!is_iteration_bearing(&list_123()));
    }

    #[test]
    fn test_is_iteration_bearing_var_function_typed() {
        // A function-typed `Var` references a let-bound iteration source
        // that was already iterate-wrapped at its bind site, so the
        // dereference itself doesn't need another wrap.
        let var_expr = var("xs").with_ty(fun_ty(Type::UIntRange(3), int_ty()));
        assert!(is_iteration_bearing(&var_expr));
    }

    #[test]
    fn test_is_iteration_bearing_var_scalar_not_iteration_bearing() {
        // A scalar `Var` isn't an iteration site at all — it shouldn't
        // be flagged as already-iterating either; `wrap_with_iterate`'s
        // domain-check then no-ops on it.
        let var_expr = var("x").with_ty(int_ty());
        assert!(!is_iteration_bearing(&var_expr));
    }

    #[test]
    fn test_is_iteration_bearing_record_at_head() {
        // Value-position `Record` is compiled by op-conversion's
        // `Record` arm under `input=None`; wrapping the chain would
        // feed an unwanted upstream stream in.
        let int = int_ty();
        let record = Expr::new(TypedExprNode::Record(vec![("f".to_string(), list_123())])).with_ty(
            Type::Record(vec![("f".to_string(), fun_ty(Type::UIntRange(3), int))]),
        );
        assert!(is_iteration_bearing(&record));
    }

    #[test]
    fn test_is_iteration_bearing_proj_apply() {
        // `Apply(record, Proj)` falls through to op-conversion's catch-all
        // `Apply` arm, which asserts `input.is_none()`.  Recognising
        // non-builtin function position as iteration-bearing avoids the
        // wrap-then-fail trap.
        let int = int_ty();
        let record_ty = Type::Record(vec![(
            "f".to_string(),
            fun_ty(Type::UIntRange(3), int.clone()),
        )]);
        let record = Expr::new(TypedExprNode::Record(vec![("f".to_string(), list_123())]))
            .with_ty(record_ty.clone());
        let proj = Expr::proj_field("f")
            .with_ty(fun_ty(record_ty, fun_ty(Type::UIntRange(3), int.clone())));
        let apply = Expr::apply(record, proj).with_ty(fun_ty(Type::UIntRange(3), int));
        assert!(is_iteration_bearing(&apply));
    }

    #[test]
    fn test_is_iteration_bearing_compose_inspects_head() {
        // `is_iteration_bearing` peeks at the first compose element —
        // a compose led by a non-iteration-bearing leaf is itself
        // wrap-eligible.
        let int = int_ty();
        let chain = compose(vec![
            list_123(),
            apply_builtin(
                Expr::tuple(vec![
                    Expr::builtin(Builtin::Id).with_ty(fun_ty(int.clone(), int.clone())),
                    apply_builtin(
                        Expr::lit(Lit::Int(10)).with_ty(int.clone()),
                        Builtin::Const,
                        fun_ty(int.clone(), fun_ty(int.clone(), int.clone())),
                        fun_ty(int.clone(), int.clone()),
                    ),
                ])
                .with_ty(Type::Tuple(vec![
                    fun_ty(int.clone(), int.clone()),
                    fun_ty(int.clone(), int.clone()),
                ])),
                Builtin::Zip,
                fun_ty(
                    Type::Tuple(vec![
                        fun_ty(int.clone(), int.clone()),
                        fun_ty(int.clone(), int.clone()),
                    ]),
                    fun_ty(int.clone(), Type::Tuple(vec![int.clone(), int.clone()])),
                ),
                fun_ty(int.clone(), Type::Tuple(vec![int.clone(), int.clone()])),
            ),
        ])
        .with_ty(fun_ty(
            Type::UIntRange(3),
            Type::Tuple(vec![int.clone(), int]),
        ));
        assert!(!is_iteration_bearing(&chain));
    }

    // -----------------------------------------------------------------
    // wrap_with_iterate
    // -----------------------------------------------------------------

    #[test]
    fn test_wrap_with_iterate_unrefined_list_prepends_trivial_iterate() {
        let mut expr = list_123();
        wrap_with_iterate(&mut expr);
        let head = chain_head(&expr);
        assert!(
            is_iterate_apply(head),
            "expected iterate at chain head, got: {}",
            symbolic(&expr)
        );
        // Trivial predicate => the symbolic shortcut shows just `iterate`.
        assert!(
            symbolic(&expr).starts_with("iterate ≫"),
            "expected trivial-iterate prefix, got: {}",
            symbolic(&expr)
        );
    }

    #[test]
    fn test_wrap_with_iterate_refined_emits_iterate_then_restrict() {
        // Build a refined-domain list: `[1,2,3] : {[0,2] | some_pred} ⇒ Int`.
        // After wrapping, the iteration source is `restrict(some_pred)`
        // *applied* to a chain-head trivially-true `iterate`, with the
        // value-producer `[1, 2, 3]` composed onto it:
        //   (iterate(true) ▷ some_pred ▷ restrict) ≫ [1, 2, 3].
        let int = int_ty();
        let pred = var("some_pred").with_ty(fun_ty(Type::UIntRange(3), bool_ty()));
        let refined_domain = refined_ty(Type::UIntRange(3), pred.clone());

        let mut expr = list_123().with_ty(fun_ty(refined_domain, int));
        wrap_with_iterate(&mut expr);

        let TypedExprNode::Compose(elts) = &expr.node else {
            panic!("expected Compose, got: {}", symbolic(&expr));
        };
        assert_eq!(
            elts.len(),
            2,
            "expected [source, body], got {}: {}",
            elts.len(),
            symbolic(&expr)
        );
        // Chain head is the iteration source: `restrict(some_pred)` applied
        // to the trivially-true `iterate`.
        let upstream = restrict_application_upstream(&elts[0]).unwrap_or_else(|| {
            panic!(
                "expected restrict application at head, got: {}",
                symbolic(&elts[0])
            )
        });
        let TypedExprNode::Apply { argument, function } = &upstream.node else {
            panic!(
                "expected iterate Apply as upstream, got: {}",
                symbolic(upstream)
            );
        };
        assert!(matches!(
            &function.node,
            TypedExprNode::Builtin(Builtin::Iterate)
        ));
        assert!(
            is_trivially_true_predicate(argument),
            "head iterate's predicate should be trivially true, got: {}",
            symbolic(argument)
        );
    }

    #[test]
    fn test_wrap_with_iterate_nested_refinements_emits_chain() {
        // `{{D | p_inner} | p_outer} ⇒ Int` builds the iteration source by
        // *applying* one restrict per refinement layer (inner first) to a
        // chain-head trivially-true iterate, then composes `body` onto it:
        //   restrict(p_outer)(restrict(p_inner)(iterate(true))) ≫ body.
        // So the outermost application narrows by `p_outer`, its upstream
        // narrows by `p_inner`, and the innermost upstream is the iterate.
        let int = int_ty();
        let inner_pred = var("p_inner").with_ty(fun_ty(Type::UIntRange(3), bool_ty()));
        let outer_pred = var("p_outer").with_ty(fun_ty(Type::UIntRange(3), bool_ty()));
        let inner_refined = refined_ty(Type::UIntRange(3), inner_pred);
        let outer_refined = refined_ty(inner_refined, outer_pred);

        let mut expr = list_123().with_ty(fun_ty(outer_refined, int));
        wrap_with_iterate(&mut expr);

        let TypedExprNode::Compose(elts) = &expr.node else {
            panic!("expected Compose, got: {}", symbolic(&expr));
        };
        // [source, body]: the source is the stack of applied restricts.
        assert_eq!(
            elts.len(),
            2,
            "expected [source, body], got {}: {}",
            elts.len(),
            symbolic(&expr)
        );
        // Outermost filter restrict(p_outer); upstream restrict(p_inner);
        // innermost upstream the trivially-true iterate.
        let outer_upstream = restrict_application_upstream(&elts[0])
            .unwrap_or_else(|| panic!("expected outer restrict, got: {}", symbolic(&elts[0])));
        let inner_upstream = restrict_application_upstream(outer_upstream).unwrap_or_else(|| {
            panic!("expected inner restrict, got: {}", symbolic(outer_upstream))
        });
        assert!(
            is_iterate_apply(inner_upstream),
            "innermost upstream should be the trivially-true iterate, got: {}",
            symbolic(inner_upstream)
        );
    }

    #[test]
    fn test_wrap_with_iterate_already_iteration_bearing_is_noop() {
        // Wrapping an `iterate(...)`-led chain leaves it untouched —
        // double-wrap would mean a redundant `IterateExtent` at runtime.
        let pred = trivially_true_predicate(int_ty());
        let mut expr = make_iterate(pred);
        let before = symbolic(&expr);
        wrap_with_iterate(&mut expr);
        assert_eq!(
            symbolic(&expr),
            before,
            "wrapping an already-iterate expression should be a no-op"
        );
    }

    #[test]
    fn test_wrap_with_iterate_recurses_into_let() {
        // For a `Let { bound_expr: list, body: var }`, the helper should
        // descend: wrap the bound list (function-typed) and walk into the
        // body (the function-typed Var is already iteration-bearing, so
        // no wrap there).  Critically, the Let itself is *not* prefixed
        // with iterate — that would force op-conversion's Let arm to
        // feed an unwanted input through to its bound expression.
        let int = int_ty();
        let list_ty = fun_ty(Type::UIntRange(3), int);
        let mut expr = Expr::let_bind(
            "xs".to_string(),
            list_123(),
            var("xs").with_ty(list_ty.clone()),
        )
        .with_ty(list_ty);

        wrap_with_iterate(&mut expr);

        // Outer Let stays as a Let — no wrap inserted at the program root.
        let TypedExprNode::Let {
            bound_expr, body, ..
        } = &expr.node
        else {
            panic!("expected Let to remain at root, got: {}", symbolic(&expr));
        };
        // Bound expression is now iterate-led.
        assert!(
            is_iterate_apply(chain_head(bound_expr)),
            "bound list should be iterate-led, got: {}",
            symbolic(bound_expr)
        );
        // Body is a function-typed Var (iteration-bearing) ⇒ unchanged.
        assert!(matches!(body.node, TypedExprNode::Var(_)));
    }

    #[test]
    fn test_wrap_with_iterate_record_is_noop() {
        // [`wrap_with_iterate`] no-ops on a Record: [`is_iteration_bearing`]
        // returns `true` for Records (they reject `input=Some` and so
        // can't be wrapped without breaking op-conversion), and field
        // wrapping is the responsibility of [`insert_iterate_recurse`]'s
        // value-position `Record` case — that pass walks the AST and
        // wraps function-typed fields wherever a Record appears.
        let int = int_ty();
        let field_ty = fun_ty(Type::UIntRange(3), int.clone());
        let mut expr = Expr::new(TypedExprNode::Record(vec![
            ("xs".to_string(), list_123()),
            (
                "constant".to_string(),
                Expr::lit(Lit::Int(42)).with_ty(int.clone()),
            ),
        ]))
        .with_ty(Type::Record(vec![
            ("xs".to_string(), field_ty),
            ("constant".to_string(), int),
        ]));

        let before = symbolic(&expr);
        wrap_with_iterate(&mut expr);
        assert_eq!(
            symbolic(&expr),
            before,
            "wrap_with_iterate on a Record should be a no-op; insert_iterate_recurse \
             handles field wrapping at the walk site",
        );
    }

    #[test]
    fn test_wrap_with_iterate_scalar_is_noop() {
        // Top-level scalars (e.g. an aggregate result) have no domain
        // to iterate; the helper bails without modifying anything.
        let mut expr = Expr::lit(Lit::Int(5)).with_ty(int_ty());
        let before = symbolic(&expr);
        wrap_with_iterate(&mut expr);
        assert_eq!(symbolic(&expr), before);
    }

    // -----------------------------------------------------------------
    // insert_iterate_recurse
    // -----------------------------------------------------------------

    #[test]
    fn test_insert_iterate_recurse_aggregate_wraps_argument() {
        // `Apply(list, Sum)` — Sum's arm needs an iteration source
        // before the scalar fold, so the argument gets iterate-wrapped.
        let int = int_ty();
        let mut expr = apply_builtin(
            list_123(),
            Builtin::Sum,
            fun_ty(fun_ty(Type::UIntRange(3), int.clone()), int.clone()),
            int,
        );
        insert_iterate_recurse(&mut expr);
        let TypedExprNode::Apply { argument, .. } = &expr.node else {
            panic!("expected Apply, got: {}", symbolic(&expr));
        };
        assert!(
            is_iterate_apply(chain_head(argument)),
            "Sum's argument should be iterate-led, got: {}",
            symbolic(argument)
        );
    }

    #[test]
    fn test_insert_iterate_recurse_converse_wraps_argument() {
        // `Apply(list, Converse)` — Converse compiles its argument
        // under `input=None`, so the argument is an iteration site.
        let int = int_ty();
        let mut expr = apply_builtin(
            list_123(),
            Builtin::Converse,
            fun_ty(
                fun_ty(Type::UIntRange(3), int.clone()),
                fun_ty(int.clone(), fun_ty(Type::UIntRange(3), Type::UIntRange(3))),
            ),
            fun_ty(int, fun_ty(Type::UIntRange(3), Type::UIntRange(3))),
        );
        insert_iterate_recurse(&mut expr);
        let TypedExprNode::Apply { argument, .. } = &expr.node else {
            panic!("expected Apply, got: {}", symbolic(&expr));
        };
        assert!(
            is_iterate_apply(chain_head(argument)),
            "Converse's argument should be iterate-led, got: {}",
            symbolic(argument)
        );
    }

    #[test]
    fn test_insert_iterate_recurse_zip_arg_tuple_left_alone() {
        // `Apply(Tuple(fields), Zip)` — Zip's arm runs the tuple under
        // `input=Some(fan_out_branch)`, so each field receives the
        // surrounding iteration via fan-out and must *not* be wrapped.
        // The catch-all `Apply` walk would otherwise wrap the inner
        // Record/Tuple fields and introduce redundant operators.
        let int = int_ty();
        let proj0 = Expr::proj_index(0).with_ty(fun_ty(
            Type::Tuple(vec![int.clone(), int.clone()]),
            int.clone(),
        ));
        let tuple_arg = Expr::tuple(vec![proj0.clone(), proj0.clone()]).with_ty(Type::Tuple(vec![
            fun_ty(Type::Tuple(vec![int.clone(), int.clone()]), int.clone()),
            fun_ty(Type::Tuple(vec![int.clone(), int.clone()]), int.clone()),
        ]));
        let mut expr = apply_builtin(
            tuple_arg,
            Builtin::Zip,
            fun_ty(
                Type::Tuple(vec![
                    fun_ty(Type::Tuple(vec![int.clone(), int.clone()]), int.clone()),
                    fun_ty(Type::Tuple(vec![int.clone(), int.clone()]), int.clone()),
                ]),
                fun_ty(
                    Type::Tuple(vec![int.clone(), int.clone()]),
                    Type::Tuple(vec![int.clone(), int.clone()]),
                ),
            ),
            fun_ty(
                Type::Tuple(vec![int.clone(), int.clone()]),
                Type::Tuple(vec![int.clone(), int]),
            ),
        );
        let before = symbolic(&expr);
        insert_iterate_recurse(&mut expr);
        assert_eq!(
            symbolic(&expr),
            before,
            "Zip's tuple-argument fields should not get iterate prepended"
        );
    }

    #[test]
    fn test_insert_iterate_recurse_collection_union_wraps_operands() {
        // The value-form `CollectionUnion(operands)` — op-conversion
        // compiles each operand with `input=None`, so each is an
        // iteration site.
        let int = int_ty();
        let mut expr = Expr::new(TypedExprNode::CollectionUnion(vec![list_123(), list_123()]))
            .with_ty(fun_ty(
                Type::Variant(vec![
                    (FieldKey::Index(0), Type::UIntRange(3)),
                    (FieldKey::Index(1), Type::UIntRange(3)),
                ]),
                int,
            ));
        insert_iterate_recurse(&mut expr);
        let TypedExprNode::CollectionUnion(operands) = &expr.node else {
            panic!("expected CollectionUnion, got: {}", symbolic(&expr));
        };
        for (i, operand) in operands.iter().enumerate() {
            assert!(
                is_iterate_apply(chain_head(operand)),
                "operand {i} should be iterate-led, got: {}",
                symbolic(operand)
            );
        }
    }

    #[test]
    fn test_insert_iterate_recurse_loop_wraps_source() {
        // `Loop`'s `source` is iterated by `Recurse` at runtime, and
        // op-conversion compiles it with `input=None` — wrap it here.
        let int = int_ty();
        let list_ty = fun_ty(Type::UIntRange(3), int.clone());
        // Build a minimal Loop with one accumulator and a body that just
        // re-emits the previous accumulator value.  The exact body shape
        // doesn't matter for this test — we're only checking the
        // `source` field gets iterate-wrapped.
        let body = Expr::new(TypedExprNode::Record(vec![(
            "step".to_string(),
            Expr::proj_index(0).with_ty(fun_ty(
                Type::Tuple(vec![int.clone(), int.clone()]),
                int.clone(),
            )),
        )]))
        .with_ty(Type::Record(vec![(
            "step".to_string(),
            fun_ty(Type::Tuple(vec![int.clone(), int.clone()]), int.clone()),
        )]));

        let mut expr = Expr::loop_node(
            vec!["acc".into()],
            vec![Expr::lit(Lit::Int(0)).with_ty(int.clone())],
            list_123().with_ty(list_ty.clone()),
            body,
        )
        .with_ty(list_ty);

        insert_iterate_recurse(&mut expr);

        let TypedExprNode::Loop { source, .. } = &expr.node else {
            panic!("expected Loop, got: {}", symbolic(&expr));
        };
        assert!(
            is_iterate_apply(chain_head(source)),
            "Loop's source should be iterate-led, got: {}",
            symbolic(source)
        );
    }

    #[test]
    fn test_insert_iterate_recurse_record_wraps_function_fields() {
        // Value-position `Record` literal — each function-typed field is
        // an iteration site (op-conversion's `Record` arm compiles each
        // field with `input=None`).
        let int = int_ty();
        let mut expr = Expr::new(TypedExprNode::Record(vec![
            ("xs".to_string(), list_123()),
            ("n".to_string(), Expr::lit(Lit::Int(0)).with_ty(int.clone())),
        ]))
        .with_ty(Type::Record(vec![
            ("xs".to_string(), fun_ty(Type::UIntRange(3), int.clone())),
            ("n".to_string(), int),
        ]));
        insert_iterate_recurse(&mut expr);
        let TypedExprNode::Record(fields) = &expr.node else {
            panic!("expected Record, got: {}", symbolic(&expr));
        };
        let xs = &fields.iter().find(|(n, _)| n == "xs").unwrap().1;
        assert!(
            is_iterate_apply(chain_head(xs)),
            "function-typed field `xs` should be iterate-led, got: {}",
            symbolic(xs)
        );
        let n = &fields.iter().find(|(n, _)| n == "n").unwrap().1;
        assert!(
            matches!(n.node, TypedExprNode::Lit(_)),
            "scalar field `n` should be untouched"
        );
    }

    // -----------------------------------------------------------------
    // End-to-end: insert_iterate_markers
    // -----------------------------------------------------------------

    #[test]
    fn test_insert_iterate_markers_top_level_let_descends_into_bound_and_body() {
        // Full driver pass: a `let xs = [1,2,3] in xs ≫ id` program.  The
        // top-level wrap should reach the bound list (compiled with
        // `input=None` by op-conversion's `Let` arm) and the body's
        // compose head (also `input=None` from the same arm).  The
        // function-typed Var inside the body is already iteration-
        // bearing, so it doesn't get a second wrap.
        let int = int_ty();
        let list_ty = fun_ty(Type::UIntRange(3), int.clone());
        let body_chain = compose(vec![
            var("xs").with_ty(list_ty.clone()),
            Expr::builtin(Builtin::Id).with_ty(fun_ty(int.clone(), int)),
        ])
        .with_ty(list_ty.clone());

        let mut expr = Expr::let_bind("xs".to_string(), list_123(), body_chain).with_ty(list_ty);

        insert_iterate_markers(&mut expr);

        let TypedExprNode::Let {
            bound_expr, body, ..
        } = &expr.node
        else {
            panic!("expected Let, got: {}", symbolic(&expr));
        };
        assert!(
            is_iterate_apply(chain_head(bound_expr)),
            "bound list should be iterate-led, got: {}",
            symbolic(bound_expr)
        );
        // Body's compose head is `Var(xs)` (iteration-bearing) — the
        // pass should leave the compose alone.
        let head = chain_head(body);
        assert!(
            matches!(head.node, TypedExprNode::Var(_)),
            "body's chain head should remain `Var(xs)`, got: {}",
            symbolic(head)
        );
    }

    #[test]
    fn test_insert_iterate_markers_scalar_top_level_only_wraps_aggregate_arg() {
        // `sum([1,2,3])` — the program root is scalar (Int), so no
        // top-level wrap.  The aggregate's argument, however, *is* an
        // iteration site and must be wrapped by the recursive pass.
        let int = int_ty();
        let mut expr = apply_builtin(
            list_123(),
            Builtin::Sum,
            fun_ty(fun_ty(Type::UIntRange(3), int.clone()), int.clone()),
            int,
        );
        insert_iterate_markers(&mut expr);
        let TypedExprNode::Apply { argument, function } = &expr.node else {
            panic!("expected Apply, got: {}", symbolic(&expr));
        };
        // Function position untouched (Sum is still Sum).
        assert!(matches!(
            &function.node,
            TypedExprNode::Builtin(Builtin::Sum)
        ));
        // Argument is iterate-led.
        assert!(
            is_iterate_apply(chain_head(argument)),
            "Sum's argument should be iterate-led, got: {}",
            symbolic(argument)
        );
    }

    #[test]
    fn test_insert_iterate_markers_record_root_wraps_each_function_field() {
        // Programs that end in a sink-bound `Record` — each
        // function-typed field is an iteration site (`compile_program`
        // dispatches to `convert_record_fields_to_operators`, which
        // compiles each field with `input=None`).
        let int = int_ty();
        let field_ty = fun_ty(Type::UIntRange(3), int.clone());
        let mut expr = Expr::new(TypedExprNode::Record(vec![
            ("out_a".to_string(), list_123()),
            ("out_b".to_string(), list_123()),
        ]))
        .with_ty(Type::Record(vec![
            ("out_a".to_string(), field_ty.clone()),
            ("out_b".to_string(), field_ty),
        ]));

        insert_iterate_markers(&mut expr);

        let TypedExprNode::Record(fields) = &expr.node else {
            panic!("expected Record, got: {}", symbolic(&expr));
        };
        for (name, value) in fields {
            assert!(
                is_iterate_apply(chain_head(value)),
                "sink field `{name}` should be iterate-led, got: {}",
                symbolic(value)
            );
        }
    }
}

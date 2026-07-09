//! Iteration-site materialisation walk (design §6.5).
//!
//! [`insert_iterate_markers`] walks the post-lambda-elim CCL and makes every
//! iteration site iteration-bearing, dispatching at each site via
//! [`wrap_with_iterate`] to the hash-join strategy ([`super::join::try_hash_join_rewrite`])
//! when applicable, else the uniform iterate-then-restricts chain.

use std::mem::take;

use super::join::try_hash_join_rewrite;
use super::predicates::{PredMemo, compile_refinement_predicates, fn_of_bare_predicate};
use super::*;

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
pub(crate) fn insert_iterate_markers(expr: &mut Expr) {
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
pub(super) fn insert_iterate_recurse(expr: &mut Expr) {
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
        // Each transaction writer's source is iterated internally by the
        // store engine (`Recurse` for an induction store); op-conversion
        // compiles it with `input=None`, so wrap it like a loop source.
        TypedExprNode::Transact { writers, .. } => {
            for w in writers.iter_mut() {
                wrap_with_iterate(&mut w.source);
            }
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
pub(super) fn builtin_at_function_position(func: &Expr) -> Option<Builtin> {
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
pub(super) fn wrap_with_iterate(expr: &mut Expr) {
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
pub(super) fn is_iteration_bearing(expr: &Expr) -> bool {
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

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::*;
    use crate::ccl::FieldKey;
    use crate::ccl::ccl_utils::is_trivially_true_predicate;
    use crate::ccl::symbolic::symbolic;
    // `super::*` also glob-imports `lambda_elim::compose`; name the test-helper
    // `compose` (`Expr::compose`) explicitly so it wins over the glob.
    use super::super::test_helpers::compose;

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
    fn test_insert_iterate_recurse_transact_wraps_writer_source() {
        use crate::ccl::{TransactKey, TransactWriter};
        // A `Transact` writer's `source` is iterated by the store engine at
        // runtime (op-conversion compiles it with `input=None`), so it must be
        // iterate-wrapped here — the same as a loop source was.
        let int = int_ty();
        let list_ty = fun_ty(Type::UIntRange(3), int.clone());
        // A minimal induction store: one key, one writer whose body is a bare
        // previous-accumulator read.  The exact body shape doesn't matter for
        // this test — we only check the writer `source` gets iterate-wrapped.
        let body = Expr::var("acc").with_ty(int.clone());
        let store_ty = Type::Record(vec![(
            "acc".to_string(),
            fun_ty(Type::UIntRange(3), int.clone()),
        )]);
        let mut expr = Expr::new(TypedExprNode::Transact {
            keys: vec![TransactKey {
                name: "acc".into(),
                init: Expr::lit(Lit::Int(0)).with_ty(int.clone()),
            }],
            writers: vec![TransactWriter {
                read_keys: vec!["acc".into()],
                write_keys: vec!["acc".into()],
                source: list_123().with_ty(list_ty.clone()),
                body,
            }],
            domain: Type::UIntRange(3),
        })
        .with_ty(store_ty);

        insert_iterate_recurse(&mut expr);

        let TypedExprNode::Transact { writers, .. } = &expr.node else {
            panic!("expected Transact, got: {}", symbolic(&expr));
        };
        assert!(
            is_iterate_apply(chain_head(&writers[0].source)),
            "Transact writer source should be iterate-led, got: {}",
            symbolic(&writers[0].source)
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
}

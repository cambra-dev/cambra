//! Miscellaneous utilities for working with CCL.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ccl::{
    BaseType, Builtin, Expr, Lit, Name, PredicateId, Refinement, Type, TypedExprNode,
};

/// Returns `true` if `expr` directly references the given built-in primitive.
pub(crate) fn is_builtin(expr: &Expr, b: Builtin) -> bool {
    matches!(&expr.node, TypedExprNode::Builtin(x) if *x == b)
}

/// Builds an application of a primitive combinator, setting the types based on
/// the input expression's type and the provided output type.
pub fn apply_primitive(expr: Expr, primitive: Builtin, output_ty: Type) -> Expr {
    apply_function(expr, Expr::builtin(primitive), output_ty)
}

/// Builds an application of a function, setting the types based on the input
/// expression's type and the provided output type.
pub fn apply_function(expr: Expr, function: Expr, output_ty: Type) -> Expr {
    let expr_ty = expr.ty.clone();
    Expr::apply(
        expr,
        function.with_ty(Type::fun(expr_ty, output_ty.clone())),
    )
    .with_ty(output_ty)
}

/// Builds a composition of expressions, setting the types based on the input
/// expressions' types. The first expression's domain type is used as the domain type of the
/// composition, and the last expression's codomain type is used as the codomain type of the composition.
pub fn typed_compose(elts: Vec<Expr>) -> Expr {
    let d_ty = elts[0].ty.domain().unwrap().clone();
    let c_ty = elts[elts.len() - 1].ty.codomain().unwrap().clone();
    Expr::compose(elts).with_ty(Type::fun(d_ty, c_ty))
}

/// Construct the trivially-true predicate `λ _ → true` over the given domain,
/// represented in point-free form as `true ▷ const`.
///
/// Returned expression has type `domain ⇒ Bool`.  Used by [`crate::ccl::planning`]
/// when emitting `iterate(pred)` at an unrefined iteration site, and matched by
/// op-conversion via [`is_trivially_true_predicate`] to skip the predicate's filter.
pub fn trivially_true_predicate(domain: Type) -> Expr {
    let bool_ty = Type::Base(BaseType::Bool);
    let true_lit = Expr::lit(Lit::Bool(true)).with_ty(bool_ty.clone());
    apply_primitive(true_lit, Builtin::Const, Type::fun(domain, bool_ty))
}

/// Returns `true` if `expr` is the trivially-true predicate `true ▷ const`
/// (the canonical predicate emitted at unrefined iteration sites by
/// [`crate::ccl::planning`]).
pub fn is_trivially_true_predicate(expr: &Expr) -> bool {
    let TypedExprNode::Apply { argument, function } = &expr.node else {
        return false;
    };
    matches!(&function.node, TypedExprNode::Builtin(Builtin::Const))
        && matches!(&argument.node, TypedExprNode::Lit(Lit::Bool(true)))
}

/// Construct `Apply(predicate, Iterate)`, the chain-head iteration-source
/// marker emitted by [`crate::ccl::planning`] at every iteration site.
/// `predicate` must have type `D ⇒ Bool` (a point-free combinator chain
/// after lambda elimination).
///
/// The result has type `{D | p} ⇒ {D | p}` — `iterate(p)` is the identity
/// on the predicate's refined domain.  As a special case, when `predicate`
/// is the trivially-true predicate (recognised by
/// [`is_trivially_true_predicate`]), the output type degenerates to
/// `D ⇒ D` with no refinement wrapper: the refinement would carry no
/// information, and skipping it keeps program dumps and golden tests
/// free of `{D | true ▷ const}` noise.  The refinement gets a freshly
/// built predicate term — safe because witnesses match by structural
/// predicate equality, while walkers key DAG dedup on the [`PredicateId`].
///
/// Op-conversion compiles `Apply(p, Iterate)` to an `IterateExtent` tile
/// (plus a `Restrict` filter when the predicate is non-trivial).  The
/// Iterate arm requires `input=None` — mid-chain filtering is handled by
/// the separate [`make_restrict`] form.  Refinements are transparent
/// under [`crate::ccl::infer::typecheck`], so the symmetric
/// `{D | p} ⇒ {D | p}` shape composes cleanly against either a refined
/// or unrefined adjacent edge.
pub fn make_iterate(predicate: Expr) -> Expr {
    let domain = predicate
        .ty
        .domain()
        .expect("iterate predicate must have a function type")
        .clone();
    let refined = refine_with(domain, &predicate);
    apply_primitive(
        predicate,
        Builtin::Iterate,
        Type::fun(refined.clone(), refined),
    )
}

/// Construct the mid-chain filter `restrict(p)` **applied to its
/// `upstream` value-producer** — the term `Apply(upstream, Apply(p,
/// Restrict))`.
///
/// `restrict` is a *codomain-parametric function transformer*: given a
/// predicate `p : D ⇒ Bool` it narrows the domain of an upstream
/// `D ⇒ T`, passing the values `T` through unchanged.  So the transformer
/// `Apply(p, Restrict)` has type `(D ⇒ T) ⇒ ({d : D | p(d)} ⇒ T)`, and
/// applying it to `upstream : D ⇒ T` yields `{d : D | p(d)} ⇒ T` — the
/// refinement on the **domain**, the value `T` preserved on the codomain.
///
/// This is application, not composition: `restrict`'s domain is a
/// *function* type, so it cannot sit as a morphism in a CCC `Compose`
/// chain (its honest type makes that ill-typed, and [`typecheck`] now
/// rejects it).  Modelling it as an applied higher-order function is what
/// keeps the emitted term well-typed — see [`crate::ccl::planning`].
///
/// `predicate` must have type `D ⇒ Bool` and `upstream` type `D ⇒ T`
/// (matching domains).  Emitted by [`crate::ccl::planning`] for every
/// filter step downstream of an iteration source — `JoinPlan::Loop` /
/// `JoinPlan::Hash` residual predicates and the outer layers of
/// nested-refinement iteration sites.  Op-conversion compiles it via the
/// generic applied-combinator arm: `upstream` is converted with
/// `input=None`, then the `Restrict` arm consumes it as `input=Some(_)`,
/// compiles the predicate against it, and wraps it in a `Restrict` tile.
/// Chain-head iteration is the separate [`make_iterate`] form.
///
/// [`typecheck`]: crate::ccl::infer::typecheck
pub fn make_restrict(predicate: Expr, upstream: Expr) -> Expr {
    let domain = predicate
        .ty
        .domain()
        .expect("restrict predicate must have a function type")
        .clone();
    let upstream_ty = upstream.ty.clone();
    let value_ty = upstream_ty
        .codomain()
        .expect("restrict upstream must have a function type D ⇒ T")
        .clone();
    let upstream_dom = upstream_ty
        .domain()
        .expect("restrict upstream must have a function type D ⇒ T");
    debug_assert!(
        strip_refinements(&upstream_dom) == strip_refinements(&domain),
        "restrict upstream domain {upstream_dom} must match predicate domain {domain}",
    );
    // `{d : D | p(d)} ⇒ T` — refinement on the domain, value preserved.
    let refined_stream = Type::fun(refine_with(domain, &predicate), value_ty);
    // The transformer node `restrict(p) : (D ⇒ T) ⇒ ({d : D | p(d)} ⇒ T)`.
    let restrict = apply_primitive(
        predicate,
        Builtin::Restrict,
        Type::fun(upstream_ty, refined_stream.clone()),
    );
    apply_function(upstream, restrict, refined_stream)
}

/// Wrap a join morphism `D ⇒ C`'s **codomain** in a refinement carrying
/// `predicate`, yielding `D ⇒ {C | predicate}` (the morphism unchanged when
/// `predicate` is trivially true).
///
/// A hash join consumes its equi-join conditions structurally — into the
/// key-lookup shape, with no residual `Restrict` — so the extent it produces
/// reaches downstream consumers *bare* even though every element it yields
/// satisfies the join condition. A `cast({C | predicate} ⇒ …)` that consumes
/// the extent then sees `C ⊀ {C | predicate}` at the adjacency. Re-stamping
/// the produced codomain with the join condition keeps both sides aligned —
/// this is what a [`make_restrict`] residual does for the loop-join arm, made
/// explicit for the equi-join case that has no residual to carry it.
///
/// A thin wrapper over [`set_codomain`] that refines the existing codomain in
/// place rather than replacing it; see there for how the rewrite is threaded
/// down the combinator's function spine so the post-planning `typecheck`
/// reconstructs it. No runtime node is added (the combinators are type-level).
pub fn refine_codomain(morphism: Expr, bare_predicate: &Expr) -> Expr {
    let codomain = morphism
        .ty
        .codomain()
        .expect("join morphism must be a function type")
        .clone();
    // `bare_predicate` is already the bare `Bool`-over-`__elem` form (the extent's
    // membership condition, the same predicate the body's `cast` demands), so it
    // is stored directly — *not* via `refine_with`, which wraps a predicate
    // *function*. Storing the identical bare term keeps the producer codomain
    // structurally equal to the cast demand.
    let refined = Type::Refinement(
        Box::new(codomain),
        Refinement::born(Rc::new(bare_predicate.clone())),
    );
    set_codomain(morphism, refined)
}

/// Re-stamp a morphism `D ⇒ _`'s codomain to `new_codomain`, yielding
/// `D ⇒ new_codomain`. Used by join planning to surface the refined extent a
/// producer yields (see [`refine_codomain`], and `wrap_with_iterate`'s
/// iteration source, whose codomain is its own refined domain).
///
/// The morphism's result type is the trailing codomain of *every* node on its
/// function spine — `apply_function` records `fun(arg.ty, result)` on the
/// combinator node, and a combinator built by application (`make_restrict` →
/// `Apply(pred, Restrict)`) nests that one level deeper. The Check pass
/// rebuilds an `Apply`'s result from the leaf combinator's recorded type, so
/// the new result must be threaded all the way down the spine, not just onto
/// the outermost node — otherwise the post-planning `typecheck` sees an
/// internally-inconsistent node it cannot reconstruct.
pub fn set_codomain(mut morphism: Expr, new_codomain: Type) -> Expr {
    let domain = morphism
        .ty
        .domain()
        .expect("morphism must be a function type")
        .clone();
    let new_ty = Type::fun(domain, new_codomain);
    // Construction-time contract, not a user error: a non-`Apply` morphism
    // has no spine to restamp, and silently restamping only the outer type
    // would hand the post-planning typecheck an internally-inconsistent node
    // (see the doc comment). Panic in all builds, matching `make_cast`.
    let TypedExprNode::Apply { function, .. } = &mut morphism.node else {
        unreachable!("set_codomain: morphism must be an applied combinator");
    };
    restamp_spine_result(function, new_ty.clone());
    morphism.ty = new_ty;
    morphism
}

/// Re-stamp a combinator-node's recorded type so its codomain becomes
/// `new_result` (the rewritten morphism type), recursing down the function
/// spine of an applied combinator so the leaf builtin — which the Check pass
/// rebuilds from — agrees. See [`set_codomain`].
fn restamp_spine_result(node: &mut Expr, new_result: Type) {
    let domain = node
        .ty
        .domain()
        .expect("combinator node must be a function type")
        .clone();
    let new_ty = Type::fun(domain, new_result);
    if let TypedExprNode::Apply { function, .. } = &mut node.node {
        restamp_spine_result(function, new_ty.clone());
    }
    node.ty = new_ty;
}

/// Construct a [`TypedExprNode::Cast`], a pure type-level assertion that
/// re-views `value` under `target_ty`.
///
/// `cast` is an upcast: [`crate::ccl::infer`]'s `Cast` arm types it
/// by the single obligation `value_ty <: target_ty`.
///
/// Op-conversion treats `cast` as a no-op — see [`TypedExprNode::Cast`] — so
/// this is purely a type-level coercion with no runtime cost.
///
/// **Temporary shape contract:** `target_ty` must be
/// `Fun(Refinement(_, _), _)` — a refinement on a function domain.  Inference
/// no longer *requires* this (any `target` with `value_ty <: target` is a
/// well-typed upcast), but it is the only shape lowering produces today and
/// the one [`crate::ccl::lambda_elim`]'s groupby reconstruction reads a witness
/// off of, so this asserts the lowering contract: a non-conforming target is
/// a construction-time bug, not a user error, so it panics rather than
/// emitting a cast `lambda_elim` would mishandle.  See [`TypedExprNode::Cast`]
/// for the migration plan toward a general `𝑈 ⇒ 𝑇` cast.
/// TODO remove this constraint once we get rid of the special-casing correlated
/// refinement code in lambda_elim.
pub fn make_cast(value: Expr, target_ty: Type) -> Expr {
    assert!(
        matches!(&target_ty, Type::Fun { domain: d, .. } if matches!(d.as_ref(), Type::Refinement(..))),
        "make_cast target_ty must be Fun(Refinement(_, _), _), got {target_ty}"
    );
    Expr::cast(value, target_ty)
}

/// Read the domain refinement off a cast target type — the refinement witness a
/// [`make_cast`] target carries on its `Fun(Refinement(_, r), _)` shape.
///
/// [`crate::ccl::lambda_elim`]'s cast-wrapped-lambda arm calls this on a
/// [`TypedExprNode::Cast`]'s `target` to reattach the refinement to the
/// reconstructed `groupby` lambda.  (Inference does not need it: it types the
/// cast as the upcast `value_ty <: target` and lets the solver carry the
/// witness.) The returned `Refinement` shares the predicate's `Rc<Expr>` with
/// `target`.
pub fn cast_target_refinement(target: &Type) -> Option<Refinement> {
    let Type::Fun { domain, .. } = target else {
        return None;
    };
    let Type::Refinement(_, refinement) = domain.as_ref() else {
        return None;
    };
    Some(refinement.clone())
}

/// Build a function type whose domain is `base_domain` wrapped in a fresh
/// `Type::Refinement` carrying `predicate`, and whose codomain is `codomain`.
///
/// Used by lowering to build the target type for a [`make_cast`] that
/// imposes a refinement on a function's domain (the canonical shape produced
/// by list-comp filters, for-loop `if`-guards, and `groupby`). `predicate` is
/// a **bare** boolean expression in which [`crate::ccl::REFINEMENT_BINDER`] is free (the
/// element being filtered) — not a lambda.
///
/// `base_domain` and `codomain` are typically `Type::Hole` at lowering time;
/// inference fills them in by unifying against the value being cast.
pub fn refined_fn_type(base_domain: Type, predicate: Expr, codomain: Type) -> Type {
    Type::fun(
        Type::Refinement(Box::new(base_domain), Refinement::born(Rc::new(predicate))),
        codomain,
    )
}

/// A structural copy of `ty` with every [`Type::Refinement`] layer removed,
/// at any depth (inside tuples / records / function types).  Used to compare
/// domains up to refinements (which are transparent to structural shape) —
/// the two sides may carry the same predicate at different compilation stages
/// (bare `__elem ▷ p` before vs after planning normalizes `p` to point-free),
/// so refinements must not participate in the comparison at any depth.
pub(crate) fn strip_refinements(ty: &Type) -> Type {
    match ty {
        Type::Refinement(base, _) => strip_refinements(base),
        Type::Fun {
            name,
            domain,
            codomain,
        } => Type::Fun {
            name: name.clone(),
            domain: Box::new(strip_refinements(domain)),
            codomain: Box::new(strip_refinements(codomain)),
        },
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(strip_refinements).collect()),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), strip_refinements(t)))
                .collect(),
        ),
        Type::Variant(tags) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), strip_refinements(t)))
                .collect(),
        ),
        Type::History {
            value,
            domain,
            kind,
        } => Type::History {
            value: Box::new(strip_refinements(value)),
            domain: Box::new(strip_refinements(domain)),
            kind: *kind,
        },
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::Hole
        | Type::Infer(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn => ty.clone(),
    }
}

/// The **bare** boolean form of a point-free predicate function `p : D ⇒ Bool`:
/// the application `__elem ▷ p` (`= p(__elem)`), in which the implicit
/// [`crate::ccl::REFINEMENT_BINDER`] (typed at the element type `base`) stands for the
/// element. This is the one shape a [`Refinement`] ever stores — a function `p`
/// lives only in a *term* (an `Apply(p, Iterate/Restrict)` argument), never in a
/// refinement type. `planning::fn_of_bare_predicate` is the inverse.
pub fn bare_predicate_of_fn(base: &Type, predicate: Expr) -> Expr {
    let elem = Expr::var(Name::elem()).with_ty(base.clone());
    Expr::apply(elem, predicate).with_ty(Type::Base(BaseType::Bool))
}

/// Re-point every [`TypedExprNode::Cast`]'s `target` type slot at the cast
/// node's own `expr.ty`. A cast's recorded type *is* its target type, so the
/// two are equal by construction — but the `target` carries its **own**
/// immutable refinement-predicate `Rc`, and a predicate-rewriting pass
/// (inlining's beta step, lambda elimination, planning's point-free
/// compilation) rebuilds the predicate on `expr.ty` without touching `target`,
/// so they drift apart. The post-pass `typecheck` reconstructs a cast from its
/// `target` ([`cast_target_refinement`]) and compares against the recorded
/// `expr.ty`; re-syncing after each such pass keeps that match exact.
pub fn sync_cast_targets(expr: &mut Expr) {
    if matches!(expr.node, TypedExprNode::Cast { .. }) {
        let ty = expr.ty.clone();
        if let TypedExprNode::Cast { target, .. } = &mut expr.node {
            *target = ty;
        }
    }
    expr.walk_children_mut(sync_cast_targets);
}

/// Wrap `base` in a fresh `Type::Refinement` whose bare predicate filters the
/// element by the point-free function `predicate : base ⇒ Bool` (stored as
/// `__elem ▷ predicate`, see [`bare_predicate_of_fn`]). Returns `base` unchanged
/// when the predicate is trivially true.
fn refine_with(base: Type, predicate: &Expr) -> Type {
    if is_trivially_true_predicate(predicate) {
        return base;
    }
    let bare = bare_predicate_of_fn(&base, predicate.clone());
    Type::Refinement(Box::new(base), Refinement::born(Rc::new(bare)))
}

/// Count free occurrences of `name` in `expr`, including occurrences in
/// any refinement predicates carried by the expression's type.
///
/// A variable is *free* at a use site when no enclosing
/// [`TypedExprNode::Lambda`] or [`TypedExprNode::Let`] inside `expr`
/// shadows the name on the path to that use; the count is the number of
/// such free uses.  [`TypedExprNode::Feed`] / [`TypedExprNode::Define`]
/// nodes treat their `name` field as a use of the defer-handle variable,
/// so writes to that defer count as occurrences too.
///
/// A [`Type::Refinement`] is a binding form too — it binds
/// [`crate::ccl::REFINEMENT_BINDER`] (`__elem`) in its predicate — so occurrences
/// of that one name inside a type are **bound, never free** (see
/// [`is_free_in_type`]). Every other name in a predicate is a free reference to
/// the enclosing lexical scope and is counted.
///
/// Used by:
/// - [`is_free`] — the bool wrapper for "does `name` appear at all?"
/// - [`crate::ccl::channelize`] — to detect when a defer's value
///   references another defer in the same cluster, and to decide
///   whether feed values reference other channels (cluster membership).
/// - [`crate::ccl::lambda_elim`] — to decide whether a lambda's body
///   captures its parameter (`const`-lift if not) and to test refinement
///   predicate occurrences for the let-in-lambda hoisting rules.
pub fn count_free(name: &Name, expr: &Expr) -> usize {
    count_free_with_visited(name, expr, &mut HashSet::new())
}

/// Recursive worker for [`count_free`].  Threads a `visited` set of
/// already-walked predicate terms ([`PredicateId`]) so that
/// self-referential refinements (a Lambda param `xs` whose type contains a
/// refinement whose predicate references `xs`) terminate cleanly.  Each
/// predicate term is walked at most once per top-level [`count_free`] call —
/// its free-var count is collected on first encounter and short-circuited on
/// subsequent encounters.
fn count_free_with_visited(name: &Name, expr: &Expr, visited: &mut HashSet<PredicateId>) -> usize {
    // Every type slot the node carries counts, via the same
    // [`Expr::walk_type_slots`] the rewriting passes use. Getting this set wrong
    // is not a cosmetic under-count: several passes *skip work* when `is_free`
    // says no (`inline_in_type_predicates`' early return, `subst`'s inert-subtree
    // and vacuous-predicate checks), so a slot this walk cannot see is a slot
    // those passes silently decline to rewrite. Enumerating it here by hand is how
    // it fell out of step with `walk_type_slots` in the first place.
    //
    // A binder's declared type is in the *enclosing* scope — a binder does not
    // bind in its own type — so occurrences there are unshadowed and count, which
    // is why this runs before the shadowing logic below. Occurrences are
    // deduplicated by `visited`, so a predicate riding both a binder slot and the
    // matching position of `expr.ty` (the usual case, and increasingly so as
    // sharing improves) is still counted once.
    let mut in_type = 0;
    expr.walk_type_slots(|ty| in_type += count_free_in_type_with_visited(name, ty, visited));
    let in_node = match &expr.node {
        TypedExprNode::Var(n) => (n == name) as usize,

        TypedExprNode::Lambda { param, body } => {
            // Domain refinements ride the type lattice, so any free
            // occurrences in a refinement predicate are counted by
            // `count_free_in_type_with_visited` on `expr.ty` above (and live
            // in the *outer* scope, unshadowed). Here `param.name` shadows
            // `name` inside the lambda body.
            if &param.name == name {
                0
            } else {
                count_free_with_visited(name, body, visited)
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // `binding.name` shadows `name` inside `body` only.
            count_free_with_visited(name, bound_expr, visited)
                + if &binding.name == name {
                    0
                } else {
                    count_free_with_visited(name, body, visited)
                }
        }

        // Mutual recursion: every group binder scopes every binding body
        // and the letrec body, so a group binder matching `name` shadows it
        // across the whole group.
        TypedExprNode::LetRec { bindings, body } => {
            if bindings.iter().any(|(b, _)| &b.name == name) {
                0
            } else {
                bindings
                    .iter()
                    .map(|(_, def)| count_free_with_visited(name, def, visited))
                    .sum::<usize>()
                    + count_free_with_visited(name, body, visited)
            }
        }

        // The `name` field of Feed/Define/MutWrite is a *use* of the defer
        // handle / mutable variable — `Feed("x", v)` (and `x := v`) is a
        // write to `x`, so `x` is free here in addition to any free uses
        // inside `value`.
        TypedExprNode::Feed {
            name: handle,
            value,
        }
        | TypedExprNode::Define {
            name: handle,
            value,
        }
        | TypedExprNode::MutWrite {
            name: handle,
            value,
        } => (handle == name) as usize + count_free_with_visited(name, value, visited),

        // The loop target shadows `name` inside the body only; the source
        // is evaluated in the outer scope.
        TypedExprNode::For { target, iter, body } => {
            count_free_with_visited(name, iter, visited)
                + if &target.name == name {
                    0
                } else {
                    count_free_with_visited(name, body, visited)
                }
        }

        // A `Case` branch's structural pattern binds its payload name,
        // shadowing `name` inside that branch's guard and body.
        // `walk_children` only visits child Exprs and can't see that
        // `pattern.binding.name` shadows `name`, so it would over-count
        // free occurrences in shadowing branches. Handle `Case` explicitly.
        // (Guard-only branches have `pattern: None` and never shadow.)
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            let scrut = scrutinee
                .as_ref()
                .map_or(0, |s| count_free_with_visited(name, s, visited));
            scrut
                + branches
                    .iter()
                    .map(|b| {
                        if b.pattern.as_ref().is_some_and(|p| &p.binding.name == name) {
                            0
                        } else {
                            count_free_with_visited(name, &b.guard, visited)
                                + count_free_with_visited(name, &b.body, visited)
                        }
                    })
                    .sum::<usize>()
        }

        // VariantCtor payload and all other variants: just sum counts
        // across the direct children.  Atoms (Lit/Proj/Builtin/Source/
        // Defer) have no children, so the fold returns 0.
        _ => {
            let mut sum = 0;
            expr.walk_children(|e| sum += count_free_with_visited(name, e, visited));
            sum
        }
    };
    in_node + in_type
}

/// Returns `true` if `name` appears free anywhere in `expr` — either in
/// the AST itself or inside a refinement predicate on its type.
///
/// Thin wrapper around [`count_free`]; see that function for the exact
/// shadowing rules.
pub fn is_free(name: &Name, expr: &Expr) -> bool {
    count_free(name, expr) > 0
}

/// Like [`is_free`] but considers only the **value** (the node tree), ignoring
/// type slots — whether `name` occurs free in `expr`'s term structure, *not* in
/// any refinement predicate riding its types.
///
/// Lambda elimination uses this to distinguish a binder used in the value (which
/// needs real point-free elimination) from one free only in a refinement on the
/// body's type. The latter is the **Pi-const** case: the value is a `const` and
/// the binder rides the type as a Pi binder (a dependent refinement), e.g. after
/// pairing rewrites a partition predicate onto a pair domain.
pub fn is_free_in_value(name: &Name, expr: &Expr) -> bool {
    count_free_in_value(name, expr) > 0
}

/// Value-only worker for [`is_free_in_value`]: mirrors [`count_free`]'s
/// shadowing rules over the node tree but never descends into type slots (and so
/// a refinement on a `Lambda` param — which lives in the type — is ignored).
fn count_free_in_value(name: &Name, expr: &Expr) -> usize {
    match &expr.node {
        TypedExprNode::Var(n) => (n == name) as usize,
        TypedExprNode::Lambda { param, body, .. } => {
            if &param.name == name {
                0
            } else {
                count_free_in_value(name, body)
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            count_free_in_value(name, bound_expr)
                + if &binding.name == name {
                    0
                } else {
                    count_free_in_value(name, body)
                }
        }
        // See the LetRec arm of `count_free_with_visited`: group binders
        // shadow `name` across every binding body and the letrec body.
        TypedExprNode::LetRec { bindings, body } => {
            if bindings.iter().any(|(b, _)| &b.name == name) {
                0
            } else {
                bindings
                    .iter()
                    .map(|(_, def)| count_free_in_value(name, def))
                    .sum::<usize>()
                    + count_free_in_value(name, body)
            }
        }
        TypedExprNode::Feed {
            name: handle,
            value,
        }
        | TypedExprNode::Define {
            name: handle,
            value,
        }
        | TypedExprNode::MutWrite {
            name: handle,
            value,
        } => (handle == name) as usize + count_free_in_value(name, value),
        // The loop target shadows `name` in the body only.
        TypedExprNode::For { target, iter, body } => {
            count_free_in_value(name, iter)
                + if &target.name == name {
                    0
                } else {
                    count_free_in_value(name, body)
                }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            scrutinee
                .as_ref()
                .map_or(0, |s| count_free_in_value(name, s))
                + branches
                    .iter()
                    .map(|b| {
                        if b.pattern.as_ref().is_some_and(|p| &p.binding.name == name) {
                            0
                        } else {
                            count_free_in_value(name, &b.guard) + count_free_in_value(name, &b.body)
                        }
                    })
                    .sum::<usize>()
        }
        _ => {
            let mut sum = 0;
            expr.walk_children(|e| sum += count_free_in_value(name, e));
            sum
        }
    }
}

/// Returns `true` if `name` appears free inside a refinement predicate
/// reachable from `ty` (walking every [`Type::Refinement`] layer, including
/// nested ones in `Fun`/`Tuple`/`Record`/`Variant` positions).
///
/// This is the *type-position* counterpart to [`is_free`]: it ignores the
/// term spine entirely and only inspects predicates carried by the type. Use
/// it to detect when a term substitution would need to reach into a
/// type-carried predicate (e.g. a `cast`-introduced domain refinement that
/// closes over the substituted variable).
///
/// **Always `false` for [`crate::ccl::REFINEMENT_BINDER`]** — a type's only
/// binding form is the refinement, and every `__elem` occurrence sits under the
/// refinement that binds it, so the element binder is never a free reference to
/// anything a substitution could supply.
pub fn is_free_in_type(name: &Name, ty: &Type) -> bool {
    count_free_in_type_with_visited(name, ty, &mut HashSet::new()) > 0
}

/// Recursive worker for the type-walking side of [`count_free`].  The
/// `visited` set ([`walk_refined_predicates`]) dedups a predicate term shared
/// by `Rc` across occurrences — counted once, matching the by-`Rc` dedup the
/// substitute-vs-preserve decision keys on.
fn count_free_in_type_with_visited(
    name: &Name,
    ty: &Type,
    visited: &mut HashSet<PredicateId>,
) -> usize {
    // The only variable a type can bind is the refinement element binder
    // ([`crate::ccl::REFINEMENT_BINDER`]): it occurs *only* inside refinement
    // predicates, and each such occurrence is bound by its enclosing refinement —
    // including under nesting, where each layer binds its own. So it is never free
    // in a type: counting its (bound) occurrences reports a binder capture that
    // cannot happen, and the caller that asks (lambda-elim's "value-dependent
    // dependent function" guard) then rejects a perfectly ordinary term because
    // some type inside it carried an `__elem` predicate. Every *other* name in a
    // predicate is a free reference to the enclosing lexical scope and is counted.
    //
    // The carve-out is type-level only: the *term* walk
    // ([`count_free_with_visited`]) deliberately keeps counting `__elem`, because a
    // bare predicate manipulated as a term — eta-expanded by
    // `planning::fn_of_bare_predicate`, say — genuinely has it free until that
    // expansion binds it.
    if name.is_elem() {
        return 0;
    }
    let mut count = 0;
    walk_refined_predicates(ty, visited, &mut |pred, vis| {
        count += count_free_with_visited(name, pred, vis);
    });
    count
}

/// Walk every [`Type::Refinement`] reachable from `ty` and invoke `f`
/// on its predicate expression by *shared* reference.  Each predicate
/// is visited at most once per call (keyed by [`PredicateId`] in
/// `visited`) — a predicate term may be shared by `Rc` across several
/// occurrences (a refinement's predicate has type slots that surface the
/// same refinement), so this dedups the DAG. (Immutable predicates cannot
/// form a cycle, so this is dedup, not cycle-breaking.)
///
/// The callback receives `visited` so it can recurse back into
/// [`walk_refined_predicates`] when the predicate's own subexpressions
/// carry types that contain further refinements.
///
/// This helper is the single source of truth for the
/// type-walk + visited-set pattern used by
/// [`count_free_in_type_with_visited`], [`crate::ccl::infer::check_fully_typed`],
/// and [`crate::ccl::lambda_elim`]'s post-pass type-refinement walk.
/// See [`walk_refined_predicates_mut`] for the rebuilding variant used by
/// [`crate::ccl::inline`].
pub fn walk_refined_predicates<F>(ty: &Type, visited: &mut HashSet<PredicateId>, f: &mut F)
where
    F: FnMut(&Expr, &mut HashSet<PredicateId>),
{
    if let Type::Refinement(_, refinement) = ty
        && visited.insert(refinement.predicate_id())
    {
        f(&refinement.predicate, visited);
    }
    ty.walk_children(|child| walk_refined_predicates(child, visited, f));
}

/// Pass-scoped memo that **preserves refinement-predicate `Rc` sharing** across
/// a single rebuild pass.
///
/// Predicates are immutable `Rc<TypedExpr>`s (see [`Refinement::predicate`]), so
/// any pass that must "update" a predicate — resolve embedded inference vars
/// (`coalesce`), restamp binder types (`retype`), eliminate lambdas
/// (`lambda_elim`), simplify, or substitute — *rebuilds* it into a fresh `Rc`
/// rather than mutating in place. When one predicate term rides several type
/// slots as a shared `Rc` (a comprehension's filtered domain appears on its
/// source, map, cast, and consumer-contract types), rebuilding each occurrence
/// independently **splits** that sharing. The split is invisible to correctness
/// — the rebuilds are value-equal (refinement equality is structural) — but it
/// defeats every downstream `Rc`-identity dedup: `Rc::ptr_eq` fast paths and, in
/// particular, planning's per-predicate compile memo, which then recompiles one
/// predicate once per occurrence (superlinearly, on nested comprehensions).
///
/// This memo re-points every occurrence that entered a pass sharing one origin
/// `Rc` at a *single* rebuilt `Rc`, so sharing survives the pass. It is the one
/// mechanism every predicate-rebuilding pass threads; the alternative —
/// reunifying afterward by structural hash/eq — would reintroduce exactly the
/// per-predicate hashing cost the `Rc` boxing exists to avoid.
///
/// **The memo must be pass-scoped.** One instance threaded across the *whole*
/// tree walk of a pass. A fresh memo per node/subtree re-shares only within that
/// node and still splits across the tree — the exact bug this type prevents.
/// The sharing invariant is guarded end-to-end by `tests/predicate_sharing.rs`
/// and, per phase, by asserting [`distinct_predicate_rcs`] does not grow across
/// a transform-only pass.
///
/// Keyed on [`PredicateId`] (the origin `Rc`'s address). Sound only while that
/// address cannot be reused during the pass, which the [`Origin`] token
/// guarantees: every entry retains its origin `Rc` for the memo's lifetime.
/// Without that, overwriting a `refinement.predicate` could drop the origin
/// `Rc`, freeing an address a later `Rc::new` in the same pass could reclaim, so
/// an unrelated predicate landing there would collide and inherit this entry's
/// rebuild. This is why a pass uses `PredMemo` rather than a bare map — the
/// keepalive is not optional bookkeeping.
///
/// # Key-determined vs context-determined transforms
///
/// The key is the predicate `Rc`'s address **and nothing else**, so *reusing* an
/// earlier occurrence's result is only sound for a transform that is a function
/// of the predicate term. Passes divide on this, and the division decides which
/// protocol below they use:
///
/// - **Key-determined** — [`begin`](Self::begin) + [`finish`](Self::finish). The
///   result depends on the term plus context that is invariant across the
///   occurrences sharing it: `uniquify`, `coalesce` (whose predicates resolve out
///   of one live constraint graph, so two occurrences of one term resolve
///   identically), `retype`, `simplify`, `inline` and `subst` *within one active
///   substitution*. A hit skips the transform.
/// - **Context-determined** — [`begin_always`](Self::begin_always) +
///   [`finish_shared`](Self::finish_shared). The result depends on something the
///   key does not name, so the transform **must run at every occurrence**; only
///   the resulting *term* is unified. Constraint emission is the case: it binds
///   `REFINEMENT_BINDER` to a domain supplied per occurrence, and skipping it
///   would leave that occurrence's domain without the constraints the predicate
///   imposes on it.
///
/// A third shape is neither: when the context is *part of the transform's
/// identity* rather than a parameter of it — `subst`'s active substitution, which
/// by design acts differently in different scopes — the fix is to scope the memo
/// so the context is constant within it, rather than to widen the key. See
/// `subst::rewrite_type_go`.
///
/// Mixing them up is a silent wrong answer, not a compile error, which is why the
/// two protocols are named rather than left as one.
#[derive(Default)]
pub struct PredMemo {
    entries: HashMap<PredicateId, (Rc<Expr>, Rc<Expr>)>,
    /// Bumped whenever a predicate slot is pointed at a *different* `Rc`. Lets
    /// [`walk_refined_predicates_mut`] observe re-pointings performed inside a
    /// callback's own recursion — which the callback's `changed` bit cannot
    /// report, because a nested memo *hit* mutates the callback's copy without
    /// the callback doing anything. See [`Self::revision`].
    revision: u64,
}

/// A predicate's **origin** `Rc`, captured before its slot was overwritten —
/// the memo key, and the keepalive pinning that key's address.
///
/// Only [`PredMemo::begin`] / [`PredMemo::begin_always`] mint one, and only the
/// `finish*` methods consume one, so it cannot be confused with a rebuild: the
/// "did you pass the origin or the rebuild?" mistake the raw `record(Rc, Rc)`
/// shape invited is not expressible.
///
/// **An opened rebuild must be closed.** Dropping the token instead of passing it
/// to a `finish*` is silent and lossy, not merely wasteful: the caller's transform
/// result is discarded, the slot keeps its origin `Rc`, and nothing is memoized —
/// so a pass that opened a rebuild and then returned early (a `?` between the two
/// halves) leaves that occurrence un-rewritten while its siblings are rewritten.
/// The `#[must_use]` on the opening methods catches ignoring the token; this
/// type's `Drop` catches losing it on an early return.
pub struct Origin(Option<Rc<Expr>>);

impl Origin {
    /// The retained origin `Rc`, defusing the drop check — the `finish*` methods'
    /// single exit.
    fn consume(mut self) -> Rc<Expr> {
        self.0.take().expect("an Origin is consumed exactly once")
    }

    /// The origin `Rc` without consuming the token.
    fn peek(&self) -> &Rc<Expr> {
        self.0.as_ref().expect("an Origin is consumed exactly once")
    }
}

impl Drop for Origin {
    fn drop(&mut self) {
        // Unwinding already: a second panic from a destructor aborts the process,
        // which would bury the original failure.
        if std::thread::panicking() {
            return;
        }
        debug_assert!(
            self.0.is_none(),
            "a `PredMemo` rebuild was opened and never finished: the transform's result is \
             discarded, the occurrence silently keeps its origin `Rc`, and nothing is \
             memoized. Every `begin`/`begin_always` must reach a `finish`, \
             `finish_shared`, or `finish_unchanged` — including on error paths."
        );
    }
}

impl PredMemo {
    pub fn new() -> Self {
        Self::default()
    }

    /// Open a rebuild of `refinement`'s predicate.
    ///
    /// On a **hit** — an occurrence sharing this origin `Rc` was already rebuilt
    /// in this pass — re-points `refinement` at that single rebuild and returns
    /// `None`: sharing preserved, transform skipped. On a **miss**, returns the
    /// [`Origin`] token together with a mutable copy for the caller to transform,
    /// to be handed back to [`finish`](Self::finish) (or
    /// [`finish_unchanged`](Self::finish_unchanged)).
    ///
    /// The copy is owned, so the caller holds **no** borrow of the memo across
    /// its own transform — which is what lets a pass whose transform needs
    /// `&mut Ctx` (with the memo living in that `Ctx`) drive this protocol
    /// without a borrow conflict.
    #[must_use = "an opened rebuild must be closed with a `finish*` — see `Origin`"]
    pub fn begin(&mut self, refinement: &mut Refinement) -> Option<(Origin, Expr)> {
        if let Some((_, rebuilt)) = self.entries.get(&refinement.predicate_id()) {
            let rebuilt = Rc::clone(rebuilt);
            self.point_at(refinement, rebuilt);
            return None;
        }
        Some(self.open(refinement))
    }

    /// Open a rebuild for a **context-determined** transform: one whose result
    /// depends on something the memo key does not name, so it must run at *every*
    /// occurrence. Always returns the [`Origin`] token and a copy — there is no
    /// skip — to be closed with [`finish_shared`](Self::finish_shared), which
    /// unifies the term while leaving the per-occurrence work already done.
    #[must_use = "an opened rebuild must be closed with a `finish*` — see `Origin`"]
    pub fn begin_always(&self, refinement: &Refinement) -> (Origin, Expr) {
        self.open(refinement)
    }

    /// Close a rebuild: install `rebuilt` into `refinement` and record
    /// `origin ↦ rebuilt`, so every later occurrence sharing `origin` is
    /// re-pointed at this same term.
    pub fn finish(&mut self, refinement: &mut Refinement, origin: Origin, rebuilt: Expr) {
        let rebuilt = Rc::new(rebuilt);
        self.point_at(refinement, Rc::clone(&rebuilt));
        self.insert(origin, rebuilt);
    }

    /// Close a [`begin_always`](Self::begin_always) rebuild: point the slot at the
    /// term an earlier occurrence produced if there is one, otherwise record this
    /// occurrence's `rebuilt` as that shared term.
    ///
    /// The caller's transform has already run — that is the whole point — so this
    /// only decides *which* term the occurrences share. Discarding `rebuilt` on a
    /// hit is safe precisely because refinement identity is type-blind: the
    /// occurrences denote one refinement, and the winning term's embedded type
    /// slots are as good as the discarded one's.
    pub fn finish_shared(&mut self, refinement: &mut Refinement, origin: Origin, rebuilt: Expr) {
        match self.entries.get(&Rc::as_ptr(origin.peek())) {
            Some((_, shared)) => {
                let shared = Rc::clone(shared);
                self.point_at(refinement, shared);
                // The entry already retains its own keepalive for this key, so
                // this token has nothing left to record — but it still has to be
                // consumed rather than dropped (see `Origin`).
                drop(origin.consume());
            }
            None => self.finish(refinement, origin, rebuilt),
        }
    }

    /// Close a rebuild the transform left **untouched**: keep the origin `Rc` in
    /// the slot and record `origin ↦ origin`.
    ///
    /// This is strictly better than rebuilding an identical term. It preserves
    /// sharing a pass *already* had rather than re-establishing it (a predicate a
    /// pass merely walks past is never reallocated, so occurrences it never
    /// visits stay pointer-equal to ones it did), and it turns the caller's
    /// "would this transform do anything?" test — `subst`'s `is_free` scan, say —
    /// from once per *occurrence* into once per distinct predicate.
    pub fn finish_unchanged(&mut self, refinement: &mut Refinement, origin: Origin) {
        let kept = Rc::clone(origin.peek());
        self.point_at(refinement, Rc::clone(&kept));
        self.insert(origin, kept);
    }

    /// A counter that advances every time this memo points some predicate slot at
    /// a *different* `Rc`.
    ///
    /// [`walk_refined_predicates_mut`] brackets its callback with this to learn
    /// whether the copy it handed over was mutated by the memo itself — a nested
    /// memo *hit* re-points a slot inside that copy without the callback doing
    /// anything, so the callback's own `changed` bit cannot report it. Comparing
    /// revisions is exact for that question and costs one integer.
    pub fn revision(&self) -> u64 {
        self.revision
    }

    /// Point `refinement` at `to`, counting it as a re-pointing when the `Rc`
    /// actually changes (see [`revision`](Self::revision)).
    fn point_at(&mut self, refinement: &mut Refinement, to: Rc<Expr>) {
        if !Rc::ptr_eq(&refinement.predicate, &to) {
            self.revision += 1;
        }
        refinement.predicate = to;
    }

    /// Mint the [`Origin`] token and the working copy for a miss.
    fn open(&self, refinement: &Refinement) -> (Origin, Expr) {
        (
            Origin(Some(Rc::clone(&refinement.predicate))),
            (*refinement.predicate).clone(),
        )
    }

    /// Retain `origin` as the keepalive pinning its address for the memo's
    /// lifetime (see the type-level note on address reuse) while mapping it to
    /// `rebuilt`.
    fn insert(&mut self, origin: Origin, rebuilt: Rc<Expr>) {
        let origin = origin.consume();
        self.entries.insert(Rc::as_ptr(&origin), (origin, rebuilt));
    }
}

/// Every refinement reachable from `expr`'s type slots, one entry per distinct
/// predicate `Rc`, in walk order. Coverage is [`Expr::walk_type_slots`]' — every
/// node's `ty`, `user_annotation`, `Cast` target, and binder-declared types — so
/// a refinement riding *only* a binder slot or a cast target (where a
/// comprehension filter's predicate lives) is reached.
///
/// Deduplicated by [`PredicateId`], so occurrences sharing one `Rc` yield one
/// entry: the result's length is the sharing metric ([`distinct_predicate_rcs`]),
/// while [`Refinement`]'s own structural `PartialEq` lets a caller ask the
/// sharper question — whether two of those *distinct* `Rc`s denote the same
/// refinement, i.e. whether sharing was split (see `tests/predicate_sharing.rs`).
pub fn reachable_refinements(expr: &Expr) -> Vec<Refinement> {
    fn in_type(ty: &Type, out: &mut Vec<Refinement>, seen: &mut HashSet<PredicateId>) {
        if let Type::Refinement(_, r) = ty
            && seen.insert(r.predicate_id())
        {
            out.push(r.clone());
            // A predicate's own subexpressions carry further refinements.
            in_expr(&r.predicate, out, seen);
        }
        ty.walk_children(|c| in_type(c, out, seen));
    }
    fn in_expr(e: &Expr, out: &mut Vec<Refinement>, seen: &mut HashSet<PredicateId>) {
        e.walk_type_slots(|ty| in_type(ty, out, seen));
        e.walk_children(|c| in_expr(c, out, seen));
    }
    let mut out = Vec::new();
    in_expr(expr, &mut out, &mut HashSet::new());
    out
}

/// Count the **distinct** refinement-predicate `Rc`s reachable from `expr`'s
/// type slots ([`reachable_refinements`]). Pure address-set arithmetic — no
/// structural hashing — so it is cheap enough for a `debug_assert!` guard.
///
/// This is the per-phase sharing check: a *sharing-preserving* transform maps N
/// distinct origin predicate `Rc`s to ≤ N distinct rebuilt `Rc`s, so this count
/// is **non-increasing** across a transform-only pass (one that rewrites but
/// does not introduce predicates). A pass that splits sharing strictly
/// increases it, tripping the guard at the exact phase that regressed.
///
/// A count is a *necessary* check, not a sufficient one — it cannot see a split
/// that a pass pairs with an equal-sized collapse elsewhere. The end-to-end
/// guard in `tests/predicate_sharing.rs` closes that by asserting no two
/// distinct `Rc`s are structurally equal, which names the defect directly.
pub fn distinct_predicate_rcs(expr: &Expr) -> usize {
    reachable_refinements(expr).len()
}

/// Rebuilding analog of [`walk_refined_predicates`]: invoke `f` on a *mutable
/// copy* of each predicate and reinstall the result, **preserving sharing** via a
/// pass-scoped [`PredMemo`] (which the callback also receives, so it can recurse
/// when a predicate's own subexpressions carry further refinements). Every
/// occurrence that shared one predicate term is re-pointed at the same term.
///
/// `f` returns whether it **changed** the copy. Returning `false` keeps the
/// origin `Rc` in place ([`PredMemo::finish_unchanged`]), so a caller that merely
/// walks past a predicate does not reallocate it — which is what lets sharing
/// survive across the nodes such a caller visits, not just within one type.
///
/// `f`'s bit is *not* the whole answer, and this does not trust it as such. A
/// callback that recurses back through the memo — which is why it is handed one —
/// can have its copy mutated underneath it by a nested memo **hit** re-pointing a
/// slot, with nothing of its own to report. Discarding the copy would then throw
/// that re-pointing away *and* memoize the staleness for every later occurrence.
/// So the copy is kept when `f` reports a change **or** the memo's
/// [`revision`](PredMemo::revision) advanced during the call: the memo is what
/// knows about its own re-pointings, so it is asked.
///
/// Returns whether this walk changed anything reachable from `ty`, so a caller
/// driving its own fixpoint (`simplify`) can fold it in.
///
/// The caller **must** pass one memo for the whole pass, not a fresh one per
/// call — see [`PredMemo`] for why.
pub fn walk_refined_predicates_mut<F>(ty: &mut Type, memo: &mut PredMemo, f: &mut F) -> bool
where
    F: FnMut(&mut Expr, &mut PredMemo) -> bool,
{
    let mut changed = false;
    if let Type::Refinement(_, refinement) = ty
        && let Some((origin, mut pred)) = memo.begin(refinement)
    {
        let before = memo.revision();
        let reported = f(&mut pred, memo);
        if reported || memo.revision() != before {
            memo.finish(refinement, origin, pred);
            changed = true;
        } else {
            memo.finish_unchanged(refinement, origin);
        }
    }
    ty.walk_children_mut(|child| changed |= walk_refined_predicates_mut(child, memo, f));
    changed
}

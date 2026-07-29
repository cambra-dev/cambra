//! Miscellaneous utilities for working with CCL.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ccl::{
    BaseType, Builtin, Expr, Lit, Name, PredicateId, Refinement, Type, TypedExprNode,
};

/// Returns `true` if `expr` directly references the given built-in primitive.
pub(crate) fn is_builtin(expr: &Expr, b: Builtin) -> bool {
    matches!(&expr.node, TypedExprNode::Builtin(x) if *x == b)
}

/// Whether `e` is a chain-head **iteration-source marker** `iterate(pred)` —
/// `Apply(pred, Builtin::Iterate)`. Planning inserts these into the *term tree*
/// ([`crate::ccl::planning::insert_iterate_markers`]) to mark an extent as an
/// iteration site; `iterate ≫ src` denotes exactly `src` (the marker is
/// denotation-neutral).
pub(crate) fn is_iterate_marker(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::Iterate))
}

/// Strip chain-head `iterate` source markers from a term, flattening the
/// `Compose` chains they head (`iterate ≫ src` ⟹ `src`).
///
/// Used when a term value is substituted **into a type** (a refinement
/// predicate — e.g. the §6.2 move-site discharge of a `let`-bound collection
/// into a refined domain like a join predicate `{d | __elem ▷ (.0 ≫ a) …}`). A
/// refinement predicate is a *denotational* term; the `iterate` marker is a
/// term-tree planning artifact with no meaning there, and leaving it in makes
/// the predicate churn under `simplify` (nested-`Compose` vs `flatten_compose`)
/// and diverge from inference's (pre-marker) copy at the post-planning
/// typecheck. Since `iterate` is denotation-neutral, dropping it recovers the
/// collection's value unchanged.
///
/// A `restrict`/`filter_values` marker is deliberately **not** stripped — it is
/// a real filter and part of the denotation; a filtered source reaching a
/// predicate is an unsupported case caught loudly by
/// [`debug_assert_no_iteration_markers_in_type`] rather than silently mis-stripped.
pub(crate) fn strip_iterate_markers(e: &Expr) -> Expr {
    let mut out = e.clone();
    out.map_children(|c| strip_iterate_markers(&c));
    if let TypedExprNode::Compose(elts) = &out.node {
        let mut flat: Vec<Expr> = Vec::new();
        for elt in elts {
            if is_iterate_marker(elt) {
                continue; // drop the neutral source marker
            }
            match &elt.node {
                // Splice a nested compose the substitution created (e.g.
                // `(a ≫ f)[a ↦ iterate ≫ xs]` = `(iterate ≫ xs) ≫ f`).
                TypedExprNode::Compose(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(elt.clone()),
            }
        }
        let ty = out.ty.clone();
        return match flat.len() {
            0 => out,
            1 => flat.into_iter().next().expect("len == 1"),
            _ => Expr::compose(flat).with_ty(ty),
        };
    }
    out
}

/// Debug-only invariant: no refinement predicate embedded in `ty` contains an
/// `iterate` or `restrict` planning marker. Predicates are denotational; markers
/// are term-tree artifacts. Upheld by [`strip_iterate_markers`] at the term→type
/// substitution boundary. A `restrict` here means a *filtered* source reached a
/// predicate (e.g. `x in [y for y in ys if p]`) — a real but unsupported case
/// that should surface loudly, not miscompile.
#[cfg(debug_assertions)]
pub(crate) fn debug_assert_no_iteration_markers_in_type(ty: &Type) {
    fn expr_has_marker(e: &Expr) -> bool {
        is_iterate_marker(e)
            || is_builtin_applied(e, Builtin::Restrict)
            || e.fold_children(false, |acc, c| acc || expr_has_marker(c))
    }
    fn go(ty: &Type) {
        if let Type::Refinement(_, r) = ty {
            debug_assert!(
                !expr_has_marker(&r.predicate),
                "iteration/restrict marker leaked into a refinement predicate: {}",
                crate::ccl::symbolic::symbolic(&r.predicate)
            );
        }
        ty.walk_children(go);
    }
    go(ty);
}

/// Whether `e` applies `b` as its function (`Apply { function: Builtin(b) }`).
#[cfg(debug_assertions)]
fn is_builtin_applied(e: &Expr, b: Builtin) -> bool {
    matches!(&e.node, TypedExprNode::Apply { function, .. } if is_builtin(function, b))
}

/// Debug-only invariant walk over a whole expression tree: every node's type
/// (and a `Cast`'s target) is checked marker-free by
/// [`debug_assert_no_iteration_markers_in_type`]. Called at the planning→
/// op-conversion boundary to catch a marker that leaked into a predicate.
#[cfg(debug_assertions)]
pub(crate) fn debug_assert_no_iteration_markers(expr: &Expr) {
    debug_assert_no_iteration_markers_in_type(&expr.ty);
    if let TypedExprNode::Cast { target, .. } = &expr.node {
        debug_assert_no_iteration_markers_in_type(target);
    }
    expr.walk_children(debug_assert_no_iteration_markers);
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
pub fn refined_data_fun(base_domain: Type, predicate: Expr, codomain: Type) -> Type {
    Type::data_fun(
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
            domain, codomain, ..
        } => Type::fun_like(ty, strip_refinements(domain), strip_refinements(codomain)),
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

/// Pass-scoped memo that **preserves refinement-predicate `Rc` sharing** across a
/// single rebuild pass — a cheap clonable handle, so reaching it never requires an
/// exclusive borrow of whatever owns it.
///
/// Predicates are immutable `Rc<TypedExpr>`s (see [`Refinement::predicate`]), so
/// any pass that must "update" a predicate — resolve embedded inference vars
/// (`coalesce`), restamp binder types (`retype`), α-uniquify, eliminate lambdas,
/// simplify, substitute, or compile to point-free form — *rebuilds* it into a
/// fresh `Rc` rather than mutating in place. When one predicate term rides several
/// type slots as a shared `Rc` (a comprehension's filtered domain appears on its
/// source, map, cast, and consumer-contract types), rebuilding each occurrence
/// independently **splits** that sharing. The split is invisible to correctness —
/// the rebuilds are value-equal, since refinement equality is structural — but it
/// defeats every downstream `Rc`-identity dedup, in particular planning's
/// per-predicate compile memo, which then recompiles one predicate once per
/// occurrence (superlinearly, on nested comprehensions).
///
/// # `C` is what the rebuild depends on besides the term
///
/// The obvious key for such a memo is the predicate `Rc`'s address. That is only
/// half a key: it answers "have I rebuilt this term?", while every pass needs
/// "have I rebuilt this term **under the conditions I am rebuilding it under
/// now**?". `C` is those conditions, and an entry is reused only when it was
/// recorded under a `C` equal to the current one. Passing the wrong `C` is then a
/// *lost sharing opportunity* rather than a wrong answer, which is the property
/// worth having: the previous key-only design made `subst` discharge a binder its
/// inner scope owned, and made constraint emission skip the emission that bounds
/// an occurrence's own domain.
///
/// What each pass supplies:
///
/// - `()` — the rebuild is a function of the term alone, or of context that is
///   provably invariant across the occurrences sharing an `Rc`. `simplify`
///   (nothing at all), and `uniquify` / `coalesce` / `retype` / `inline`, each with
///   the argument written at its call site. `()` is a *claim*, and the place to
///   check it.
/// - [`crate::ccl::subst::Subst`] — the active substitution. Acting differently in
///   different scopes is the point of a substitution, so this is the case the
///   key-only design got wrong.
/// - [`Type`] — planning's refinement base, which its compilation reads.
///
/// A pass that needs to share *allocations* without sharing *results* wants
/// [`TermMemo`] instead: constraint emission binds `REFINEMENT_BINDER` to a domain
/// minted per occurrence, so no two occurrences may reuse an answer, yet they
/// should still end up on one term.
///
/// # Keepalive
///
/// Keyed on [`PredicateId`] (the origin `Rc`'s address), which is sound only while
/// that address cannot be reused: overwriting a `refinement.predicate` can drop
/// the last reference to the origin, freeing an address a later `Rc::new` in the
/// same pass reclaims, so an unrelated predicate landing there would collide and
/// inherit this entry's rebuild. Every entry therefore retains its origin `Rc` for
/// the memo's lifetime. This is why passes use `PredMemo` rather than a bare map.
///
/// # One memo per pass
///
/// One handle (or clones of it, which are the same memo) across the *whole* tree
/// walk. A fresh memo per node re-shares only within that node and splits across
/// the tree — the bug this type exists to prevent. Guarded end-to-end by
/// `tests/predicate_sharing.rs` and, per phase, by asserting
/// [`distinct_predicate_rcs`] does not grow across a rewrite-only pass.
pub struct PredMemo<C = ()>(Rc<RefCell<MemoStore<C>>>);

impl<C> Clone for PredMemo<C> {
    /// Another handle on the *same* memo — not a copy of it.
    fn clone(&self) -> Self {
        PredMemo(Rc::clone(&self.0))
    }
}

impl<C> Default for PredMemo<C> {
    fn default() -> Self {
        PredMemo(Rc::new(RefCell::new(MemoStore {
            entries: HashMap::new(),
            revision: 0,
        })))
    }
}

/// Shares predicate *terms* without sharing rebuild *results*: the transform runs
/// at every occurrence, and occurrences that entered sharing one `Rc` leave
/// sharing one `Rc`.
///
/// For a pass whose rebuild depends on something that never repeats across
/// occurrences, so [`PredMemo`]'s reuse could never fire and must not: constraint
/// emission types the predicate with `REFINEMENT_BINDER` bound to a domain
/// `emit_cast` mints fresh per cast node. Each occurrence has to discharge its own
/// typing obligation; only the resulting allocation is unified. Discarding the
/// loser's term is sound because refinement identity is type-blind — the
/// occurrences denote one refinement, so the winner's embedded type slots are as
/// good as the discarded one's.
///
/// A separate type from [`PredMemo`] on purpose: "reuse the answer" and "reuse only
/// the allocation" are different operations, and which one a pass is entitled to
/// should be visible in its type rather than argued in a comment.
#[derive(Clone, Default)]
pub struct TermMemo(PredMemo<()>);

/// The memo's actual storage, reached only through a handle.
struct MemoStore<C> {
    /// One key can be rebuilt under several contexts (`subst` inside and outside a
    /// scope that shadows a substituted binder), so entries are a list. It is
    /// almost always length 1, and a linear scan of it beats hashing a `C`.
    entries: HashMap<PredicateId, Vec<Entry<C>>>,
    /// Advances whenever a predicate slot is pointed at a *different* `Rc`. Lets
    /// [`PredMemo::rebuild`] observe re-pointings performed inside its callback's
    /// own recursion, which the callback cannot report: a nested reuse mutates the
    /// callback's copy without the callback doing anything.
    revision: u64,
}

struct Entry<C> {
    /// Pins the key's address for the memo's lifetime (see the keepalive note on
    /// [`PredMemo`]). Deliberately never read: *holding* the `Rc` is the entire
    /// job, and dropping this field would make the address reusable and the key
    /// unsound.
    #[allow(dead_code)]
    keepalive: Rc<Expr>,
    rebuilt: Rc<Expr>,
    context: C,
}

impl<C> MemoStore<C> {
    /// Point `refinement` at `to`, counting it when the `Rc` actually changes.
    fn point_at(&mut self, refinement: &mut Refinement, to: Rc<Expr>) {
        if !Rc::ptr_eq(&refinement.predicate, &to) {
            self.revision += 1;
        }
        refinement.predicate = to;
    }
}

impl<C: PartialEq + Clone> PredMemo<C> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Rebuild `refinement`'s predicate under `context`, or reuse the rebuild an
    /// earlier occurrence made under an **equal** context.
    ///
    /// `f` receives a mutable copy of the predicate and reports whether it changed
    /// it. It may re-enter this memo freely — including through the pass's own
    /// recursion, which is the usual case — because no borrow of the store is held
    /// across the call. That re-entrancy is why this is a closure rather than a
    /// begin/finish token pair: the token could be dropped on an early return,
    /// silently discarding the rebuild and leaving the occurrence on its origin.
    ///
    /// Reporting `false` keeps the origin `Rc` in the slot, so a predicate the pass
    /// merely walks past is never reallocated and stays pointer-shared with
    /// occurrences the pass never visits.
    ///
    /// Returns whether the slot ended up pointing somewhere new — which is *not*
    /// just `f`'s answer. A nested reuse inside `f` can re-point a slot in the copy
    /// with `f` having nothing of its own to report; discarding the copy would then
    /// throw that away and memoize the staleness. The store's revision counter is
    /// consulted for exactly that.
    pub fn rebuild(
        &self,
        refinement: &mut Refinement,
        context: &C,
        f: impl FnOnce(&mut Expr) -> bool,
    ) -> bool {
        let (mut pred, keepalive, before) = {
            let mut store = self.0.borrow_mut();
            let hit = store
                .entries
                .get(&refinement.predicate_id())
                .and_then(|es| es.iter().find(|e| e.context == *context))
                .map(|e| Rc::clone(&e.rebuilt));
            match hit {
                Some(rebuilt) => {
                    store.point_at(refinement, rebuilt);
                    return false;
                }
                None => {
                    let keepalive = Rc::clone(&refinement.predicate);
                    let copy = (*refinement.predicate).clone();
                    let rev = store.revision;
                    (copy, keepalive, rev)
                }
            }
        };
        let reported = f(&mut pred);
        let mut store = self.0.borrow_mut();
        let changed = reported || store.revision != before;
        let installed = if changed {
            Rc::new(pred)
        } else {
            Rc::clone(&keepalive)
        };
        store.point_at(refinement, Rc::clone(&installed));
        store
            .entries
            .entry(Rc::as_ptr(&keepalive))
            .or_default()
            .push(Entry {
                keepalive,
                rebuilt: installed,
                context: context.clone(),
            });
        changed
    }
}

impl TermMemo {
    pub fn new() -> Self {
        Self::default()
    }

    /// Run `f` on a copy of `refinement`'s predicate — **always**, never skipped —
    /// then point the slot at the term an earlier occurrence produced, or record
    /// this one as that term if it is the first.
    ///
    /// The closure cannot leak the rebuild: there is no token to drop, so an early
    /// return inside `f` (a `?` on the pass's own error type, captured by the
    /// caller) still leaves the occurrence rebuilt and recorded.
    pub fn rebuild_always(&self, refinement: &mut Refinement, f: impl FnOnce(&mut Expr)) {
        let keepalive = Rc::clone(&refinement.predicate);
        let mut pred = (*refinement.predicate).clone();
        f(&mut pred);
        let mut store = self.0.0.borrow_mut();
        let shared = store
            .entries
            .get(&Rc::as_ptr(&keepalive))
            .and_then(|es| es.first())
            .map(|e| Rc::clone(&e.rebuilt));
        match shared {
            Some(term) => store.point_at(refinement, term),
            None => {
                let installed = Rc::new(pred);
                store.point_at(refinement, Rc::clone(&installed));
                store
                    .entries
                    .entry(Rc::as_ptr(&keepalive))
                    .or_default()
                    .push(Entry {
                        keepalive,
                        rebuilt: installed,
                        context: (),
                    });
            }
        }
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
/// `f` returns whether it **changed** the copy; see [`PredMemo::rebuild`] for what
/// that bit does and does not decide, and for why `f` may re-enter the memo.
///
/// Returns whether this walk changed anything reachable from `ty`, so a caller
/// driving its own fixpoint (`simplify`) can fold it in.
///
/// The caller **must** pass one memo for the whole pass, not a fresh one per
/// call — see [`PredMemo`] for why. `context` is that pass's `C` (see `PredMemo`);
/// a pass whose rebuild is a function of the term alone passes `&()`.
pub fn walk_refined_predicates_mut<C, F>(
    ty: &mut Type,
    memo: &PredMemo<C>,
    context: &C,
    f: &mut F,
) -> bool
where
    C: PartialEq + Clone,
    F: FnMut(&mut Expr, &PredMemo<C>) -> bool,
{
    let mut changed = false;
    if let Type::Refinement(_, refinement) = ty {
        changed |= memo.rebuild(refinement, context, |pred| f(pred, memo));
    }
    ty.walk_children_mut(|child| changed |= walk_refined_predicates_mut(child, memo, context, f));
    changed
}

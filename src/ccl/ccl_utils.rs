//! Miscellaneous utilities for working with CCL.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::ccl::scope::{ScopedItem, for_each_scoped_item};
use crate::ccl::{
    BaseType, BinOpKind, Branch, Builtin, Expr, F_FIRE_SUFFIX, F_WRITES, FieldKey, Lit, LogicKind,
    Name, PredicateId, ProjKey, Refinement, RefinementSet, Type, TypedExprNode, UnaryOpKind,
    V_ABORT, V_COMMIT,
};

/// The `commit` selector field of the **intermediate** decision record the two
/// writer phases build (`{commit, writes, to_<defer>*}`) *before*
/// [`wrap_decision_variant`] folds it into the `` {`commit{𝑃} | `abort} `` variant.
/// The whole-transaction grant/deny is no longer a decision-codomain field — it
/// is the variant *tag* — so this constant is phase-internal plumbing, not part
/// of the observable decision protocol (hence it lives here, beside the wrapper,
/// rather than among the AST field constants in `expr.rs`).
pub(crate) const COMMIT_SELECTOR: &str = "commit";

/// Disjoin control-flow `paths` into one boolean commit gate — the writer
/// decision's `commit` field, true exactly where some path commits. Short-circuits
/// a literal `true` path (an unconditional commit) and skips a literal `false`,
/// so a spine writer folds to `true` (not `true or true or …`) and the two phases
/// build the same gate for the same shape. `empty` is the value of an empty
/// disjunction: `true` for a transaction block (a bare `with begin():` always
/// commits), `false` for an induction `Case` (no writing/feeding branch commits
/// nothing — a pure carry).
pub fn disjoin(paths: impl IntoIterator<Item = Expr>, empty: bool, bool_ty: &Type) -> Expr {
    let lit = |b: bool| Expr::new(TypedExprNode::Lit(Lit::Bool(b))).with_ty(bool_ty.clone());
    let mut acc: Option<Expr> = None;
    for p in paths {
        match &p.node {
            TypedExprNode::Lit(Lit::Bool(true)) => return lit(true),
            TypedExprNode::Lit(Lit::Bool(false)) => continue,
            _ => {}
        }
        acc = Some(match acc {
            None => p,
            Some(prev) => {
                Expr::binop(prev, BinOpKind::BoolLogic(LogicKind::Or), p).with_ty(bool_ty.clone())
            }
        });
    }
    acc.unwrap_or_else(|| lit(empty))
}

/// Assemble a writer **decision record** `{commit, writes, (to_<feed>__fire,)?
/// to_<feed>, …}` — the single encoding of the tap/`__fire` protocol shared by the
/// transaction writer ([`crate::ccl::transact_phase`]) and the induction writer
/// ([`crate::ccl::mut_elim`]). Both feed it to the interpreter through the same
/// `body_decision_at` decoder, so the shape must be built in exactly one place.
///
/// `feeds` are `(field, value, fire)` in tap order. A tap whose `fire` path is
/// structurally the writer's `commit` — a spine or sole-committer feed that fires
/// with *every* committing position — carries **no** gate (the engine treats an
/// ungated tap as firing with the commit). A **narrower** `fire` carries a
/// `to_<feed>__fire` gate the engine reads to fire the reply only on its own route,
/// so a sibling route's commit does not over-fire it.
///
/// `commit` must already be the writer's *final* commit gate — including every
/// feed's fire path, so a feed-only committing position appends a change carrying
/// the tap (the caller folds fires into `commit` before calling; see
/// `transact_phase`'s `commit_paths` and `letrec_phase`'s widen).
pub fn writer_decision_record(commit: Expr, writes: Expr, feeds: &[(String, Expr, Expr)]) -> Expr {
    let mut fields: Vec<(String, Expr)> = Vec::with_capacity(2 + feeds.len() * 2);
    fields.push((COMMIT_SELECTOR.to_string(), commit.clone()));
    fields.push((F_WRITES.to_string(), writes));
    for (field, value, fire) in feeds {
        // Gate iff the fire path is *narrower* than the commit — a structural test
        // (no Boolean simplification); the engine handles both an ungated tap
        // (fires with commit) and a gated one (fires on its route) correctly, so
        // the two shapes are observationally equal, this only decides which is
        // emitted.
        if *fire != commit {
            fields.push((format!("{field}{F_FIRE_SUFFIX}"), fire.clone()));
        }
        fields.push((field.clone(), value.clone()));
    }
    let ty = Type::Record(
        fields
            .iter()
            .map(|(k, v)| (k.clone(), v.ty.clone()))
            .collect(),
    );
    Expr::new(TypedExprNode::Record(fields)).with_ty(ty)
}

/// The decision **variant** type `` {`commit{𝑃} | `abort} `` over a (dense) payload
/// record type `𝑃` (`{writes, to_<defer>*}`). Tag order is `commit`=0, `abort`=1
/// — the positions [`wrap_decision_variant`] injects and `body_decision_at`
/// decodes.
pub fn decision_variant_ty(payload_ty: Type) -> Type {
    Type::variant(vec![
        (FieldKey::Name(V_COMMIT.into()), payload_ty),
        (FieldKey::Name(V_ABORT.into()), Type::Base(BaseType::Unit)),
    ])
}

/// The type of a **history**: the total function `𝐷 ⤇ 𝑉` a mutable variable, a feed
/// channel, or a commit log denotes over its sequencing domain (`mutability.md`,
/// "The model: histories and causal recursion").
///
/// A collection, and so [`crate::ccl::ty::FunKind::Data`]: the engine stores one value per
/// position of the domain — an induction store's changelog, a commit log — and every read is
/// a read at a position (`get_prev_seq`, `get_prev_txn`, `final_or_default`, an `AsOf` join).
/// A view of a history is a history too, but it is built by *carrying* the head's kind
/// through the compose ([`Type::fun_like`]) rather than by restating this.
///
/// One history has several spellings — the binding, the record field holding it, the
/// tuple slot a causal accessor reads it from — and they have to agree, so they all say
/// this rather than each reaching for [`Type::fun`].
pub fn history_ty(domain_ty: &Type, value_ty: &Type) -> Type {
    Type::data_fun(domain_ty.clone(), value_ty.clone())
}

/// The `commit` payload record type of a decision variant `` {`commit{𝑃} | `abort} ``
/// (peeling outer refinements).
pub fn commit_payload_ty(decision_ty: &Type) -> Type {
    let mut t = decision_ty;
    while let Type::Refinement(inner, _) = t {
        t = inner;
    }
    match t {
        Type::Variant(tags, _) => tags
            .iter()
            .find(|(k, _)| matches!(k, FieldKey::Name(n) if n == V_COMMIT))
            .unwrap_or_else(|| panic!("decision variant lacks a `commit` tag: {decision_ty}"))
            .1
            .clone(),
        other => panic!("expected a decision variant type, got {other}"),
    }
}

/// The point-free one-arm eliminator ``variant_project(`commit) : 𝑑 ⇒ 𝑃`` reading a
/// decision stream's `commit` payload — inserted before a `.writes`/`.to_<defer>`
/// read so a `` Fun(D, {`commit{𝑃} | `abort}) `` history projects its committing
/// payload. (`abort` positions carry no payload and drop out of the eliminated
/// stream; a read is only meaningful at committing positions.)
pub fn commit_project(decision_ty: &Type) -> Expr {
    // The projection names the tag, so a decision variant materialized in any arm
    // order reads the same — there is no position for the runtime decode to agree
    // with, and `commit_payload_ty` below finds the payload by the same name.
    Expr::builtin(Builtin::VariantProject(FieldKey::Name(V_COMMIT.into()))).with_ty(Type::fun(
        decision_ty.clone(),
        commit_payload_ty(decision_ty),
    ))
}

/// Wrap a writer **decision record** `{commit, writes, to_<defer>*}` (the
/// intermediate the two phases build via [`writer_decision_record`]) into the
/// **decision variant** `Case[ commit → .commit(⟨writes, to_<defer>*⟩) ; true →
/// `abort(unit) ]``. The `commit` field becomes the value-`Case` **selector** (its
/// disjunction of path conditions) rather than a stored field; the remaining
/// fields are the (dense) `commit` payload. This is the single site both the
/// transaction writer and the induction writer funnel through, so the variant is
/// built in exactly one place and `body_decision_at` decodes one shape.
///
/// The decision may sit under read-your-writes `let`s (the induction writer's
/// `let __v = … in {commit, writes}`); descend through them and rebuild the
/// variant at the record, preserving the `let` scope.
pub fn wrap_decision_variant(decision: Expr) -> Expr {
    match decision.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_body = wrap_decision_variant(*body);
            let ty = new_body.ty.clone();
            let mut e = Expr::new(TypedExprNode::Let {
                binding,
                bound_expr,
                body: Box::new(new_body),
            });
            e.ty = ty;
            e
        }
        TypedExprNode::Record(fields) => {
            let bool_ty = Type::Base(BaseType::Bool);
            let unit_ty = Type::Base(BaseType::Unit);
            // Split the `commit` selector out from the payload fields (everything
            // else — `writes` and the `to_<defer>*` taps, in order).
            let mut commit: Option<Expr> = None;
            let mut payload_fields: Vec<(String, Expr)> = Vec::with_capacity(fields.len());
            for (k, v) in fields {
                if k == COMMIT_SELECTOR {
                    commit = Some(v);
                } else {
                    payload_fields.push((k, v));
                }
            }
            let commit = commit.expect("a writer decision record carries a `commit` selector");
            let payload_ty = Type::Record(
                payload_fields
                    .iter()
                    .map(|(k, v)| (k.clone(), v.ty.clone()))
                    .collect(),
            );
            let payload =
                Expr::new(TypedExprNode::Record(payload_fields)).with_ty(payload_ty.clone());
            let variant_ty = decision_variant_ty(payload_ty);

            let commit_ctor = Expr::variant_ctor(V_COMMIT, payload).with_ty(variant_ty.clone());
            let unit = Expr::new(TypedExprNode::Lit(Lit::Unit)).with_ty(unit_ty.clone());
            let abort_ctor = Expr::variant_ctor(V_ABORT, unit).with_ty(variant_ty.clone());
            let true_lit = Expr::new(TypedExprNode::Lit(Lit::Bool(true))).with_ty(bool_ty.clone());

            let mut case = Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: vec![
                    Branch {
                        pattern: None,
                        guard: commit,
                        body: commit_ctor,
                    },
                    Branch {
                        pattern: None,
                        guard: true_lit,
                        body: abort_ctor,
                    },
                ],
            });
            case.ty = variant_ty;
            case
        }
        other => panic!(
            "wrap_decision_variant: a writer decision is `let* in {{commit, writes, …}}`, got {other:?}"
        ),
    }
}

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
        if let Type::Refinement(_, refinements) = ty {
            for r in refinements {
                debug_assert!(
                    !expr_has_marker(&r.predicate),
                    "iteration/restrict marker leaked into a refinement predicate: {}",
                    crate::ccl::symbolic::symbolic(&r.predicate)
                );
                debug_assert!(
                    !expr_needs_iteration(&r.predicate),
                    "a source that must be *iterated* reached a refinement predicate: {}\n\
                     A predicate looks its collection up at an index; it never sweeps one, and \
                     it may carry no `iterate`/`restrict` to sweep with. Realizing a conditional \
                     source inside a predicate produces exactly this — a gated union whose legs \
                     need the markers the assertion above forbids — and op-conversion then \
                     compiles one leg and silently answers from the wrong arm. The predicate has \
                     to name a *plain* collection: under leg i the conditional is `arm i`, so \
                     substitute it.",
                    crate::ccl::symbolic::symbolic(&r.predicate)
                );
            }
        }
        ty.walk_children(go);
    }
    go(ty);
}

/// Whether `e` contains a collection that op-conversion could only compile by **iterating**
/// it — a realized conditional (`Realize`) or a union of collections.
///
/// The complement of [`debug_assert_no_iteration_markers_in_type`]'s own check, and the half
/// it could not see. That one catches a marker that *leaked in*; this catches a term that
/// would *need* one. Both say the same thing about a predicate — it is denotational — and
/// only together do they close the gap, since a term needing iteration and carrying no
/// marker passes the first check and miscompiles.
#[cfg(debug_assertions)]
fn expr_needs_iteration(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::Realize(_) | TypedExprNode::Copair(_))
        || e.fold_children(false, |acc, c| acc || expr_needs_iteration(c))
}

/// Whether `e` applies `b` as its function (`Apply { function: Builtin(b) }`).
#[cfg(debug_assertions)]
fn is_builtin_applied(e: &Expr, b: Builtin) -> bool {
    matches!(&e.node, TypedExprNode::Apply { function, .. } if is_builtin(function, b))
}

/// Debug-only invariant walk over a whole expression tree: every type slot a node
/// carries ([`Expr::walk_type_slots`]) is checked marker-free by
/// [`debug_assert_no_iteration_markers_in_type`]. Called at the planning→
/// op-conversion boundary to catch a marker that leaked into a predicate.
#[cfg(debug_assertions)]
pub(crate) fn debug_assert_no_iteration_markers(expr: &Expr) {
    expr.walk_type_slots(debug_assert_no_iteration_markers_in_type);
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

/// Build arm `i`'s effective **first-match** predicate `gᵢ ∧ ¬g₀ ∧ … ∧ ¬gᵢ₋₁`,
/// encoding a `Case`'s "first matching guard wins" semantics: arm `i` fires only
/// where its own guard holds and no earlier arm's did. `prior` holds `g₀ … gᵢ₋₁`
/// in order; `guard` is `gᵢ`. Every guard is a `Bool`-typed expression over the
/// same element, so the synthesized conjunction is `Bool` too — typed here
/// because the callers (post-inference channelize, lambda elimination, the
/// transaction path walk) must be type-preserving.
///
/// Shared by [`crate::ccl::channelize`] (feed fan-out), [`crate::ccl::lambda_elim`]
/// (value-`Case` compilation), and the transaction path walk — every conditional
/// fan-out in the pipeline partitions its domain with the same encoding.
pub fn synthesize_arm_predicate(guard: &Expr, prior: &[Expr]) -> Expr {
    let bool_ty = Type::Base(BaseType::Bool);
    let mut pred = guard.clone();
    for g in prior {
        let mut neg = Expr::unary(UnaryOpKind::Not, g.clone());
        neg.ty = bool_ty.clone();
        let mut conj = Expr::binop(pred, BinOpKind::BoolLogic(LogicKind::And), neg);
        conj.ty = bool_ty.clone();
        pred = conj;
    }
    pred
}

/// Returns `true` if `b` is a trailing `true → Case{…}` arm whose body is itself
/// a guard-only value `Case` — the shape an `elif` chain lowers to
/// (`a if p else b if q else c`; the `else` binds the nested conditional).
fn is_trailing_nested_case(b: &Branch) -> bool {
    b.pattern.is_none()
        && matches!(&b.guard.node, TypedExprNode::Lit(Lit::Bool(true)))
        && matches!(
            &b.body.node,
            TypedExprNode::Case { scrutinee: None, branches }
                if branches.iter().all(|ib| ib.pattern.is_none())
        )
}

/// Flatten `elif` chains: a trailing `true → Case{…}` arm splices its inner
/// branches into the outer list, so a value-`Case` fan-out sees one flat
/// partition `[g₀ → e₀; g₁ → e₁; …; true → eₙ]` rather than a nest of `Case`s.
/// The first-match encoding ([`synthesize_arm_predicate`]) composes the guards
/// correctly across the flattened arms. Shared by the value-`Case` compilation
/// ([`crate::ccl::lambda_elim`]) and the comprehension element fan-out
/// ([`crate::ccl::lower`]).
pub fn flatten_trailing_value_case(mut branches: Vec<Branch>) -> Vec<Branch> {
    while branches.last().is_some_and(is_trailing_nested_case) {
        let last = branches.pop().expect("checked non-empty via last()");
        if let TypedExprNode::Case {
            branches: inner, ..
        } = last.body.node
        {
            branches.extend(inner);
        }
    }
    branches
}

/// Builds a composition of expressions, setting the types based on the input
/// expressions' types. The first expression's domain type is used as the domain type of the
/// composition, and the last expression's codomain type is used as the codomain type of the composition.
///
/// The chain's **kind** is the head morphism's, matching the inference rule
/// (`emit_compose`): a chain's domain is the head's domain, so the chain denotes
/// a collection exactly when the head does. Mapping a function over a collection
/// (`xs ≫ f`) leaves a collection; a chain of capabilities stays a capability.
pub fn typed_compose(elts: Vec<Expr>) -> Expr {
    let d_ty = elts[0].ty.domain().unwrap().clone();
    let c_ty = elts[elts.len() - 1].ty.codomain().unwrap().clone();
    // Not `fun_like`: only the *kind* comes from the head. A Pi binder belongs to
    // the morphism that binds it, and the chain's codomain is the last morphism's.
    let fun_kind = match &elts[0].ty {
        Type::Fun { fun_kind, .. } => fun_kind.clone(),
        _ => crate::ccl::ty::FunKind::Compute,
    };
    Expr::compose(elts).with_ty(Type::Fun {
        name: None,
        fun_kind,
        domain: Box::new(d_ty),
        codomain: Box::new(c_ty),
    })
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
/// built predicate term — safe because refinements match by structural
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
    // A **data** function, because it denotes a collection: `iterate(p)` is the
    // identity on the extent, so the extent is its data. This is what makes the
    // kind decide whether iterating is
    // acceptable at all — every chain led by an iteration source inherits `Data`
    // from here (`typed_compose`), so a site whose value-producer is a mere
    // capability is a kind error rather than something a later stamp papers over.
    apply_primitive(
        predicate,
        Builtin::Iterate,
        Type::data_fun(refined.clone(), refined),
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
        {
            let (u, d) = (strip_refinements(&upstream_dom), strip_refinements(&domain));
            u == d || (matches!(u, Type::WitnessRef(_)) && matches!(d, Type::WitnessRef(_)))
        },
        "restrict upstream domain {upstream_dom} must match predicate domain {domain}",
    );
    // `{d : D | p(d)} ⇒ T` — refinement on the domain, value preserved.
    // Narrowing an extent leaves it an extent, so the kind rides through from
    // `upstream`: restricting a collection yields a collection, restricting a
    // capability yields a capability.
    //
    // The refinement is built **without** `refine_with`'s trivially-true
    // degeneracy: the caller emits one `restrict` per refinement the site declared,
    // so dropping one here would leave the source producing a bare extent while the
    // site — and the body's `cast` — still demand the refined one. A vacuous
    // refinement is the site's business, not this constructor's.
    let refined_dom = Type::refined_one(
        domain.clone(),
        Refinement::born(Rc::new(bare_predicate_of_fn(&domain, predicate.clone()))),
    );
    let refined_stream = Type::fun_like(&upstream_ty, refined_dom, value_ty);
    // The transformer node `restrict(p) : (D ⇒ T) ⇒ ({d : D | p(d)} ⇒ T)`.
    let restrict = apply_primitive(
        predicate,
        Builtin::Restrict,
        Type::fun(upstream_ty, refined_stream.clone()),
    );
    apply_function(upstream, restrict, refined_stream)
}

/// Refine a join morphism's **extent** — both sides — with `predicate`, taking
/// `D ⇒ C` to `{D | predicate} ⇒ {C | predicate}`.
///
/// A hash join consumes its equi-join conditions structurally, into the key-lookup
/// shape with no residual `Restrict`, so nothing in the term says which rows it
/// yields. What it yields is nonetheless exactly the join-satisfying extent, and
/// that is what the type must say: a data function's domain *is* its data, so the
/// domain of this morphism is the refined extent, not the full product. Refining
/// only the codomain would leave the domain claiming rows the join never produces
/// — readable as a supertype under the contravariant reading of a function, but
/// wrong for a collection, and it puts every enclosing type at odds with the site.
///
/// The symmetric `{D | p} ⇒ {D | p}` shape is the same one [`make_iterate`] gives
/// an iteration source, for the same reason: both denote the extent they sweep.
///
/// A thin wrapper over [`set_extent`] that refines the existing types in place
/// rather than replacing them; see there for how the rewrite is threaded down the
/// combinator's function spine so the post-planning `typecheck` reconstructs it.
/// No runtime node is added (the combinators are type-level).
pub fn refine_extent(morphism: Expr, bare_predicate: &Expr) -> Expr {
    let Type::Fun {
        domain, codomain, ..
    } = &morphism.ty
    else {
        panic!("join morphism must be a function type, got {}", morphism.ty);
    };
    // `bare_predicate` is already the bare `Bool`-over-`__elem` form (the extent's
    // membership condition, the same predicate the body's `cast` demands), so it
    // is stored directly — *not* via `refine_with`, which wraps a predicate
    // *function*. Storing the identical bare term keeps the producer structurally
    // equal to the cast demand.
    let (d, c) = (
        refine_with_bare((**domain).clone(), bare_predicate),
        refine_with_bare((**codomain).clone(), bare_predicate),
    );
    set_extent(morphism, d, c)
}

/// Re-stamp a morphism `D ⇒ _`'s codomain to `new_codomain`, yielding
/// `D ⇒ new_codomain`. Used by join planning to surface the refined extent a
/// producer yields (see [`refine_extent`], and `wrap_with_iterate`'s
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
pub fn set_codomain(morphism: Expr, new_codomain: Type) -> Expr {
    let domain = morphism
        .ty
        .domain()
        .expect("morphism must be a function type")
        .clone();
    set_extent(morphism, domain, new_codomain)
}

/// Re-stamp a morphism's whole extent — domain and codomain — threading the new
/// type down the combinator's function spine. See [`set_codomain`], which fixes
/// the domain, and [`refine_extent`], which refines both.
pub fn set_extent(mut morphism: Expr, domain: Type, new_codomain: Type) -> Expr {
    // `fun_like`: a codomain-only rewrite must not flip the kind or drop
    // its Pi binder — restamping an iteration source's codomain leaves it the
    // same collection.
    let new_ty = Type::fun_like(&morphism.ty, domain, new_codomain);
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
    let new_ty = Type::fun_like(&node.ty, domain, new_result);
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
/// the one [`crate::ccl::lambda_elim`]'s groupby reconstruction reads a refinement
/// off of, so this asserts the lowering contract: a non-conforming target is
/// a construction-time bug, not a user error, so it panics rather than
/// emitting a cast `lambda_elim` would mishandle.  See [`TypedExprNode::Cast`]
/// for the migration plan toward a general `𝑈 ⇒ 𝑇` cast.
/// TODO remove this constraint once we get rid of the special-casing correlated
/// refinement code in lambda_elim.
pub fn make_cast(value: Expr, target_ty: Type) -> Expr {
    // Through [`Type::domain`], not by matching `Type::Fun` here: a collection indexed by a
    // witness spells the function inside a `Σ` binder, and `Type::fun_like` — which is what
    // builds these targets — re-closes that binder. Matching the outer constructor rejects
    // the shape the paired constructor just produced.
    assert!(
        matches!(target_ty.domain(), Some(Type::Refinement(..))),
        "make_cast target_ty must denote a function with a refined domain, got {target_ty}"
    );
    Expr::cast(value, target_ty)
}

/// Read the domain refinement off a cast target type — the refinement a
/// [`make_cast`] target carries on its `Fun(Refinement(_, r), _)` shape.
///
/// [`crate::ccl::lambda_elim`]'s cast-wrapped-lambda arm calls this on a
/// [`TypedExprNode::Cast`]'s `target` to reattach the refinement to the
/// reconstructed `groupby` lambda.  (Inference does not need it: it types the
/// cast as the upcast `value_ty <: target` and lets the solver carry the
/// refinement.) The returned refinements share their predicates' `Rc<Expr>`s with
/// `target`.
///
/// The whole [`RefinementSet`] is returned rather than a single refinement: a target
/// is *built* carrying one predicate ([`refined_data_fun`]), but the domain it
/// unifies against may contribute more, and a caller reattaching "the cast's
/// refinement" wants all of what the target demands.
pub fn cast_target_refinement(target: &Type) -> Option<RefinementSet> {
    // [`Type::domain`] for the same reason [`make_cast`] uses it: the target may be a
    // witness-indexed collection, whose function sits under a `Σ` binder. This has to agree
    // with `make_cast` on which targets carry a refinement, since one asserts what the
    // other reads.
    let Type::Refinement(_, refinements) = target.domain()? else {
        return None;
    };
    Some(refinements)
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
pub fn refined_data_fun(
    base_domain: Type,
    predicate: Expr,
    codomain: Type,
    fun_kind: crate::ccl::ty::FunKind,
) -> Type {
    // A kind **variable**, not a concrete `Data(None)`: the value being re-viewed may be a
    // sum (a filtered conditional collection), and the cast target must relate to a plain
    // collection and a sum alike (`src/ccl/design/type-inference.md`, "Consuming a sum:
    // pinning the consumer's kind").
    //
    // The caller supplies it so that a re-view can share the kind of the thing it re-views.
    // Minting one here instead left a filtered comprehension's target unrelated to its own
    // source, so nothing ever told it whether it was a sum and materialization decided from
    // the domain.
    Type::Fun {
        name: None,
        fun_kind,
        domain: Box::new(Type::refined_one(
            base_domain,
            Refinement::born(Rc::new(predicate)),
        )),
        codomain: Box::new(codomain),
    }
}

/// A structural copy of `ty` with every [`Type::Refinement`] layer removed,
/// at any depth (inside tuples / records / function types).  Used to compare
/// domains up to refinements (which are transparent to structural shape) —
/// the two sides may carry the same predicate at different compilation stages
/// (bare `__elem ▷ p` before vs after planning normalizes `p` to point-free),
/// so refinements must not participate in the comparison at any depth.
///
/// **Only meaningful on a resolved type.** This is a *syntactic* peel: it removes the
/// `Type::Refinement` layers it can see and returns a [`Type::Infer`] untouched. During
/// constraint emission, where most types are still inference variables, it therefore
/// silently does nothing for every operand that is not a literal — while looking like
/// it works, which is the trap. It cannot express a *relation* between two types that
/// are still variables, because at the moment it runs there is nothing to peel.
///
/// So: fine for **comparing** two already-resolved types, and fine in any pass after
/// inference. There is no call for it in `emit`, and the two things a rule reaches for
/// it wanting are elsewhere:
///
/// - "these are related on their base, not on their refinements" during inference:
///   a trait obligation over them, which defers the same question until the operands
///   resolve and reads the base off each as it arrives
///   ([`solver::traits`](crate::ccl::infer::solver::traits)).
/// - "look *past* the outer layers" — what a shape test wants, since a refinement is
///   not part of the shape: [`Type::peel_refinements`](crate::ccl::Type::peel_refinements),
///   which borrows rather than dropping.
pub(crate) fn strip_refinements(ty: &Type) -> Type {
    match ty {
        // Annotation-position only, and structural: keep the wrapper and strip
        // inside it, so a bounded annotation's bound is stripped like any other.
        Type::BoundedHole(t) => Type::BoundedHole(Box::new(strip_refinements(t))),
        Type::Refinement(base, _) => strip_refinements(base),
        // The **witnesses' type kinds are left alone** (they ride the `kind` `fun_like`
        // copies).
        // A sum's candidates are domains, and the Σ rules match them by value, so two
        // sums differing only in a candidate's refinement are different types —
        // `Σ (σ : [{[0,2] | 𝑝}]). …` is the filtered arm and `Σ (σ : [[0,2]]). …` is not.
        // Erasing there would make them compare equal, which is the opposite of what a
        // comparison up to refinements is for: it drops a distinction rather than an
        // incidental spelling.
        Type::Fun {
            domain, codomain, ..
        } => Type::fun_like(ty, strip_refinements(domain), strip_refinements(codomain)),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(strip_refinements).collect()),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), strip_refinements(t)))
                .collect(),
        ),
        Type::Variant(tags, openness) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), strip_refinements(t)))
                .collect(),
            *openness,
        ),
        Type::History {
            value,
            domain,
            history_kind,
        } => Type::History {
            value: Box::new(strip_refinements(value)),
            domain: Box::new(strip_refinements(domain)),
            history_kind: *history_kind,
        },
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::Hole
        | Type::SharedHole(_)
        | Type::Infer(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::WitnessRef(_)
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

/// Restore every [`TypedExprNode::Cast`]'s canonical type split after a
/// rebuild pass: the `target` keeps its **born** refinements on the rebuilt view's
/// shape and bases; the node type carries the value's domain refinements ∪ born
/// ([`canonical_cast_ty`] — the same rule coalesce applies). Bottom-up, so a
/// cast value that is itself a cast presents its canonical type to its parent.
///
/// A pass that rebuilds node types wholesale (lambda elimination's composition
/// typing, `simplify`'s rule rewrites, planning's point-free compilation)
/// re-derives `expr.ty` from surrounding term structure — and where inference
/// left route-dependent types in eq-blind slots (a lambda param annotation,
/// say), that re-derivation is route-dependent too. Installing the rebuilt
/// view wholesale into `target` (the previous behaviour) therefore made a
/// cast's *refinements* route-dependent — the defect the coalesce-time
/// canonicalization retired — while dropping the view's refinements from `expr.ty`
/// left the recorded type disagreeing with the post-pass typecheck's
/// reconstruction (value-refinements ∪ target-refinements). Deriving both slots from
/// the term repairs both at once.
pub fn canonicalize_cast_types(expr: &mut Expr) {
    expr.walk_children_mut(canonicalize_cast_types);
    match &expr.node {
        TypedExprNode::Cast { .. } => {
            let view = expr.ty.clone();
            if let TypedExprNode::Cast { value, target } = &mut expr.node {
                let born = std::mem::replace(target, Type::Hole);
                *target = canonical_cast_ty(&born, None, view.clone());
                expr.ty = canonical_cast_ty(&born, Some(&value.ty), view);
            }
        }
        // A chain's type is derived from its ends (`emit_compose`): the domain
        // comes from the head, the codomain from the tail. A head cast whose
        // domain was just canonicalized owes the chain its domain — the
        // post-pass typecheck's reconcile is exact on domain refinements (a
        // recorded domain may be neither wider nor narrower than the derived
        // one, by contravariance meeting the covariant reconcile), so the
        // recorded chain type must follow.
        //
        // Follow only where the difference is *refinements on the same base* — the
        // one thing cast canonicalization moves — and only on the domain. A
        // structurally different recorded end, or a codomain refined beyond
        // the tail's (a conditional leg's realization pin, planning's
        // `refine_codomain`), is a deliberate statement this pass has no
        // license to rewrite; overwriting one miscompiles (observed: a
        // comprehension over a conditional summing the unfiltered extent).
        // The kind and Pi name stay recorded for the same reason (`Data`
        // pins, dependent binders).
        TypedExprNode::Compose(elts) => {
            if let Some(head) = elts.first()
                && matches!(head.node, TypedExprNode::Cast { .. })
                && let Some(head_dom) = head.ty.domain()
                && let Type::Fun { domain, .. } = &mut expr.ty
                && **domain != head_dom
                && domain.peel_refinements() == head_dom.peel_refinements()
            {
                **domain = head_dom;
            }
        }
        _ => {}
    }
}

/// The canonical type of a `Cast` node: the `view`'s shape and bases (the
/// coalesced view at inference time; the rebuilt type after a rebuild pass),
/// carrying the refinements the **term** determines — the value's own domain refinements
/// plus the `born` target's refinement set. Inference and the rebuild passes
/// resolve a cast's bases; they do not decide its refinements.
///
/// A cast is an *assertion*: `cast(value, {𝐷 | 𝑝} ⇒ 𝑉)` asserts exactly `𝑝` on
/// top of whatever its value already established, and both parts are fixed by
/// the term — the born refinements when the cast was written (lowering's filter, a
/// group-by's key equation), the value's refinements by the value's own type, which
/// is already canonical by induction (both callers walk bottom-up). The graph
/// view of the same position accumulates the same union on the ordinary route
/// — the upcast `value <: target` is how the value's refinements flow in — but
/// *which* refinements an occurrence's variable accumulates depends on the route
/// bounds took through the graph: an embedded copy of a cast (a comprehension
/// source cloned into a filter predicate) has its own variable, and under an
/// adversarial bound order it coalesces bare, or decorated with a sibling
/// layer's filter. Installing the view wholesale (the previous behaviour)
/// therefore made a cast's *identity* route-dependent — which refinement
/// equality, deliberately cast-target-aware, then refused to dedup. Deriving
/// the refinements from the term instead is route-independent and agrees with the
/// view on every deterministic route.
///
/// When the view's refinements already equal the term-derived set, the view is
/// installed wholesale — preserving the predicate-`Rc` sharing between the
/// target and the node type that planning's compile-once relies on.
/// `value_ty: None` computes the canonical *target* (born refinements alone);
/// `Some` computes the canonical node *type* (value's domain refinements ∪ born).
///
/// A cast re-views its value **at the target**, so the data-vs-capability answer comes from
/// `born` — `emit_cast` reads it there, and a view rebuilt from a neighbour's type states
/// whatever that neighbour was. A predicate's chain is a capability (`base ⇒ Bool`), so a
/// collection cast collapsing inside one is where the two part company. Only that answer
/// travels: the binder slot is named at each type's own domain position
/// (`src/ccl/design/type-inference.md`, "4.6 Data vs compute functions"), so a view keeps
/// the slot it has.
pub(crate) fn canonical_cast_ty(born: &Type, value_ty: Option<&Type>, view: Type) -> Type {
    let at_born_answer = |mut t: Type| {
        if let (Some(b), Type::Fun { fun_kind, .. }) = (born.fun_kind(), &mut t)
            && b.resolved().is_data() != fun_kind.resolved().is_data()
        {
            *fun_kind = if b.resolved().is_data() {
                crate::ccl::ty::FunKind::Data(None)
            } else {
                crate::ccl::ty::FunKind::Compute
            };
        }
        t
    };
    let born_refinements = match born.domain() {
        Some(d) => d.refinements().to_vec(),
        None => return at_born_answer(view),
    };
    let Some(view_dom) = view.domain() else {
        return at_born_answer(view);
    };
    // The term-determined refinement set: value's domain refinements (type position
    // only) ∪ born refinements.
    let mut canon_refinements: RefinementSet = value_ty
        .and_then(|t| t.domain())
        .map(|d| d.refinements().to_vec())
        .unwrap_or_default()
        .into_iter()
        .collect();
    canon_refinements.extend(born_refinements);
    let view_refinements = view_dom.refinements();
    let same = canon_refinements.len() == view_refinements.len()
        && view_refinements
            .iter()
            .all(|r| canon_refinements.contains(r));
    if same {
        return at_born_answer(view);
    }
    let cod = view
        .codomain()
        .expect("a type with a domain has a codomain");
    at_born_answer(Type::fun_like(
        &view,
        Type::refined(view_dom.peel_refinements().clone(), canon_refinements),
        cod,
    ))
}

/// Wrap `base` in a fresh `Type::Refinement` whose bare predicate filters the
/// element by the point-free function `predicate : base ⇒ Bool` (stored as
/// `__elem ▷ predicate`, see [`bare_predicate_of_fn`]). Returns `base` unchanged
/// when the predicate is trivially true.
pub(crate) fn refine_with(base: Type, predicate: &Expr) -> Type {
    if is_trivially_true_predicate(predicate) {
        return base;
    }
    let bare = bare_predicate_of_fn(&base, predicate.clone());
    Type::refined_one(base, Refinement::born(Rc::new(bare)))
}

/// Is `bare` the trivially-true predicate in **bare** form, `__elem ▷ (true ▷ const)`?
///
/// [`is_trivially_true_predicate`] recognises the predicate *function*; a
/// refinement stores it applied to the element binder, so it needs peeling first.
pub fn is_trivially_true_bare_predicate(bare: &Expr) -> bool {
    matches!(&bare.node, TypedExprNode::Apply { argument, function }
        if matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem())
            && is_trivially_true_predicate(function))
}

/// Refine `base` by an already-**bare** predicate (`__elem ▷ p`), degenerating to
/// `base` when the predicate is trivially true.
///
/// The degeneracy is the same one [`refine_with`] applies to a predicate
/// *function*, and it is not cosmetic: `{D | true}` and `D` describe the same
/// extent, but they are distinct types, and a data domain is invariant — so a
/// producer carrying the bare form cannot meet a consumer carrying the refined
/// one. [`is_trivially_true_predicate`] only recognises the function `true ▷ const`;
/// wrapped as `__elem ▷ (true ▷ const)` it needs peeling first.
pub fn refine_with_bare(base: Type, bare_predicate: &Expr) -> Type {
    if is_trivially_true_bare_predicate(bare_predicate) {
        return base;
    }
    Type::refined_one(base, Refinement::born(Rc::new(bare_predicate.clone())))
}

/// Count free occurrences of `name` in `expr`, including occurrences in
/// any refinement predicates carried by the expression's type.
///
/// A variable is *free* at a use site when no binder inside `expr` shadows the
/// name on the path to that use; the count is the number of such free uses.
/// The shadowing rules are not restated here — the walk folds over
/// [`crate::ccl::scope::for_each_scoped_item`], which declares them once for the
/// whole crate. Consequently [`TypedExprNode::Feed`] / [`TypedExprNode::Define`]
/// / [`TypedExprNode::MutWrite`] target names count as occurrences (they are
/// *uses* of the handle / mutable variable), while a
/// [`TypedExprNode::Transact`] mutable variable key does not (it is a field label).
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
    // The term spine is a fold over the shared scoping walk: a child whose
    // binder list mentions `name` is shadowed and contributes nothing;
    // everything else recurses. Variable-key labels (`KeyRef`) are not variable
    // occurrences, so they do not count.
    let mut in_node = 0;
    for_each_scoped_item(expr, &mut |item| match item {
        ScopedItem::VarRef(n) => in_node += (n == name) as usize,
        ScopedItem::KeyRef(_) => {}
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            if !binders.shadows(name) {
                in_node += count_free_with_visited(name, child, visited);
            }
        }
    });
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

/// Which witnesses `expr`'s type slots name — the witness analog of [`is_free`], for the
/// whole subtree in one traversal.
///
/// Every occurrence is free: a witness is bound by a Σ, which is a type, so nothing in a
/// *term* binds one. A type slot that carries its own Σ is handled inside
/// [`crate::ccl::ty::free_witness_refs`], which excludes what that Σ binds.
pub fn free_witnesses(expr: &Expr) -> BTreeSet<crate::ccl::ty::WitnessId> {
    fn go(e: &Expr, out: &mut BTreeSet<crate::ccl::ty::WitnessId>) {
        e.walk_type_slots(|ty| out.extend(crate::ccl::ty::free_witness_refs(ty, &[])));
        e.walk_children(|c| go(c, out));
    }
    let mut out = BTreeSet::new();
    go(expr, &mut out);
    out
}

/// Type every read of the refinement binder **from the base**, at the path it reads.
///
/// `__elem` ranges over the base, so a read of it at path `p` has the type the base has at
/// `p` and carries no information of its own. Coalesce resolves the predicate's slots against
/// a graph that does not contain the `Σ` the refinement rides, so it answers them from the
/// names its own route carried — a second answer to a question the base has already
/// answered. This installs the base's, which is the only one that can be right.
///
/// **A projection's own function type is `base(p) ⇒ base(p ++ [k])`**, so it is rebuilt from
/// the same two ends rather than left holding the spelling the read no longer has.
///
/// **The base's shape, the slot's refinements.** The binder's slot is deliberately bare where
/// the base carries refinements, and what a read has narrowing it is its own business — a
/// nested filter's inner predicate sees the outer refinement and the base does not carry it
/// yet. So only the part that says *which index* is taken from the base.
pub(crate) fn type_element_reads_from_base(pred: &mut Expr, base: &Type) {
    /// `expr`'s own path if it reads the element, retyping every read at or below it.
    fn go(expr: &mut Expr, base: &Type) -> Option<Vec<ProjKey>> {
        match &mut expr.node {
            TypedExprNode::Var(n) if n.is_elem() => {
                if let Some(t) = base_at(base, &[]) {
                    take_index_from(&mut expr.ty, t);
                }
                return Some(Vec::new());
            }
            TypedExprNode::Apply { function, argument }
                if matches!(&function.node, TypedExprNode::Proj(_)) =>
            {
                let mut path = go(argument, base)?;
                let TypedExprNode::Proj(key) = &function.node else {
                    unreachable!("guarded by the match arm")
                };
                let from = base_at(base, &path).cloned();
                path.push(key.clone());
                let to = base_at(base, &path).cloned();
                // Both ends or neither: a path the base does not have is a read of something
                // the base is not, and half-retyping it would leave the node disagreeing
                // with its own function slot.
                if let (Some(from), Some(to)) = (from, to) {
                    take_index_from(&mut expr.ty, &to);
                    let mut fn_from = argument.ty.clone();
                    take_index_from(&mut fn_from, &from);
                    function.ty = Type::fun(fn_from, expr.ty.clone());
                }
                return Some(path);
            }
            _ => {}
        }
        // The `&mut` walk yields a scope and then the run of children it covers, so this
        // pairs them: a binder of the same name makes the occurrences below it a different
        // variable, and its whole run is skipped. Local to this frame, so a nested read
        // keeps its own answer.
        let mut shadowed = false;
        crate::ccl::scope::for_each_scoped_item_mut(expr, &mut |item| match item {
            crate::ccl::scope::ScopedItemMut::Scope(names) => {
                shadowed = names.iter().any(|n| n.is_elem());
            }
            crate::ccl::scope::ScopedItemMut::Child(child) if !shadowed => {
                go(child, base);
            }
            _ => {}
        });
        None
    }
    go(pred, base);
}

/// Re-base `slot` on `from`'s shape, keeping `slot`'s own refinements.
fn take_index_from(slot: &mut Type, from: &Type) {
    let refinements = slot.refinements().iter().cloned().collect();
    *slot = Type::refined(from.peel_refinements().clone(), refinements);
}

/// The base at a projection path — the type a read of the element at that path has.
///
/// Through refinements: a projection reads a *position*, and a restriction on the product
/// says nothing about which index that position names.
fn base_at<'a>(base: &'a Type, path: &[ProjKey]) -> Option<&'a Type> {
    let mut ty = base;
    for key in path {
        ty = match (ty.peel_refinements(), key) {
            (Type::Tuple(ts), ProjKey::Index(i)) => ts.get(*i)?,
            (Type::Record(fs), ProjKey::Field(n)) => &fs.iter().find(|(k, _)| k == n)?.1,
            _ => return None,
        };
    }
    Some(ty)
}

/// Which of `candidates` occur free in `expr`, in **one** traversal.
///
/// Same shadowing rules as [`count_free`] — this is that fold with the single
/// name generalized to a set — but it answers for the whole set at once, where
/// [`is_free`] per candidate walks `expr` once *per name*. Callers that select a
/// live subset of a wide environment want this: the per-name form makes the
/// selection cost `|candidates| × |expr|`, worth 10–22% of whole-program compile
/// time at the widths the mutability phases reach and growing with block length
/// (see [`crate::ccl::subst::Subst::discharge_env_in_place`]).
///
/// Shadowing is per-name, so the candidate set *narrows* as the walk crosses a
/// binder rather than the walk aborting: a scope that shadows one candidate says
/// nothing about the others.
pub fn free_among<'a>(
    candidates: impl IntoIterator<Item = &'a Name>,
    expr: &Expr,
) -> BTreeSet<Name> {
    let live: BTreeSet<Name> = candidates.into_iter().cloned().collect();
    let mut out = BTreeSet::new();
    free_among_go(&live, expr, &mut out);
    out
}

/// Recursive worker for [`free_among`]. `live` is the candidates not yet shadowed
/// at this depth; `out` accumulates the ones found free.
fn free_among_go(live: &BTreeSet<Name>, expr: &Expr, out: &mut BTreeSet<Name>) {
    if live.is_empty() {
        return;
    }
    // A binder's declared type is in the *enclosing* scope, so every candidate is
    // unshadowed in a type slot — the same rule (and the same reason) as
    // `count_free`, which walks slots before applying any shadowing. Each name
    // gets its own `visited` set via `is_free_in_type`, which is what terminates
    // on a self-referential refinement.
    expr.walk_type_slots(|ty| {
        for name in live {
            if !out.contains(name) && is_free_in_type(name, ty) {
                out.insert(name.clone());
            }
        }
    });
    for_each_scoped_item(expr, &mut |item| match item {
        ScopedItem::VarRef(n) => {
            if live.contains(n) {
                out.insert(n.clone());
            }
        }
        // A register key is a field label, not a variable occurrence.
        ScopedItem::KeyRef(_) => {}
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            // Narrow only when the scope actually shadows a candidate; the common
            // case recurses on the borrowed set with no allocation.
            if live.iter().any(|n| binders.shadows(n)) {
                let inner: BTreeSet<Name> = live
                    .iter()
                    .filter(|n| !binders.shadows(n))
                    .cloned()
                    .collect();
                free_among_go(&inner, child, out);
            } else {
                free_among_go(live, child, out);
            }
        }
    });
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

/// Every name free in `expr`'s **value** — the set counterpart of
/// [`is_free_in_value`], for when the question is *which* names escaped rather than
/// whether a particular one did.
///
/// A pass that only rearranges a tree can check itself against this: its output's free
/// names must be a subset of its input's, since rearranging binds no new outside name.
/// That is a post-condition a pass which moves statements between scopes cannot
/// establish by construction, and one whose violation is otherwise found much later —
/// a reference that escaped its binder survives every typecheck and surfaces as an
/// unrecognised variable in op-conversion.
pub fn free_names_in_value(expr: &Expr) -> HashSet<Name> {
    fn go(e: &Expr, bound: &mut Vec<Name>, out: &mut HashSet<Name>) {
        for_each_scoped_item(e, &mut |item| match item {
            ScopedItem::VarRef(n) => {
                if !bound.contains(n) {
                    out.insert(n.clone());
                }
            }
            // A key label names a field of the history record the node denotes, not a
            // variable use — the same exclusion `count_free_in_value` makes.
            ScopedItem::KeyRef(_) => {}
            ScopedItem::Child { expr, binders } => {
                let depth = bound.len();
                bound.extend(binders.iter().map(|b| b.name.clone()));
                go(expr, bound, out);
                bound.truncate(depth);
            }
        });
    }
    let mut out = HashSet::new();
    go(expr, &mut Vec::new(), &mut out);
    out
}

/// Value-only worker for [`is_free_in_value`]: the same fold over
/// [`crate::ccl::scope::for_each_scoped_item`] as [`count_free`], minus the type
/// slots (so a refinement on a `Lambda` param — which lives in the type — is
/// ignored).
fn count_free_in_value(name: &Name, expr: &Expr) -> usize {
    let mut sum = 0;
    for_each_scoped_item(expr, &mut |item| match item {
        ScopedItem::VarRef(n) => sum += (n == name) as usize,
        ScopedItem::KeyRef(_) => {}
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            if !binders.shadows(name) {
                sum += count_free_in_value(name, child);
            }
        }
    });
    sum
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
    if let Type::Refinement(_, refinements) = ty {
        for refinement in refinements {
            if visited.insert(refinement.predicate_id()) {
                f(&refinement.predicate, visited);
            }
        }
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
            replacing: false,
        })))
    }
}

impl<C> PredMemo<C> {
    /// A memo whose rebuilds **replace** the terms they are handed, so the
    /// rebuilt term keeps the original's `NodeId`s.
    ///
    /// Only sound when the owning walk reaches **every** occurrence of every
    /// predicate it rebuilds. A predicate is an `Rc` shared across many type
    /// slots and a rebuild cannot mutate through it, so it builds a new `Rc` and
    /// repoints the refinement it was given. If some other type still holds the
    /// original, the two coexist — and preserving ids then puts one id-set on two
    /// live terms, which `assert_unique_node_ids`' predicate walk reports at the
    /// next phase boundary.
    ///
    /// [`uniquify`](crate::ccl::uniquify) is the one caller entitled to this: it
    /// walks the whole tree, and asserts the resulting 1:1 correspondence
    /// (N distinct terms in, N out, same ids) on every compile.
    ///
    /// Every other caller rebuilds within a single type while the original may
    /// survive elsewhere. Those are *derivations*, and [`Default`] gives them the
    /// recording behaviour they need.
    pub fn replacing() -> Self {
        let m = Self::default();
        m.0.borrow_mut().replacing = true;
        m
    }

    fn is_replacing(&self) -> bool {
        self.0.borrow().replacing
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
    /// See [`PredMemo::replacing`]: the owning walk reaches every occurrence, so
    /// a rebuild is a replacement and keeps the original's ids.
    replacing: bool,
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
    /// TODO(discarded-copy): a `false` report still pays for a full copy. `f`
    /// takes `&mut Expr`, so the predicate is cloned before there is any way to
    /// know whether `f` will change it, and a `false` answer discards the clone.
    /// The copy is captured and recorded like any other, so the table gains
    /// entries for nodes no tree ends up holding. Neither a correctness nor a
    /// soundness gap — it bloats the table.
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
        let (keepalive, before) = {
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
                    let rev = store.revision;
                    (keepalive, rev)
                }
            }
        };
        // The copy and the rewrite run together under the memo's declared intent
        // — `f` mints and copies *into* the term, so its products belong to
        // whichever the rebuild is.
        //
        // **Replacing** (see [`PredMemo::replacing`]): the rebuilt term stands in
        // for the original everywhere, so it is the same logical predicate at a
        // new allocation and keeps its ids.
        //
        // **Deriving** (the default): the original may survive on a type this
        // walk never reaches, so the rebuilt term is a genuinely new one. It
        // freshens, recorded against the source predicate's own root, which records
        // it as derived from the term it was rebuilt from.
        let (pred, reported) = if self.is_replacing() {
            crate::ccl::provenance::preserving_ids(|| {
                let mut pred = (*keepalive).clone();
                let reported = f(&mut pred);
                (pred, reported)
            })
        } else {
            let _g = crate::ccl::provenance::enter(
                keepalive.node_id(),
                "predicate.rebuild",
                crate::ccl::provenance::Nature::Machinery,
            );
            let mut pred = (*keepalive).clone();
            let reported = f(&mut pred);
            (pred, reported)
        };
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
        // Copy and rewrite under the memo's declared intent; see `rebuild`.
        let pred = if self.0.is_replacing() {
            crate::ccl::provenance::preserving_ids(|| {
                let mut pred = (*keepalive).clone();
                f(&mut pred);
                pred
            })
        } else {
            let _g = crate::ccl::provenance::enter(
                keepalive.node_id(),
                "predicate.rebuild",
                crate::ccl::provenance::Nature::Machinery,
            );
            let mut pred = (*keepalive).clone();
            f(&mut pred);
            pred
        };
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
        if let Type::Refinement(_, refinements) = ty {
            for r in refinements {
                if seen.insert(r.predicate_id()) {
                    out.push(r.clone());
                    // A predicate's own subexpressions carry further refinements.
                    in_expr(&r.predicate, out, seen);
                }
            }
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
    if let Type::Refinement(_, refinements) = ty {
        refinements.rewrite_each(|_, refinement| {
            changed |= memo.rebuild(refinement, context, |pred| f(pred, memo));
        });
    }
    ty.walk_children_mut(|child| changed |= walk_refined_predicates_mut(child, memo, context, f));
    changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::ty::TypeKind;

    /// **A realized conditional inside a predicate is caught at the planning wall.**
    ///
    /// A predicate looks its collection up at an index; it never sweeps one, and it may
    /// carry no `iterate`/`restrict` to sweep with. Realizing a conditional source inside a
    /// predicate produces exactly the forbidden thing — a gated union whose legs need those
    /// markers — and the marker check alone cannot see it, because the union arrives with
    /// *no* markers at all. Without this the failure is a wrong arm at runtime, four passes
    /// downstream.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "must be *iterated* reached a refinement predicate")]
    fn a_source_needing_iteration_in_a_predicate_is_caught() {
        let arm = |n| {
            Expr::new(TypedExprNode::Var(Name::from("xs"))).with_ty(Type::data_fun(
                Type::UIntRange(n),
                Type::Base(BaseType::Int),
            ))
        };
        let realized = Expr::new(TypedExprNode::Realize(Box::new(
            Expr::new(TypedExprNode::Copair(vec![arm(2), arm(3)])).with_ty(Type::data_fun(
                Type::UIntRange(2),
                Type::Base(BaseType::Int),
            )),
        )))
        .with_ty(Type::data_fun(
            Type::UIntRange(2),
            Type::Base(BaseType::Int),
        ));
        let ty = Type::refined_one(Type::UIntRange(2), Refinement::born(Rc::new(realized)));
        debug_assert_no_iteration_markers_in_type(&ty);
    }

    /// `{[0, 2] | __elem}` — a refined range. The predicate's content is irrelevant
    /// here; only that the two sides carry *different* ones.
    fn refined(base: Type, tag: &str) -> Type {
        Type::refined_one(base, Refinement::born(Rc::new(Expr::var(Name::from(tag)))))
    }

    /// A Σ's candidates are **domains**, matched by value, so two sums differing only
    /// in a candidate's refinement are different types — one is the filtered arm and
    /// the other is not. Erasing there would collapse that distinction, which is a
    /// stronger claim than "these two spellings of one predicate are the same".
    #[test]
    fn strip_refinements_keeps_a_sum_s_candidates_distinct() {
        let int = Type::Base(BaseType::Int);
        let filtered = Type::sum_over(
            TypeKind::Enumerated(vec![refined(Type::UIntRange(3), "p")]),
            None,
            int.clone(),
        );
        let bare = Type::sum_over(TypeKind::Enumerated(vec![Type::UIntRange(3)]), None, int);
        assert_ne!(strip_refinements(&filtered), strip_refinements(&bare));
        assert_eq!(strip_refinements(&filtered), filtered);
    }

    /// A composition's fun kind comes from the element whose domain it inherits — the first.
    /// Composing an element map onto a collection does not stop it being one, and
    /// `Type::fun`'s hardcoded `Compute` was discarding the fun kind at every point-free
    /// rebuild, which is exactly what [`Type::fun_like`] exists to prevent.
    #[test]
    fn typed_compose_keeps_the_chain_s_kind() {
        let int = Type::Base(BaseType::Int);
        let coll =
            Expr::var(Name::from("xs")).with_ty(Type::data_fun(Type::UIntRange(2), int.clone()));
        let map = Expr::var(Name::from("f")).with_ty(Type::fun(int.clone(), int.clone()));
        let composed = typed_compose(vec![coll, map]);
        assert!(
            matches!(
                &composed.ty,
                Type::Fun {
                    fun_kind: crate::ccl::ty::FunKind::Data(..),
                    ..
                }
            ),
            "a collection composed with an element map is still a collection, got {}",
            composed.ty
        );
    }
}

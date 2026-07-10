//! A single pre-lambda-elim inlining pass that substitutes `Let` bindings at
//! their call sites for UDFs with non-iterable domains.
//!
//! # [`inline_non_iterable_lambdas`] — inlines `Let` bindings for functions with non-iterable domains
//!
//! Runs **before** [`crate::ccl::lambda_elim`].  Inlines any `Let` binding
//! (selected by [`should_inline`]) whose domain is not natively iterable by the
//! operator graph.  This covers:
//!
//! - **Scalar UDFs**: `Fun(non_iterable_domain, codomain)`.  These have a
//!   non-iterable (non-enumerable) domain.  Syntactic multi-arg Python lambdas
//!   (`lambda x, y: …`) are uncurried at lowering to `Tuple([…]) → T`, so they
//!   match this rule too.
//!
//! - **List-producing UDFs**: `Fun(Fun(iterable_domain, _), _)`.  Functions
//!   whose domain is itself a function type — generator functions and
//!   list-returning `def`s lowered to `λ user_arg → λ __iter_record → body`.
//!   A `Fun` domain has no iterable extent, so these are covered by the same
//!   non-iterable-domain rule.
//!
//! After substituting the bound lambda at each call site, the resulting
//! `Apply(arg, Lambda(x, body))` nodes are beta-reduced so that downstream
//! passes (lambda-elim, operator conversion) see fully-reduced expressions.
//! Multi-arg uncurried call sites leave behind `Apply(Tuple, Proj(Index(i)))`
//! references; those are folded by [`crate::ccl::simplify`]'s
//! `try_literal_tuple_projection` rule, not here.
//!
//! # Why a single pre-lambda-elim pass works for both
//!
//! Lambda-elim recurses into `Apply` nodes, so an `Apply(arg, Lambda)` produced
//! by inlining a scalar UDF before lambda-elim is handled correctly — the
//! `Lambda` inside the `Apply` gets converted to a combinator by lambda-elim as
//! usual.  Both scalar and list-producing UDFs benefit from the same
//! per-call-site beta-reduction performed here, making a separate post-elim
//! pass unnecessary.
//!
//! # Limitations
//!
//! - **Recursive UDFs** are not supported (already noted in operator conversion).
//! - **Body duplication**: if a scalar UDF is called N times, its body appears N
//!   times in the operator graph. Acceptable for now; caching is only needed for
//!   collection-typed UDFs (iterable domain), which are not inlined.
//!
//! # Alias inlining
//!
//! In addition to UDF inlining, this pass eliminates `Let` bindings
//! whose right-hand side is a plain `Var` (`let y = x in body` →
//! `body[y → x]`).  Running this before [`crate::ccl::lambda_elim`]
//! prevents the let-in-lambda rule from hoisting such bindings into
//! `const(x)` wrappers, which would otherwise require special
//! recognition downstream.
//!
//! This pass runs **before** [`crate::ccl::desugar_defers`] (so the unified
//! letrec phase can route an in-loop feed against inlined writers, and a
//! defer-mediating UDF reaches its call site before desugar routes it), so it
//! *does* see [`Defer`]/[`Feed`]/[`Define`] nodes and `Type::Feed` domains.
//! Beta-reduction goes through the defer-aware [`crate::ccl::subst::Subst`]
//! engine, whose `Feed`/`Define` arms rename a fed-to handle correctly when a
//! defer-mediating UDF is inlined (`g(mydefer)` for `def g(out): out << e`
//! renames `out` → `mydefer`). Generators are defer-returning (their body ends
//! in the yield-defer), so inlining preserves their output.
//!
//! [`Defer`]: crate::ccl::TypedExprNode::Defer
//! [`Feed`]: crate::ccl::TypedExprNode::Feed
//! [`Define`]: crate::ccl::TypedExprNode::Define

use std::collections::HashSet;

use crate::ccl::{
    Expr, Lit, Name, Type, TypedExprNode,
    ccl_utils::walk_refined_predicates_mut,
    lambda_elim::substitute,
    node_recorder::NodeRecorder,
    provenance::{NodeId, Pass},
};

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Inline `Let` bindings for UDFs with non-iterable domains and beta-reduce
/// their call sites.
///
/// Runs **before** [`crate::ccl::lambda_elim`].  Walks the expression tree and
/// substitutes each matching UDF at every free occurrence of its binding name
/// in the body, beta-reducing at each call site, then drops the `Let` wrapper.
///
/// Inlines any function whose domain is not natively iterable (see
/// [`should_inline`]): scalar UDFs, list-producing UDFs, and curried functions
/// all qualify.  Only bindings whose domain is natively iterable (`UIntRange`,
/// `DataSource`) are left intact.
///
/// Literal tuple projections that arise from uncurried multi-arg call sites
/// are *not* folded here — `crate::ccl::simplify` handles that rewrite as a
/// general rule so it fires consistently throughout the tree.
pub fn inline_non_iterable_lambdas(expr: Expr) -> Expr {
    inline_with_records(expr).0
}

/// Inline as [`inline_non_iterable_lambdas`], but also return the
/// [`NodeRecorder`] describing this pass's construction edges (see
/// [`crate::ccl::node_recorder`]).
///
/// Inline is **id-preserving**: a rebuilt node carries its input [`NodeId`], so
/// most of the tree is an implicit Preserve (nothing recorded). The only
/// recorded deviations are:
///
/// * [`Discarded`](crate::ccl::node_recorder::NodeRecord::Discarded) — the `Let`
///   wrappers, beta-reduction redexes, lambda wrappers, and `Var` occurrences a
///   rewrite removes. Recorded at each inlining site by diffing the subtree it
///   consumes against the subtree it produces (see [`record_drops`]).
/// * [`Replicated`](crate::ccl::node_recorder::NodeRecord::Replicated) — the
///   fan-out at a multi-use call site. A UDF/alias used N times duplicates its
///   body/value N times; [`dedup_and_record`] keeps the first occurrence (the
///   input id survives = a Preserve) and freshens the rest, recording each as a
///   copy of the input node it mirrors.
///
/// There is intentionally no `Minted` and no `Fused`: inline neither invents
/// nodes nor collapses clusters (tuple-projection folding lives in
/// `crate::ccl::simplify`).
pub(crate) fn inline_with_records(expr: Expr) -> (Expr, NodeRecorder) {
    let mut rec = NodeRecorder::new(Pass::Inline, &expr);
    let mut expr = inline_impl(expr, &mut rec);
    // Beta-reduction rebuilds predicates on `expr.ty` (immutable terms); keep
    // each `Cast`'s `target` slot in step so the post-pass typecheck matches.
    crate::ccl::ccl_utils::sync_cast_targets(&mut expr);
    // Restore id uniqueness last. Throughout the walk every node keeps an input
    // id (fan-out duplicates it in place, so the tree carries repeated input
    // ids but never a fresh one); this single sweep is the *only* place a fresh
    // id is minted, and every one is recorded as a `Replicated` copy. Running it
    // once over the final tree makes the first occurrence of each id — anywhere
    // — the preserved one, which is what `reconcile` checks.
    dedup_and_record(&mut expr, &mut rec);
    (expr, rec)
}

// ---------------------------------------------------------------------------
// Domain extent predicates
// ---------------------------------------------------------------------------

/// Returns `true` when `ty` has a finite, enumerable extent — i.e., when the
/// operator graph can natively schedule a function over this domain as
/// `IterateExtent` without inlining.
///
/// | Type | Iterable? | Reason |
/// |------|-----------|--------|
/// | `Base(_)` | no | No finite enumeration of all integers / strings / bools |
/// | `Tuple(ts)` | yes only if ALL `t` are iterable | A tuple can only be iterated if every component can |
/// | `Record(fields)` | yes only if ALL fields are iterable | Same logic as tuples: a record with an unbounded field has no finite extent |
/// | `Refinement(inner, _)` | same as `inner` | Refinement doesn't add iterability |
/// | `UIntRange(_)` | yes | Finite, bounded range |
/// | `DataSource(_)` | yes | Externally-backed finite collection |
/// | `Fun(_, _)` as domain | no | Infinitely many possible functions; cannot enumerate |
/// | anything else | yes | Conservative default: assume iterable so unknown types are not inlined |
fn is_iterable_domain(ty: &Type) -> bool {
    match ty {
        Type::Base(_) => false,
        // A tuple domain is iterable only if ALL components are iterable; you
        // can't enumerate (UIntRange(3), Int) because Int is unbounded.
        Type::Tuple(ts) => ts.iter().all(is_iterable_domain),
        // Records are structurally equivalent to tuples for extent purposes.
        Type::Record(fields) => fields.iter().all(|(_, t)| is_iterable_domain(t)),
        // Refinement inherits the iterability of its base type.
        Type::Refinement(inner, _) => is_iterable_domain(inner),
        // Natively iterable types.
        Type::UIntRange(_) | Type::DataSource(_) => true,
        // There are infinitely many possible functions for any given function
        // type, so function-typed domains cannot be enumerated.
        Type::Fun {
            domain: _,
            codomain: _,
            ..
        } => false,
        // Inlining now runs *before* desugar_defers, so a defer-handle domain
        // is reachable (a defer-mediating UDF `λ out → out << e` has domain
        // `Feed(ρ)`). A handle has no enumerable extent — treat it as
        // non-iterable like a function, so such a UDF is inlined (its call
        // sites beta-reduce, renaming the fed-to handle; see
        // `Subst::handle_target`).
        Type::Feed(_) => false,
        // A `Mut` reference (pass-by-ref param domain) has no enumerable
        // extent — treat it non-iterable like a function/feed so a
        // `Mut`-param UDF is inlined; the `_ => true` fallthrough would
        // otherwise strand it.
        Type::Mut { .. } => false,
        _ => true,
    }
}

/// Returns `true` when a `Let` binding of type `bound_ty` should be inlined.
///
/// Inlines `Let` bindings for functions whose domain is not iterable — i.e.,
/// domains the operator graph cannot natively schedule as `IterateExtent`.
/// This covers scalar UDFs (`Fun(Int, Int)`, `Fun(Tuple(Int,Int), Int)`, …),
/// list-producing UDFs (`Fun(Fun(UIntRange,Int), Fun(UIntRange,Int))`, …), and
/// curried functions (`Fun(Int, Fun(Int, Int))`, …): all of them have
/// non-iterable domains and cannot be compiled as standalone operators by
/// operator conversion.
///
/// # What is NOT inlined
///
/// Functions over natively iterable domains (`UIntRange`, `DataSource`) have a
/// domain the operator graph can natively schedule and iterate.  They compile
/// correctly as standalone `Let` bindings via `Memo + Splitter` and benefit
/// from sharing, so they are left intact.
fn should_inline(bound_ty: &Type) -> bool {
    match bound_ty {
        Type::Fun {
            domain,
            codomain: _,
            ..
        } => !is_iterable_domain(domain),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Alias and defer helpers
// ---------------------------------------------------------------------------

/// Returns `true` if `name` is bound (shadowed) anywhere inside `expr` — by a
/// `Let` binder or a `Lambda` parameter.
///
/// Used to guard alias inlining: substituting `y → x` in a body that rebinds
/// `x` via an inner `let x = …` or `λ x → …` would cause the substituted `x`
/// references to be captured by the shadowing binding, producing incorrect
/// semantics.
fn is_let_bound(name: &Name, expr: &Expr) -> bool {
    match &expr.node {
        // A Let whose binding matches `name` is a definitive bind site.
        TypedExprNode::Let { binding, .. } if &binding.name == name => true,
        // A Lambda param shadows `name` inside the body — treat it as a binding
        // site so we don't substitute through it.
        TypedExprNode::Lambda { param, .. } if &param.name == name => true,
        // A LetRec with any group binder matching `name` is a definitive
        // bind site (the group scopes every binding body and the letrec body).
        TypedExprNode::LetRec { bindings, .. } if bindings.iter().any(|(b, _)| &b.name == name) => {
            true
        }
        // A For whose target matches `name` shadows it inside the body.
        TypedExprNode::For { target, .. } if &target.name == name => true,
        TypedExprNode::Error => crate::unexpected_error_node!(),
        // A `Case` branch's structural pattern binds its payload name,
        // shadowing `name` inside that branch's guard/body; `any_child`
        // can't see binding names, so check explicitly. (Guard-only
        // branches have `pattern: None` and never shadow.)
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            scrutinee.as_ref().is_some_and(|s| is_let_bound(name, s))
                || branches.iter().any(|b| {
                    if b.pattern.as_ref().is_some_and(|p| &p.binding.name == name) {
                        false
                    } else {
                        is_let_bound(name, &b.guard) || is_let_bound(name, &b.body)
                    }
                })
        }
        _ => expr.any_child(|e| is_let_bound(name, e)),
    }
}

// ---------------------------------------------------------------------------
// Tree walk
// ---------------------------------------------------------------------------

/// Recursively inline `Let` bindings that pass [`should_inline`], beta-reducing
/// each call site as the substitution produces it.
///
/// Also applies alias inlining (eliminates `let y = x` via α-renaming)
/// before the UDF-inlining check.  Running it before
/// [`crate::ccl::lambda_elim`] prevents the let-in-lambda rewrite from
/// wrapping aliases in `const(…)`.
///
/// This pass runs **before** [`crate::ccl::desugar_defers`] (see the module
/// docs), so it *does* encounter `Defer`/`Feed`/`Define` nodes; beta-reduction
/// routes them through the defer-aware [`crate::ccl::subst::Subst`] engine,
/// which renames a fed-to handle when a defer-mediating UDF is inlined. The
/// defer-returning lift itself lives in `desugar_defers::try_lift_defer`.
fn inline_impl(expr: Expr, rec: &mut NodeRecorder) -> Expr {
    // Carry `node_id` through every rebuild: reconstructing a node with
    // inlined children is a Preserve (the same node, same identity), so the
    // input id must flow onto the rebuilt `Expr` rather than being re-minted.
    let Expr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;

    let new_node = match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_expr = inline_impl(*bound_expr, rec);
            let body = inline_impl(*body, rec);

            // Alias: `let y = x` is pure α-renaming — substitute y → x in body
            // and drop the Let.  This must run before lambda_elim so that the
            // let-in-lambda rule never wraps such aliases in `const(x)`.
            //
            // Guard: only safe when x is not re-bound inside body.  If body
            // contains `let x = …` the substitution would capture those x
            // references under the wrong binding (e.g. `x = 1; y = x; x += 4;
            // y` must return 1, not 5).
            if let TypedExprNode::Var(repl_name) = &bound_expr.node
                && !is_let_bound(repl_name, &body)
            {
                // The `Let` wrapper and every `Var(binding.name)` occurrence
                // vanish (each occurrence is overwritten by a copy of the
                // `Var(x)` bound expr, whose own id survives via those copies —
                // or is dropped when the alias is unused).
                let consumed = consumed_subtree_ids(node_id, &bound_expr, &body);
                let result = substitute(body, &binding.name, &bound_expr);
                record_drops(&consumed, &result, rec);
                return result;
            }

            if should_inline(&bound_expr.ty) {
                // Substitute the bound Lambda at every free occurrence of the
                // binding name in the body, beta-reducing at each call site.
                //
                // Safety: substitution is not capture-avoiding, but this is
                // safe here because lowering assigns unique binding names per
                // scope — no free variable in `bound_expr` can shadow a binder
                // introduced in `body`.
                //
                // The `Let` wrapper, the lambda wrapper + `Apply` redex consumed
                // at each beta-reduced site, and every `Var(binding.name)`
                // occurrence vanish; the lambda *body*'s ids survive via
                // substitution (fanned out to N sites, deduped later). Diffing
                // the consumed subtree against the reduced result records
                // exactly those drops — including the whole bound lambda when
                // the binding is unused.
                let consumed = consumed_subtree_ids(node_id, &bound_expr, &body);
                let reduced = inline_and_beta_reduce(body, &binding.name, &bound_expr);
                record_drops(&consumed, &reduced, rec);
                // Re-run inline_impl after beta-reduction so that newly created
                // Let bindings (e.g. `let y = (let x = Defer in …) in …` after
                // expanding a defer-returning UDF) are eligible for the alias
                // and lift rewrites on the second pass; that recursion records
                // its own drops at the nested sites.
                return inline_impl(reduced, rec);
            }
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(bound_expr),
                body: Box::new(body),
            }
        }

        // ANF defer-returning Compose source: when the first element of a Compose
        // (i.e. the for-loop iteration source) is itself a defer-returning
        // expression, wrap it in a fresh `let __for_src_N = source` binding so
        // that `try_lift_defer` can physically rename its inner defer handle,
        // preventing two same-named `__result` defers from coexisting in
        // `desugar_defers`. Re-running `inline_impl` on the wrapping `Let`
        // triggers `try_lift_defer` on the new binding.
        TypedExprNode::Compose(terms) => {
            TypedExprNode::Compose(terms.into_iter().map(|t| inline_impl(t, rec)).collect())
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),

        // All remaining variants: pure structural recursion, carrying the input
        // id (a Preserve).  Atoms have no children, so this is a no-op for them.
        node => {
            let mut expr = Expr {
                node_id,
                node,
                ty,
                user_annotation,
            };
            expr.map_children(|child| inline_impl(child, rec));
            return expr;
        }
    };

    Expr {
        node_id,
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Substitute `lambda` at every free occurrence of `name` in `expr`, and
/// beta-reduce at each call-site Apply chain — i.e. where `Var(name)` sits in
/// the function position of an `Apply(arg, …)` (optionally nested for curried
/// calls).
///
/// Only Apply chains that actually terminate in `Var(name)` participate in
/// beta-reduction. Unrelated `Apply(arg, Lambda)` patterns elsewhere in the
/// tree are left intact so lambda-elim + simplify still produce the structure
/// they expect for list comprehensions, scalar BinOps, etc.
///
/// TODO: immediately-applied anonymous lambdas (`Apply(arg, Lambda(x, body))`
/// not gated on a `Var(name)`) currently fall through this scope and survive
/// into `lambda_elim`.  They are equationally equivalent to a beta-reduction
/// here and would benefit from the same treatment, but doing so today
/// perturbs CCC simplify's input shape for list comprehensions, scalar UDFs,
/// and BinOp paths in ways that need test-suite triage first.  Revisit if a
/// case surfaces where the surviving anon-lambda blocks downstream work.
fn inline_and_beta_reduce(expr: Expr, name: &Name, lambda: &Expr) -> Expr {
    // Direct occurrence: replace the variable with the Lambda value.
    if let TypedExprNode::Var(ref n) = expr.node
        && n == name
    {
        return lambda.clone();
    }

    // Substitute inside refinement predicates riding this node's types. A
    // predicate is an expression tree the children-walk below never reaches
    // (e.g. a list-comprehension filter `f(x)` lives only in the cast-target
    // refinement), so a UDF use inside one would survive as a dangling `Var`
    // once the enclosing `Let` is dropped.
    let mut expr = expr;
    inline_in_type_predicates(&mut expr.ty, name, lambda);
    if let Some(annotation) = &mut expr.user_annotation {
        inline_in_type_predicates(annotation, name, lambda);
    }

    // Apply chain ending in `Var(name)` — beta-reduce after recursively
    // substituting the argument and collapsing the function side.
    if let TypedExprNode::Apply { function, .. } = &expr.node
        && is_name_in_function_position(function, name)
    {
        let Expr {
            node,
            ty,
            user_annotation,
            node_id,
        } = expr;
        let (function, argument) = match node {
            TypedExprNode::Apply { function, argument } => (function, argument),
            _ => unreachable!(),
        };
        let argument = inline_and_beta_reduce(*argument, name, lambda);
        let function = inline_and_beta_reduce(*function, name, lambda);
        match function.node {
            TypedExprNode::Lambda { param, body } => {
                // A domain refinement on this outer lambda would encode a
                // precondition `P(arg)` that beta reduction must preserve.
                // Such refinements ride the param's *type* (a
                // `Type::Refinement` introduced by `cast`, and copied into
                // `param.ty` by coalesce's `refresh_lambda_param_slot`);
                // current lowering of generator/list-returning `def`s puts no
                // refinement on the outer parameter (only the inner
                // `__iter_record` if-guard lambda is refined, and that is
                // never beta-reduced here). If a future lowering refines the
                // outer param, this branch needs a principled lift (e.g. a
                // `restrict(pred)` guard around the substituted body) before
                // proceeding. A hard assert, not debug_assert: the condition
                // reads a live post-inference data path, and a release build
                // proceeding past it would silently drop the precondition —
                // a wrong-results miscompile, not a recoverable state.
                assert!(
                    !matches!(param.ty, Type::Refinement(..)),
                    "inline_and_beta_reduce: outer lambda for `{name}` has a \
                         refined parameter type; beta reduction would silently drop its \
                         precondition. Extend this branch if list-UDF lowering \
                         starts producing refined outer params."
                );
                return substitute(*body, &param.name, &argument);
            }
            // Not a Lambda (e.g. the bound expression is Var("id") rather
            // than a literal lambda) — skip beta-reduction and reconstruct
            // the Apply (a Preserve: same node, substituted children) with its
            // input id carried through.
            _ => {
                return Expr {
                    node_id,
                    node: TypedExprNode::Apply {
                        function: Box::new(function),
                        argument: Box::new(argument),
                    },
                    ty,
                    user_annotation,
                };
            }
        }
    }

    // Not a call site of `name`: recurse into sub-expressions. Each recursion
    // carries the same (name, lambda) so that deeper call sites still
    // beta-reduce. This mirrors [`crate::ccl::lambda_elim::substitute`] but
    // preserves the specialised Apply-chain detection above. Rebuilding a node
    // with substituted children is a Preserve, so its input id is carried.
    let Expr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;
    let new_node = match node {
        TypedExprNode::Lambda { param, body } => {
            if &param.name == name {
                // shadowed — stop substituting inside
                TypedExprNode::Lambda { param, body }
            } else {
                TypedExprNode::Lambda {
                    param,
                    body: Box::new(inline_and_beta_reduce(*body, name, lambda)),
                }
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_bound = inline_and_beta_reduce(*bound_expr, name, lambda);
            let new_body = if &binding.name == name {
                *body
            } else {
                inline_and_beta_reduce(*body, name, lambda)
            };
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(new_bound),
                body: Box::new(new_body),
            }
        }

        // LetRec group binders shadow `name` across every binding body AND
        // the letrec body (mutual recursion), so a matching binder stops the
        // substitution for the whole group.
        TypedExprNode::LetRec { bindings, body } => {
            if bindings.iter().any(|(b, _)| &b.name == name) {
                TypedExprNode::LetRec { bindings, body }
            } else {
                TypedExprNode::LetRec {
                    bindings: bindings
                        .into_iter()
                        .map(|(b, def)| (b, inline_and_beta_reduce(def, name, lambda)))
                        .collect(),
                    body: Box::new(inline_and_beta_reduce(*body, name, lambda)),
                }
            }
        }

        // The cast target is where its refinement predicate is written —
        // `lambda_elim` and operator conversion read the predicate off the
        // target, not off `ty` — so walk it explicitly; `target` carries its
        // own predicate `Rc`, independent of the one on `ty`.
        TypedExprNode::Cast { value, mut target } => {
            inline_in_type_predicates(&mut target, name, lambda);
            TypedExprNode::Cast {
                value: Box::new(inline_and_beta_reduce(*value, name, lambda)),
                target,
            }
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),

        // The loop target shadows `name` inside the body only; the source
        // still substitutes.
        TypedExprNode::For { target, iter, body } => {
            let iter = Box::new(inline_and_beta_reduce(*iter, name, lambda));
            let body = if &target.name == name {
                body
            } else {
                Box::new(inline_and_beta_reduce(*body, name, lambda))
            };
            TypedExprNode::For { target, iter, body }
        }

        // All remaining variants: pure structural recursion.  Atoms have
        // no children, so this is a no-op for them.  (`MutWrite` lands here:
        // its `name` references a value binding, never an inlinable lambda
        // `let`, so only its `value` child needs the walk.)
        node => {
            let mut expr = Expr {
                node_id,
                node,
                ty,
                user_annotation,
            };
            expr.map_children(|child| inline_and_beta_reduce(child, name, lambda));
            return expr;
        }
    };

    Expr {
        node_id,
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Run [`inline_and_beta_reduce`] on every refinement predicate embedded in
/// `ty`, rebuilding each predicate as a fresh immutable `Rc`. Every occurrence
/// that shared one predicate term in `ty` is re-pointed at the same rebuilt
/// term (the memo in [`walk_refined_predicates_mut`]), so the rewrite is
/// observed uniformly across them.
///
/// This stays a pass-level walk rather than a `Subst` call because inlining
/// inside a predicate must also *beta-reduce* the call sites it creates —
/// substitution proper is the engine's job and runs inside
/// [`inline_and_beta_reduce`] via `lambda_elim::substitute`.
fn inline_in_type_predicates(ty: &mut Type, name: &Name, lambda: &Expr) {
    walk_refined_predicates_mut(ty, &mut std::collections::HashMap::new(), &mut |pred, _| {
        let old = std::mem::replace(pred, Expr::lit(Lit::Unit));
        *pred = inline_and_beta_reduce(old, name, lambda);
    });
}

/// Returns `true` when `expr` has `Var(name)` in the function position of its
/// Apply chain — i.e. `Var(name)`, or `Apply(_, …Apply(_, Var(name))…)`.
/// Used by [`inline_and_beta_reduce`] to decide whether an enclosing `Apply`
/// should beta-reduce after the inner substitution collapses a Lambda.
fn is_name_in_function_position(expr: &Expr, name: &Name) -> bool {
    match &expr.node {
        TypedExprNode::Var(n) => n == name,
        TypedExprNode::Apply { function, .. } => is_name_in_function_position(function, name),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Provenance recording: drops and fan-out
// ---------------------------------------------------------------------------

/// Collect every main-tree [`NodeId`] reachable in `expr` (itself and all
/// descendants).
///
/// Mirrors `node_recorder`'s own collector: it walks `child_exprs` and so
/// **skips type-refinement predicates** — exactly the node set
/// [`NodeRecorder::reconcile`] reasons about, so drop/replicate accounting done
/// against this set lines up with reconciliation.
fn collect_ids(expr: &Expr, acc: &mut HashSet<NodeId>) {
    acc.insert(expr.node_id());
    expr.walk_children(|child| collect_ids(child, acc));
}

/// The ids an inlining rewrite *consumes*: the `Let` wrapper (`let_id`) plus
/// every id in the (already-inlined) `bound_expr` and `body` it is about to
/// rewrite away. Diffed against the produced result to find the dropped ids.
fn consumed_subtree_ids(let_id: NodeId, bound_expr: &Expr, body: &Expr) -> HashSet<NodeId> {
    let mut ids = HashSet::new();
    ids.insert(let_id);
    collect_ids(bound_expr, &mut ids);
    collect_ids(body, &mut ids);
    ids
}

/// Record as [`Discarded`](crate::ccl::node_recorder::NodeRecord::Discarded)
/// every consumed id absent from `result` — the nodes this rewrite removed with
/// no surviving counterpart (`Let` wrappers, beta redexes, lambda wrappers, and
/// the `Var` occurrences overwritten by substitution).
///
/// This diff *is* "discard exactly the ids that vanish": a consumed id survives
/// iff it (or its first fan-out copy) still appears in `result`. Every id in
/// `consumed` is a genuine pass input — inline mints no fresh id until the final
/// [`dedup_and_record`] sweep — so the `discarded` input-membership invariant
/// holds by construction.
fn record_drops(consumed: &HashSet<NodeId>, result: &Expr, rec: &mut NodeRecorder) {
    let mut surviving = HashSet::new();
    collect_ids(result, &mut surviving);
    for id in consumed {
        if !surviving.contains(id) {
            rec.discarded(*id);
        }
    }
}

/// Restore id uniqueness after fan-out, recording each duplicate as a
/// [`Replicated`](crate::ccl::node_recorder::NodeRecord::Replicated) copy.
///
/// Fan-out (an alias/UDF used N times) duplicates a subtree in place, so the
/// tree carries the same input id on N nodes. This single top-of-tree sweep
/// keeps the **first** occurrence of each id (an implicit Preserve — the input
/// id survives) and freshens every later occurrence, recording
/// `replicated(original, [fresh])` so the copy mirrors the node it came from.
/// It walks the main tree only (`walk_children_mut` skips predicates), matching
/// the node set reconciliation checks.
fn dedup_and_record(expr: &mut Expr, rec: &mut NodeRecorder) {
    let mut seen = HashSet::new();
    dedup_go(expr, &mut seen, rec);
}

fn dedup_go(expr: &mut Expr, seen: &mut HashSet<NodeId>, rec: &mut NodeRecorder) {
    if !seen.insert(expr.node_id()) {
        // Second or later occurrence of this id: this node is a fan-out copy.
        // Freshen it and record it as a replica of the input node it mirrors.
        let (original, fresh) = expr.freshen_node_id();
        rec.replicated(original, [fresh]);
        seen.insert(fresh);
    }
    expr.walk_children_mut(|child| dedup_go(child, seen, rec));
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BaseType, Lit, Type, TypedExpr, TypedExprNode};

    // -----------------------------------------------------------------------
    // is_iterable_domain predicate
    // -----------------------------------------------------------------------

    #[test]
    fn non_iterable_domain_base_int() {
        assert!(!is_iterable_domain(&Type::Base(BaseType::Int)));
    }

    #[test]
    fn non_iterable_domain_base_string() {
        assert!(!is_iterable_domain(&Type::Base(BaseType::String)));
    }

    #[test]
    fn iterable_domain_uint_range() {
        assert!(is_iterable_domain(&Type::UIntRange(3)));
    }

    #[test]
    fn iterable_domain_datasource() {
        assert!(is_iterable_domain(&Type::DataSource("s".to_string())));
    }

    #[test]
    fn non_iterable_domain_tuple_all_non_iterable() {
        let ty = Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Int)]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_tuple_mixed() {
        // Any non-iterable component makes the whole tuple non-iterable.
        let ty = Type::Tuple(vec![Type::UIntRange(3), Type::Base(BaseType::Int)]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn iterable_domain_tuple_all_iterable() {
        let ty = Type::Tuple(vec![Type::UIntRange(3), Type::UIntRange(3)]);
        assert!(is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_record_any_non_iterable() {
        let ty = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("n".to_string(), Type::UIntRange(3)),
        ]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn iterable_domain_record_all_iterable() {
        let ty = Type::Record(vec![
            ("a".to_string(), Type::UIntRange(2)),
            ("b".to_string(), Type::UIntRange(5)),
        ]);
        assert!(is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_record_all_non_iterable() {
        let ty = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("y".to_string(), Type::Base(BaseType::String)),
        ]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_refinement_wraps_non_iterable() {
        use crate::ccl::Refinement;
        use std::rc::Rc;
        let pred = Rc::new(TypedExpr::lit(Lit::Bool(true)));
        let refinement = Refinement { predicate: pred };
        let ty = Type::Refinement(Box::new(Type::Base(BaseType::Int)), refinement);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn iterable_domain_refinement_wraps_iterable() {
        use crate::ccl::Refinement;
        use std::rc::Rc;
        let pred = Rc::new(TypedExpr::lit(Lit::Bool(true)));
        let refinement = Refinement { predicate: pred };
        let ty = Type::Refinement(Box::new(Type::UIntRange(3)), refinement);
        assert!(is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_fun() {
        // There are infinitely many possible Int → Int functions, so Fun-as-domain
        // has no finite, enumerable extent.
        let ty = Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        assert!(!is_iterable_domain(&ty));
    }

    // -----------------------------------------------------------------------
    // should_inline predicate
    // -----------------------------------------------------------------------

    #[test]
    fn should_inline_scalar_to_scalar() {
        let ty = Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_curried_fun() {
        // Int → (Int → Int): domain is non-iterable (Int), so the curried
        // function is now inlined. Beta-reduction at concrete call sites
        // eliminates the nested lambda before any `curry` combinator is produced.
        let ty = Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Fun {
                name: None,
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Int)),
            }),
        };
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_refined_fun_codomain() {
        // Int → Refinement(Int → Int, pred): domain is non-iterable (Int),
        // so the function is inlined regardless of the refined codomain.
        use crate::ccl::Refinement;
        use std::rc::Rc;
        let pred = Rc::new(TypedExpr::lit(Lit::Bool(true)));
        let refinement = Refinement { predicate: pred };
        let inner_fun = Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        let ty = Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Refinement(Box::new(inner_fun), refinement)),
        };
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_not_inline_iterable_domain() {
        // UIntRange(3) → Int: iterable domain, don't inline.
        let ty = Type::Fun {
            name: None,
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        assert!(!should_inline(&ty));
    }

    #[test]
    fn should_inline_all_non_iterable_tuple_domain() {
        // (Int, Int) → Int: both components non-iterable, should inline.
        let ty = Type::Fun {
            name: None,
            domain: Box::new(Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::Int),
            ])),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_mixed_tuple_domain() {
        // (UIntRange(3), Int) → Int: any non-iterable component makes the tuple
        // non-iterable, so this is inlined.
        let ty = Type::Fun {
            name: None,
            domain: Box::new(Type::Tuple(vec![
                Type::UIntRange(3),
                Type::Base(BaseType::Int),
            ])),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_base_type_not_fun() {
        // Not a function type — should not inline.
        assert!(!should_inline(&Type::Base(BaseType::Int)));
    }

    #[test]
    fn should_inline_list_to_list_udf() {
        // Fun(Fun(UIntRange, Int), Fun(UIntRange, Int)): list-producing UDF, should inline.
        let int = Type::Base(BaseType::Int);
        let list = fn_ty(Type::UIntRange(3), int.clone());
        assert!(should_inline(&fn_ty(list.clone(), list)));
    }

    #[test]
    fn should_inline_tuple_arg_list_udf() {
        // Fun(Tuple(List, Int), List): uncurried multi-arg list UDF, should inline.
        let int = Type::Base(BaseType::Int);
        let list = fn_ty(Type::UIntRange(3), int.clone());
        let domain = Type::Tuple(vec![list.clone(), int]);
        assert!(should_inline(&fn_ty(domain, list)));
    }

    #[test]
    fn should_inline_list_to_scalar_udf() {
        // Fun(Fun(UIntRange, Int), Int): takes a list, returns a scalar (e.g. a
        // user-defined sum/fold). The domain is a Fun type — non-iterable —
        // so this is inlined just like any other non-iterable-domain function.
        let int = Type::Base(BaseType::Int);
        let list = fn_ty(Type::UIntRange(3), int.clone());
        assert!(should_inline(&fn_ty(list, int)));
    }

    // -----------------------------------------------------------------------
    // run pass structural transforms
    // -----------------------------------------------------------------------

    /// Build a scalar `Let` binding: `let x: Int = 2 in BinOp(Var(x), Add, Lit(1))`.
    fn scalar_let() -> Expr {
        let int = Type::Base(BaseType::Int);
        let bound = TypedExpr::lit(Lit::Int(2)).with_ty(int.clone());
        let body = TypedExpr::new(TypedExprNode::BinOp {
            left: Box::new(TypedExpr::var("x").with_ty(int.clone())),
            op: crate::ccl::BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
            right: Box::new(TypedExpr::lit(Lit::Int(1)).with_ty(int.clone())),
        })
        .with_ty(int.clone());
        TypedExpr::let_bind("x", bound, body)
    }

    #[test]
    fn scalar_let_unchanged() {
        let expr = scalar_let();
        let result = inline_non_iterable_lambdas(expr.clone());
        assert_eq!(result, expr);
    }

    #[test]
    fn collection_let_alias_is_inlined() {
        // let f: UIntRange(3) → Int = id in f
        // Even though the domain is iterable (so should_inline returns false), the bound
        // expression is a plain Var — alias inlining eliminates the let unconditionally.
        let domain = Type::UIntRange(3);
        let codomain = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(domain.clone(), codomain.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty.clone());
        let body = TypedExpr::var("f").with_ty(fun_ty.clone());
        let expr = TypedExpr::let_bind("f", id_expr.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        // Alias `f → id` is substituted; result is just `id`.
        assert_eq!(result, id_expr);
    }

    #[test]
    fn curried_let_is_inlined() {
        // let f: Int → (Int → Int) = curry_add in f
        // Domain is Int (non-iterable), so the curried Let IS inlined.
        // After inline_non_iterable_lambdas: the Let is dropped and the result is Var("curry_add").
        let int = Type::Base(BaseType::Int);
        let curried_ty = Type::fun(int.clone(), Type::fun(int.clone(), int.clone()));
        let curry_expr = TypedExpr::var("curry_add").with_ty(curried_ty.clone());
        let body = TypedExpr::var("f").with_ty(curried_ty.clone());
        let expr = TypedExpr::let_bind("f", curry_expr.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        assert_eq!(result, curry_expr);
    }

    #[test]
    fn scalar_function_let_is_inlined() {
        // let f: Int → Int = id in Apply(Lit(3), Var(f))
        // After inlining: Apply(Lit(3), id)
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty.clone());
        let apply = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", id_expr.clone(), apply);

        let result = inline_non_iterable_lambdas(expr);

        // The Let wrapper should be gone; Var(f) replaced by id_expr.
        // Note: id_expr is Var("id"), not a Lambda, so Apply(Lit(3), id_expr)
        // is not beta-reduced (no Lambda to reduce into).
        let expected = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(id_expr),
        })
        .with_ty(int.clone());
        assert_eq!(result, expected);
    }

    #[test]
    fn multi_use_inlining_substitutes_all_occurrences() {
        // let f: Int → Int = id in Tuple([Apply(3, f), Apply(4, f)])
        // After inlining: Tuple([Apply(3, id), Apply(4, id)])
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty.clone());

        let call3 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let call4 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(4)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let body = TypedExpr::tuple(vec![call3, call4])
            .with_ty(Type::Tuple(vec![int.clone(), int.clone()]));
        let expr = TypedExpr::let_bind("f", id_expr.clone(), body);

        let result = inline_non_iterable_lambdas(expr);

        let expected_call3 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(id_expr.clone()),
        })
        .with_ty(int.clone());
        let expected_call4 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(4)).with_ty(int.clone())),
            function: Box::new(id_expr),
        })
        .with_ty(int.clone());
        let expected = TypedExpr::tuple(vec![expected_call3, expected_call4])
            .with_ty(Type::Tuple(vec![int.clone(), int.clone()]));
        assert_eq!(result, expected);
    }

    #[test]
    fn unused_function_let_is_dropped() {
        // let f: Int → Int = id in Lit(42)
        // After inlining (f is never used): Lit(42)
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty);
        let body = TypedExpr::lit(Lit::Int(42)).with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", id_expr, body);

        let result = inline_non_iterable_lambdas(expr);
        let expected = TypedExpr::lit(Lit::Int(42)).with_ty(int);
        assert_eq!(result, expected);
    }

    #[test]
    fn nested_inlining_both_lets_inlined() {
        // let f: Int → Int = id in let g: Int → Int = id in Apply(Apply(3, g), f)
        // After inlining both: Apply(Apply(3, id), id)
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_f = TypedExpr::var("id").with_ty(fun_ty.clone());
        let id_g = TypedExpr::var("id").with_ty(fun_ty.clone());

        let inner_apply = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("g").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let outer_apply = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(inner_apply),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());

        let inner_let = TypedExpr::let_bind("g", id_g.clone(), outer_apply);
        let expr = TypedExpr::let_bind("f", id_f.clone(), inner_let);

        let result = inline_non_iterable_lambdas(expr);

        // Both f and g should be substituted with id.
        let expected_inner = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(id_g),
        })
        .with_ty(int.clone());
        let expected = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(expected_inner),
            function: Box::new(id_f),
        })
        .with_ty(int.clone());
        assert_eq!(result, expected);
    }

    // -----------------------------------------------------------------------
    // Helper used in the remaining tests
    // -----------------------------------------------------------------------

    /// `Fun(domain, codomain)` shorthand for the tests below.
    fn fn_ty(domain: Type, codomain: Type) -> Type {
        Type::Fun {
            name: None,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    // is_name_in_function_position — call-site detector
    // -----------------------------------------------------------------------

    #[test]
    fn name_in_function_position_bare_var() {
        let expr = TypedExpr::var("f");
        assert!(is_name_in_function_position(&expr, &Name::raw("f")));
        assert!(!is_name_in_function_position(&expr, &Name::raw("g")));
    }

    #[test]
    fn name_in_function_position_apply_chain() {
        // `Apply(arg2, Apply(arg1, Var("f")))` — curried call of `f`.
        let int = Type::Base(BaseType::Int);
        let inner = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
            TypedExpr::var("f"),
        );
        let outer = TypedExpr::apply(TypedExpr::lit(Lit::Int(2)).with_ty(int), inner);
        assert!(is_name_in_function_position(&outer, &Name::raw("f")));
        assert!(!is_name_in_function_position(&outer, &Name::raw("g")));
    }

    #[test]
    fn name_in_function_position_in_argument_only() {
        // `Apply(Var("f"), Var("g"))` — `f` sits in the *argument* slot, not
        // function. Should not count as `f` in function position.
        let expr = TypedExpr::apply(TypedExpr::var("f"), TypedExpr::var("g"));
        assert!(is_name_in_function_position(&expr, &Name::raw("g")));
        assert!(!is_name_in_function_position(&expr, &Name::raw("f")));
    }

    #[test]
    fn name_in_function_position_non_apply_non_var() {
        // Lambda/Lit/etc. never put Var(name) in function position by themselves.
        assert!(!is_name_in_function_position(
            &TypedExpr::lit(Lit::Int(1)),
            &Name::raw("f")
        ));
    }

    // inline_and_beta_reduce — targeted behaviour
    // -----------------------------------------------------------------------

    #[test]
    fn inline_and_beta_reduce_bare_var_replaced_with_lambda() {
        // `Var("f")` in a non-call position is substituted literally (the
        // Lambda value), no beta reduction.
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let body = TypedExpr::var("f").with_ty(fn_ty(int.clone(), int));
        let result = inline_and_beta_reduce(body, &Name::raw("f"), &lambda);
        assert_eq!(result, lambda);
    }

    #[test]
    fn inline_and_beta_reduce_single_arg_call() {
        // `Apply(lit(3), Var("f"))` with `f = λ x → x` beta-reduces to `3`.
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let arg = TypedExpr::lit(Lit::Int(3)).with_ty(int.clone());
        let call = TypedExpr::apply(arg.clone(), TypedExpr::var("f").with_ty(lambda.ty.clone()))
            .with_ty(int);
        let result = inline_and_beta_reduce(call, &Name::raw("f"), &lambda);
        assert_eq!(result, arg);
    }

    #[test]
    fn inline_and_beta_reduce_curried_call() {
        // `Apply(lit(2), Apply(lit(1), Var("f")))` with `f = λ a → λ b → a`
        // reduces to `1` (first argument wins). Mirrors the multi-arg
        // curried UDF call site.
        let int = Type::Base(BaseType::Int);
        let inner = TypedExpr::lambda("b", int.clone(), TypedExpr::var("a").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let lambda = TypedExpr::lambda("a", int.clone(), inner)
            .with_ty(fn_ty(int.clone(), fn_ty(int.clone(), int.clone())));
        let call = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(2)).with_ty(int.clone()),
            TypedExpr::apply(
                TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
                TypedExpr::var("f").with_ty(lambda.ty.clone()),
            )
            .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let result = inline_and_beta_reduce(call, &Name::raw("f"), &lambda);
        assert_eq!(result, TypedExpr::lit(Lit::Int(1)).with_ty(int));
    }

    #[test]
    fn inline_and_beta_reduce_shadowing_guard() {
        // `Lambda("f", Var("f"))` — the inner `f` is shadowed by the lambda
        // param, so substitution must not replace it. The input binding of
        // `f` to the lambda we pass in is irrelevant here.
        let int = Type::Base(BaseType::Int);
        let shadowed =
            TypedExpr::lambda("f", int.clone(), TypedExpr::var("f").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone()));
        // Some arbitrary lambda we'd otherwise inline if `f` weren't shadowed.
        let replacement = TypedExpr::lambda(
            "x",
            int.clone(),
            TypedExpr::lit(Lit::Int(42)).with_ty(int.clone()),
        )
        .with_ty(fn_ty(int.clone(), int));
        let result = inline_and_beta_reduce(shadowed.clone(), &Name::raw("f"), &replacement);
        assert_eq!(result, shadowed);
    }

    // inline_non_iterable_lambdas — end-to-end pass behaviour
    // -----------------------------------------------------------------------

    #[test]
    fn inline_non_iterable_lambdas_inlines_scalar_let() {
        // Scalar UDF: `let f: Int → Int = id in Var("f")`.
        // After inline_non_iterable_lambdas: the Let is dropped and the result is Var("id").
        let int = Type::Base(BaseType::Int);
        let ident = TypedExpr::var("id").with_ty(fn_ty(int.clone(), int.clone()));
        let body = TypedExpr::var("f").with_ty(fn_ty(int.clone(), int.clone()));
        let expr = TypedExpr::let_bind("f", ident.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        assert_eq!(result, ident);
    }

    #[test]
    fn inline_non_iterable_lambdas_inlines_user_curried_let() {
        // `let f: Int → (Int → Int) = g in f` — user-curried scalar.
        // Domain is Int (non-iterable), so `should_inline` returns true and
        // the Let IS inlined. After inline_non_iterable_lambdas: the result is Var("g").
        let int = Type::Base(BaseType::Int);
        let curried = fn_ty(int.clone(), fn_ty(int.clone(), int.clone()));
        let ident = TypedExpr::var("g").with_ty(curried.clone());
        let body = TypedExpr::var("f").with_ty(curried);
        let expr = TypedExpr::let_bind("f", ident.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        assert_eq!(result, ident);
    }

    #[test]
    fn inline_non_iterable_lambdas_inlines_and_beta_reduces_list_udf() {
        // Mirror the simplest generator-function lowering:
        //   let doubles = λ xs → λ __iter_record → __iter_record ▷ xs ▷ (λ x → x)
        //   in [1, 2, 3] ▷ doubles
        // After inline_non_iterable_lambdas: the outer `λ xs` is substituted and beta-reduced,
        // leaving `λ __iter_record → __iter_record ▷ [1, 2, 3] ▷ (λ x → x)`.
        let int = Type::Base(BaseType::Int);
        let range = Type::UIntRange(3);
        let list = fn_ty(range.clone(), int.clone());
        let udf_ty = fn_ty(list.clone(), list.clone());

        let inner_lambda_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                TypedExpr::var("xs").with_ty(list.clone()),
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let inner_lambda =
            TypedExpr::lambda("__iter_record", range.clone(), inner_lambda_body.clone())
                .with_ty(list.clone());
        let outer_lambda =
            TypedExpr::lambda("xs", list.clone(), inner_lambda).with_ty(udf_ty.clone());

        let list_literal = TypedExpr::new(TypedExprNode::List(vec![
            TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(2)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
        ]))
        .with_ty(list.clone());
        let call = TypedExpr::apply(
            list_literal.clone(),
            TypedExpr::var("doubles").with_ty(udf_ty.clone()),
        )
        .with_ty(list.clone());
        let expr = TypedExpr::let_bind("doubles", outer_lambda, call);

        let result = inline_non_iterable_lambdas(expr);

        // Expected: the top-level node is the inner Lambda (no more Let, no
        // more outer `λ xs`), with `xs` substituted by the concrete list.
        let expected_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                list_literal,
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int);
        let expected = TypedExpr::lambda("__iter_record", range, expected_body).with_ty(list);
        assert_eq!(result, expected);
    }

    #[test]
    fn inline_non_iterable_lambdas_substitutes_arg_pair_into_multi_arg_body() {
        // Mirror the uncurried multi-arg shape:
        //   let f = λ __arg_pair → λ __iter_record → … __arg_pair.0 …
        //   in ([1, 2, 3], 10) ▷ f
        // After inline_non_iterable_lambdas: the outer `λ __arg_pair` is
        // beta-reduced, leaving `Tuple([1,2,3], 10).0` in the body. The
        // literal-tuple-projection fold lives in `crate::ccl::simplify` and
        // is *not* applied here — this test asserts only the substitution +
        // outer-lambda beta-reduction behaviour.
        let int = Type::Base(BaseType::Int);
        let range = Type::UIntRange(3);
        let list = fn_ty(range.clone(), int.clone());
        let arg_pair_ty = Type::Tuple(vec![list.clone(), int.clone()]);
        let udf_ty = fn_ty(arg_pair_ty.clone(), list.clone());

        // body: λ __iter_record → __iter_record ▷ __arg_pair.0 ▷ (λ x → x)
        let proj0 = TypedExpr::new(TypedExprNode::Proj(crate::ccl::ProjKey::Index(0)))
            .with_ty(fn_ty(arg_pair_ty.clone(), list.clone()));
        let pair_proj = TypedExpr::apply(
            TypedExpr::var("__arg_pair").with_ty(arg_pair_ty.clone()),
            proj0.clone(),
        )
        .with_ty(list.clone());
        let inner_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                pair_proj,
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let inner_lambda =
            TypedExpr::lambda("__iter_record", range.clone(), inner_body).with_ty(list.clone());
        let outer_lambda = TypedExpr::lambda("__arg_pair", arg_pair_ty.clone(), inner_lambda)
            .with_ty(udf_ty.clone());

        let list_literal = TypedExpr::new(TypedExprNode::List(vec![
            TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(2)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
        ]))
        .with_ty(list.clone());
        let arg = TypedExpr::tuple(vec![
            list_literal.clone(),
            TypedExpr::lit(Lit::Int(10)).with_ty(int.clone()),
        ])
        .with_ty(arg_pair_ty.clone());
        let call = TypedExpr::apply(arg.clone(), TypedExpr::var("f").with_ty(udf_ty))
            .with_ty(list.clone());
        let expr = TypedExpr::let_bind("f", outer_lambda, call);

        let result = inline_non_iterable_lambdas(expr);

        // Expected: outer Let / outer `λ __arg_pair` are gone; references to
        // `__arg_pair` are rewritten to the concrete tuple literal, so the
        // `Tuple([list, 10]).0` shape now sits inside the body verbatim.
        let folded_pair_proj = TypedExpr::apply(arg, proj0).with_ty(list.clone());
        let expected_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                folded_pair_proj,
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int);
        let expected = TypedExpr::lambda("__iter_record", range, expected_body).with_ty(list);
        assert_eq!(result, expected);
    }

    #[test]
    fn inline_non_iterable_lambdas_beta_reduces_scalar_lambda_call() {
        // let f: Int → Int = λ x → Lit(42) in Apply(Lit(3), Var("f"))
        // After inline_non_iterable_lambdas: Lit(42) (the constant lambda is beta-reduced,
        // discarding the argument Lit(3)).
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda(
            "x",
            int.clone(),
            TypedExpr::lit(Lit::Int(42)).with_ty(int.clone()),
        )
        .with_ty(fn_ty(int.clone(), int.clone()));
        let call = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
            TypedExpr::var("f").with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", lambda, call);

        let result = inline_non_iterable_lambdas(expr);
        let expected = TypedExpr::lit(Lit::Int(42)).with_ty(int);
        assert_eq!(result, expected);
    }

    #[test]
    fn inline_non_iterable_lambdas_substitutes_pair_into_multi_arg_scalar_body() {
        // let add: Tuple(Int, Int) → Int = λ __pair → __pair.0 + __pair.1
        // in add(Tuple(Lit(1), Lit(2)))
        //
        // After inline_non_iterable_lambdas: the body becomes
        //   Tuple(1, 2).0 + Tuple(1, 2).1
        // — the literal-tuple projections survive here and are folded later
        // by `crate::ccl::simplify::try_literal_tuple_projection`.
        use crate::ccl::{ArithmeticKind, BinOpKind};
        let int = Type::Base(BaseType::Int);
        let pair_ty = Type::Tuple(vec![int.clone(), int.clone()]);
        let udf_ty = fn_ty(pair_ty.clone(), int.clone());

        // __pair.0: Apply(argument: Var("__pair"), function: Proj(0))
        let proj0 = TypedExpr::new(TypedExprNode::Proj(crate::ccl::ProjKey::Index(0)))
            .with_ty(fn_ty(pair_ty.clone(), int.clone()));
        let pair_proj0 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::var("__pair").with_ty(pair_ty.clone())),
            function: Box::new(proj0.clone()),
        })
        .with_ty(int.clone());

        // __pair.1: Apply(argument: Var("__pair"), function: Proj(1))
        let proj1 = TypedExpr::new(TypedExprNode::Proj(crate::ccl::ProjKey::Index(1)))
            .with_ty(fn_ty(pair_ty.clone(), int.clone()));
        let pair_proj1 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::var("__pair").with_ty(pair_ty.clone())),
            function: Box::new(proj1.clone()),
        })
        .with_ty(int.clone());

        // body: __pair.0 + __pair.1
        let body = TypedExpr::new(TypedExprNode::BinOp {
            left: Box::new(pair_proj0),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(pair_proj1),
        })
        .with_ty(int.clone());

        // λ __pair → body
        let lambda = TypedExpr::lambda("__pair", pair_ty.clone(), body).with_ty(udf_ty.clone());

        // arg: Tuple(Lit(1), Lit(2))
        let lit1 = TypedExpr::lit(Lit::Int(1)).with_ty(int.clone());
        let lit2 = TypedExpr::lit(Lit::Int(2)).with_ty(int.clone());
        let arg = TypedExpr::tuple(vec![lit1.clone(), lit2.clone()]).with_ty(pair_ty.clone());

        // call: Apply(argument: arg, function: Var("add"))
        let call = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(arg.clone()),
            function: Box::new(TypedExpr::var("add").with_ty(udf_ty)),
        })
        .with_ty(int.clone());

        let expr = TypedExpr::let_bind("add", lambda, call);
        let result = inline_non_iterable_lambdas(expr);

        // Expected: Tuple(1,2).0 + Tuple(1,2).1 — projections unfolded here.
        let expected_left = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(arg.clone()),
            function: Box::new(proj0),
        })
        .with_ty(int.clone());
        let expected_right = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(arg),
            function: Box::new(proj1),
        })
        .with_ty(int.clone());
        let expected = TypedExpr::new(TypedExprNode::BinOp {
            left: Box::new(expected_left),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(expected_right),
        })
        .with_ty(int);
        assert_eq!(result, expected);
    }

    // -----------------------------------------------------------------------
    // NodeRecorder adoption: reconcile must be clean for every rewrite shape.
    //
    // A clean `reconcile` is the definition of done for the record set: every
    // output id is explained (preserve-by-presence or a `Replicated` copy) and
    // every dropped input is declared `Discarded`. Inline emits no `Minted`
    // and no `Fused`.
    // -----------------------------------------------------------------------

    /// Collect every main-tree id in `expr` (the node set reconcile reasons
    /// about).
    fn ids(expr: &Expr) -> HashSet<NodeId> {
        let mut acc = HashSet::new();
        collect_ids(expr, &mut acc);
        acc
    }

    #[test]
    fn records_udf_used_once_is_pure_preserve_and_discards() {
        // let f: Int → Int = λ x → x in Apply(3, f)  — a single use.
        // Beta-reduces to `3`; the `Let`, the `Apply` redex, the lambda
        // wrapper, its body `Var x` and the `Var f` occurrence all vanish, and
        // no subtree is duplicated.
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let call = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
            TypedExpr::var("f").with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", lambda, call);

        let (output, rec) = inline_with_records(expr);
        assert_eq!(rec.reconcile(&output), Ok(()));
        // A single use fans nothing out: no Replicated (or any) stage edge.
        assert!(
            rec.stage_remap().is_empty(),
            "single-use inline must record no replicate edges, got {:?}",
            rec.stage_remap()
        );
    }

    #[test]
    fn records_udf_used_twice_fans_out_and_reconciles() {
        // let f: Int → Int = λ x → x in Tuple[f, f]  — two *bare* uses, so each
        // occurrence gets a full copy of the lambda that survives into the
        // output (unlike a call site, which the beta-reduction consumes).
        let int = Type::Base(BaseType::Int);
        let fun = fn_ty(int.clone(), int.clone());
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fun.clone());
        let body = TypedExpr::tuple(vec![
            TypedExpr::var("f").with_ty(fun.clone()),
            TypedExpr::var("f").with_ty(fun.clone()),
        ])
        .with_ty(Type::Tuple(vec![fun.clone(), fun.clone()]));
        // Capture the lambda's input ids: one of them must survive as the
        // preserved "origin" of the fan-out.
        let lambda_ids = ids(&lambda);
        let expr = TypedExpr::let_bind("f", lambda, body);

        let (output, rec) = inline_with_records(expr);
        assert_eq!(rec.reconcile(&output), Ok(()));

        // Fan-out: at least one `(copy, origin)` edge, every origin an input
        // lambda id, and every origin still present in the output (preserve-one).
        let remap = rec.stage_remap();
        assert!(
            !remap.is_empty(),
            "a >=2-use inline must record replicate edges"
        );
        let out_ids = ids(&output);
        for (copy, origin) in &remap {
            assert!(
                lambda_ids.contains(origin),
                "replicate origin {origin:?} must be an input lambda id"
            );
            assert!(
                out_ids.contains(origin),
                "the origin id {origin:?} must survive (preserve-one)"
            );
            assert!(
                out_ids.contains(copy),
                "the freshened copy {copy:?} must be present in the output"
            );
        }
    }

    #[test]
    fn records_alias_reconciles() {
        // let f = id in f  — pure alias α-rename; the `Let` and the `Var f`
        // occurrence vanish, `id` survives.
        let fun = fn_ty(Type::UIntRange(3), Type::Base(BaseType::Int));
        let id_expr = TypedExpr::var("id").with_ty(fun.clone());
        let body = TypedExpr::var("f").with_ty(fun);
        let expr = TypedExpr::let_bind("f", id_expr, body);

        let (output, rec) = inline_with_records(expr);
        assert_eq!(rec.reconcile(&output), Ok(()));
    }

    #[test]
    fn records_unused_let_discards_everything() {
        // let f: Int → Int = id in Lit(42)  — f never used, so the whole
        // binding (the `Let` and the bound `Var id`) is discarded; only Lit(42)
        // survives.
        let int = Type::Base(BaseType::Int);
        let id_expr = TypedExpr::var("id").with_ty(fn_ty(int.clone(), int.clone()));
        let body = TypedExpr::lit(Lit::Int(42)).with_ty(int);
        let expr = TypedExpr::let_bind("f", id_expr, body);

        let (output, rec) = inline_with_records(expr);
        assert_eq!(rec.reconcile(&output), Ok(()));
        // Nothing fans out or is minted.
        assert!(rec.stage_remap().is_empty());
    }

    #[test]
    fn preserves_ids_on_untouched_program() {
        // A program with nothing to inline (scalar `let x = 2 in x + 1`) is
        // reproduced verbatim, ids and all — id preservation is behaviour-neutral.
        let expr = scalar_let();
        let input_ids = ids(&expr);

        let (output, rec) = inline_with_records(expr);
        assert_eq!(rec.reconcile(&output), Ok(()));
        // Every input id survives with its identity intact (no fresh mints, no
        // drops): the id set is preserved exactly.
        assert_eq!(ids(&output), input_ids);
    }
}

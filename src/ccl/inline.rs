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
//!   (`\x, y -> …`) are uncurried at lowering to `Tuple([…]) → T`, so they
//!   match this rule too.
//!
//! - **List-producing UDFs**: `Fun(Fun(iterable_domain, _), _)`.  Functions
//!   whose domain is itself a function type — generator functions and
//!   list-returning `def`s lowered to `λ user_arg → λ __iter_record → body`.
//!   A `Fun` domain has no iterable domain, so these are covered by the same
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
//! This pass runs **before** [`crate::ccl::channelize`] (so the unified
//! letrec phase can route an in-loop feed against inlined writers, and a
//! defer-mediating UDF reaches its call site before desugar routes it), so it
//! *does* see [`Defer`]/[`Feed`]/[`Define`] nodes and `Type::History` (feed) domains.
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
    Expr, Lit, Name, Refinement, Type, TypedExprNode,
    ccl_utils::{PredMemo, is_free, walk_refined_predicates_mut},
    lambda_elim::substitute,
    lineage::{self, LineageLog, Nature, RecorderSession, RewriteLabel},
    provenance::NodeId,
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
    let mut expr = inline_impl(expr);
    // Beta-reduction rebuilds predicates on `expr.ty` (immutable terms); keep
    // each `Cast`'s `target` slot in step so the post-pass typecheck matches.
    crate::ccl::ccl_utils::sync_cast_targets(&mut expr);
    expr
}

/// Inline as [`inline_non_iterable_lambdas`], but also drain the [`LineageLog`]
/// of the [`RewriteStep`](crate::ccl::lineage::RewriteStep)s this pass opens at
/// its rewrite sites — the redesign's recording layer, and the only provenance
/// surface inline exposes.
///
/// Inline is **id-preserving**: a rebuilt node carries its input [`NodeId`], so
/// most of the tree is an implicit preserve (a self-edge at collapse, nothing
/// recorded). The recorded rewrites are:
///
/// * a `Transform` discard per beta/alias site (the dropped scaffolding — the
///   `Let` wrapper, beta redex, lambda wrapper, and the `Var` occurrences
///   substitution overwrote; see [`record_drops`]), and
/// * one `Copy` per freshened fan-out duplicate, captured from the `on_copy`
///   hook while the substitution runs under the beta site's open step.
///
/// Inline neither invents source-blamed nodes nor fuses clusters (tuple-
/// projection folding lives in `crate::ccl::simplify`).
pub(crate) fn inline_with_lineage(expr: Expr) -> (Expr, LineageLog) {
    let session = RecorderSession::new();
    let expr = inline_non_iterable_lambdas(expr);
    (expr, session.into_log())
}

// ---------------------------------------------------------------------------
// Domain predicates
// ---------------------------------------------------------------------------

/// Returns `true` when `ty` has a finite, enumerable domain — i.e., when the
/// operator graph can natively schedule a function over this domain as
/// `IterateExtent` without inlining.
///
/// | Type | Iterable? | Reason |
/// |------|-----------|--------|
/// | `Base(_)` | no | No finite enumeration of all integers / strings / bools |
/// | `Tuple(ts)` | yes only if ALL `t` are iterable | A tuple can only be iterated if every component can |
/// | `Record(fields)` | yes only if ALL fields are iterable | Same logic as tuples: a record with an unbounded field has no finite domain |
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
        // Records are structurally equivalent to tuples for domain purposes.
        Type::Record(fields) => fields.iter().all(|(_, t)| is_iterable_domain(t)),
        // Refinement inherits the iterability of its base type.
        Type::Refinement(inner, _) => is_iterable_domain(inner),
        // Natively iterable types.
        Type::UIntRange(_) | Type::DataSource(_) => true,
        // There are infinitely many possible functions for any given function
        // type, so function-typed domains cannot be enumerated.
        Type::Fun { .. } => false,
        // A history-typed domain has no enumerable domain — treat it
        // non-iterable like a function so a history-param UDF is inlined; the
        // `_ => true` fallthrough would otherwise strand it. Two cases reach
        // here, both pre-erasure (inlining runs before `channelize` and the
        // unified phase): a `Feed` defer-handle domain (a defer-mediating UDF
        // `λ out → out << e` has domain `feed(ρ)`; its call sites beta-reduce,
        // renaming the fed-to handle — see `Subst::handle_target`), and a
        // `Overwrite` pass-by-ref param domain.
        Type::History { .. } => false,
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
        Type::Fun { domain, .. } => !is_iterable_domain(domain),
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

/// Returns `true` if `name` is written by a mutable-variable mutation (`MutWrite`) anywhere
/// inside `expr`. A mutable write advances the variable's history, so an alias
/// `let y = x` may not be substituted past one (the read would move to the wrong
/// position) — the mutation-era complement to [`is_let_bound`]'s lexical-rebind
/// check. Conservative: any write to `x` in the body blocks the substitution,
/// even if every use of the alias precedes it.
fn is_mut_written(name: &Name, expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::MutWrite { name: target, .. } if target == name => true,
        _ => expr.any_child(|e| is_mut_written(name, e)),
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
/// This pass runs **before** [`crate::ccl::channelize`] (see the module
/// docs), so it *does* encounter `Defer`/`Feed`/`Define` nodes; beta-reduction
/// routes them through the defer-aware [`crate::ccl::subst::Subst`] engine,
/// which renames a fed-to handle when a defer-mediating UDF is inlined. The
/// defer-returning lift itself lives in `channelize::try_lift_defer`.
fn inline_impl(expr: Expr) -> Expr {
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
            let bound_expr = inline_impl(*bound_expr);
            let body = inline_impl(*body);

            // Alias: `let y = x` is pure α-renaming — substitute y → x in body
            // and drop the Let.  This must run before lambda_elim so that the
            // let-in-lambda rule never wraps such aliases in `const(x)`.
            //
            // Guard: only safe when `x` is not *re-defined* inside body. Two
            // ways it can be: a lexical rebind (`let x = …` / `λ x → …`), which
            // would capture the substituted references under the shadow; or a
            // mutable write (`x += …`, a `MutWrite`), which advances `x`'s history
            // so a read at the binding site and a read after the write are
            // different values. Substituting past a write moves the read to the
            // wrong position — e.g. `x := 1; y: int = x; x += 4; y` must be `1`
            // (the value when `y` is bound), not `5` (the post-write value). A
            // mutable write is a `MutWrite`, not a `let`, so `is_let_bound` alone
            // misses it (writes stopped being `let` shadows in mutability v2).
            if let TypedExprNode::Var(repl_name) = &bound_expr.node
                && !is_let_bound(repl_name, &body)
                && !is_mut_written(repl_name, &body)
            {
                // The `Let` wrapper and every `Var(binding.name)` occurrence
                // vanish (each occurrence is overwritten by a copy of the
                // `Var(x)` bound expr, whose own id survives via those copies —
                // or is dropped when the alias is unused).
                let consumed = consumed_subtree_ids(node_id, &bound_expr, &body);
                let result = substitute(body, &binding.name, &bound_expr);
                record_drops(&consumed, &result, "inline.alias");
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
                let reduced = {
                    // Open the beta site's fan-out step over the substitution +
                    // lambda clones: each freshened duplicate is captured as a
                    // per-origin `Copy` via the `on_copy` hook. Consuming nothing
                    // and minting nothing of its own, this frame flushes only the
                    // captured copies (no `Transform`).
                    let _g =
                        lineage::step("inline.beta", Vec::new(), Vec::new(), Nature::Expansion);
                    // One memo for the whole `[name ↦ lambda]` rewrite, so a
                    // predicate rebuilt at one node is re-pointed at (not
                    // re-derived for) its occurrences on every other node this
                    // sweep touches. Scoped to *this* rewrite, not the `inline`
                    // pass: a different binder's rewrite maps the same origin
                    // `Rc` to a different result.
                    inline_and_beta_reduce(body, &binding.name, &bound_expr, &PredMemo::new())
                };
                record_drops(&consumed, &reduced, "inline.beta");
                // Re-run inline_impl after beta-reduction so that newly created
                // Let bindings (e.g. `let y = (let x = Defer in …) in …` after
                // expanding a defer-returning UDF) are eligible for the alias
                // and lift rewrites on the second pass; that recursion records
                // its own drops at the nested sites.
                return inline_impl(reduced);
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
        // `channelize`. Re-running `inline_impl` on the wrapping `Let`
        // triggers `try_lift_defer` on the new binding.
        TypedExprNode::Compose(terms) => {
            TypedExprNode::Compose(terms.into_iter().map(inline_impl).collect())
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
            expr.map_children(inline_impl);
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
fn inline_and_beta_reduce(expr: Expr, name: &Name, lambda: &Expr, memo: &PredMemo) -> Expr {
    // Direct occurrence: replace the variable with the Lambda value — a UDF used
    // as an unapplied value, or the function side of a call about to
    // beta-reduce. Freshen the clone unconditionally at this duplication site so
    // N occurrences never share the source lambda's NodeIds; each freshened node
    // fires `on_copy` into the open beta step (the fan-out `Copy` lineage).
    if let TypedExprNode::Var(ref n) = expr.node
        && n == name
    {
        let mut cloned = lambda.clone();
        cloned.freshen_node_ids_deep();
        return cloned;
    }

    // Substitute inside refinement predicates riding **every** type slot this
    // node carries — its `ty`, its annotation, a `Cast`'s `target`, and each
    // binder's declared type. A predicate is an expression tree the
    // children-walk below never reaches (e.g. a list-comprehension filter
    // `f(x)` lives only in the cast-target refinement, which is also where
    // `lambda_elim` and operator conversion read it from), so a UDF use inside
    // one would survive as a dangling `Var` once the enclosing `Let` is
    // dropped — and enumerating the slots by hand here is how one gets missed.
    // A binder's own type is in the enclosing scope (a binder does not bind in
    // its own type), so the shadowing checks further down do not apply to it.
    let mut expr = expr;
    expr.walk_type_slots_mut(|ty| inline_in_type_predicates(ty, name, lambda, memo));

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
        let argument = inline_and_beta_reduce(*argument, name, lambda, memo);
        let function = inline_and_beta_reduce(*function, name, lambda, memo);
        match function.node {
            TypedExprNode::Lambda { param, body } => {
                // A domain refinement on this outer lambda encodes a precondition
                // `P(arg)` that beta reduction must not lose. Such refinements ride
                // the param's *type* (a `Type::Refinement` introduced by `cast`, or
                // the singleton a literal carries), copied into `param.ty` by
                // coalesce's `refresh_lambda_param_slot`.
                //
                // Substitution **discharges** the precondition when the argument's
                // own type already entails it: `P` then holds of the term replacing
                // the binder, so dropping it from a type that no longer has a binder
                // to describe loses nothing. That is the ordinary case for a literal
                // argument — `{Int | __elem == 5}` is entailed by `5`'s own type,
                // trivially.
                //
                // What is *not* safe is a precondition the argument does not
                // establish; that needs a principled lift (a `restrict(pred)` guard
                // around the substituted body) rather than a silent drop. A hard
                // assert, not `debug_assert`: this reads a live post-inference data
                // path, and a release build proceeding past it would miscompile to
                // wrong results rather than fail.
                assert!(
                    refinement_discharged_by(&argument.ty, &param.ty),
                    "inline_and_beta_reduce: outer lambda for `{name}` has parameter \
                     type {} which the argument type {} does not entail; beta reduction \
                     would silently drop the precondition. This needs a `restrict` lift, \
                     not a substitution.",
                    param.ty,
                    argument.ty
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
                    body: Box::new(inline_and_beta_reduce(*body, name, lambda, memo)),
                }
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_bound = inline_and_beta_reduce(*bound_expr, name, lambda, memo);
            let new_body = if &binding.name == name {
                *body
            } else {
                inline_and_beta_reduce(*body, name, lambda, memo)
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
                        .map(|(b, def)| (b, inline_and_beta_reduce(def, name, lambda, memo)))
                        .collect(),
                    body: Box::new(inline_and_beta_reduce(*body, name, lambda, memo)),
                }
            }
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),

        // The loop target shadows `name` inside the body only; the source
        // still substitutes.
        TypedExprNode::For { target, iter, body } => {
            let iter = Box::new(inline_and_beta_reduce(*iter, name, lambda, memo));
            let body = if &target.name == name {
                body
            } else {
                Box::new(inline_and_beta_reduce(*body, name, lambda, memo))
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
            expr.map_children(|child| inline_and_beta_reduce(child, name, lambda, memo));
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
/// `ty` that mentions the inlined binder, rebuilding each as a fresh immutable
/// `Rc`. `memo` spans the whole `[name ↦ lambda]` sweep, so every occurrence
/// sharing one predicate term — across nodes, not just within one type — is
/// re-pointed at the same rebuilt term and the rewrite is observed uniformly.
///
/// This stays a pass-level walk rather than a `Subst` call because inlining
/// inside a predicate must also *beta-reduce* the call sites it creates —
/// substitution proper is the engine's job and runs inside
/// [`inline_and_beta_reduce`] via `lambda_elim::substitute`.
/// **Why `C = ()` is honest here** even though the rewrite is scope-sensitive (see
/// [`PredMemo`]'s note on what `C` is). `[name ↦ lambda]` must not fire under a
/// binder that shadows `name`, and unlike `subst` — which descends into such a
/// scope with a *restricted* substitution, and so carries that substitution as its
/// `C` — [`inline_and_beta_reduce`] does not descend at all: every binder arm that
/// matches `name` returns its node with the body untouched. An occurrence inside a
/// shadowed scope is therefore never *visited*, so there is nothing for the memo to
/// serve it. This claim depends on that skipping: an arm rewritten to
/// descend-with-a-guard would need the rewrite's scope in `C`, exactly as `subst`
/// carries its `Subst`.
fn inline_in_type_predicates(ty: &mut Type, name: &Name, lambda: &Expr, memo: &PredMemo) {
    walk_refined_predicates_mut(ty, memo, &(), &mut |pred, memo| {
        // A predicate the inlined binder does not occur in is reported
        // *unchanged*, so it keeps its origin `Rc` and stays pointer-shared with
        // its occurrences on other nodes rather than being reallocated at each
        // one the sweep walks past.
        if !is_free(name, pred) {
            return false;
        }
        let old = std::mem::replace(pred, Expr::lit(Lit::Unit));
        *pred = inline_and_beta_reduce(old, name, lambda, memo);
        true
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

/// Whether every refinement the parameter demands is already carried by the
/// argument — so substituting the argument for the binder **discharges** the
/// precondition rather than dropping it.
///
/// Compared with the type-blind predicate relation
/// ([`eq_refinement_predicate`](crate::ccl::eq_refinement_predicate), via `Refinement`'s
/// `PartialEq`), because the two copies legitimately differ in inference metadata.
/// This is deliberately a *syntactic* entailment, not a solver call: post-inference
/// there is no constraint graph left, and the case that must succeed — an argument
/// whose type carries the very refinement the parameter acquired *from* it — is an
/// equality. Anything subtler is exactly what should trip the assert and get a real
/// `restrict` lift.
fn refinement_discharged_by(arg_ty: &Type, param_ty: &Type) -> bool {
    fn layers(mut ty: &Type) -> Vec<&Refinement> {
        let mut out = Vec::new();
        while let Type::Refinement(inner, r) = ty {
            out.push(r);
            ty = inner;
        }
        out
    }
    let demanded = layers(param_ty);
    if demanded.is_empty() {
        return true;
    }
    let supplied = layers(arg_ty);
    demanded.iter().all(|d| supplied.contains(d))
}

// ---------------------------------------------------------------------------
// Provenance recording: drops and fan-out
// ---------------------------------------------------------------------------

/// Collect every main-tree [`NodeId`] reachable in `expr` (itself and all
/// descendants).
///
/// Walks `child_exprs` (main tree only, skipping type-refinement predicates) —
/// the node set the drop diff reasons over.
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

/// Record as a lineage `Transform` discard every consumed id absent from
/// `result` — the nodes this rewrite removed with no surviving counterpart
/// (`Let` wrappers, beta redexes, lambda wrappers, and the `Var` occurrences
/// overwritten by substitution).
///
/// This diff *is* "discard exactly the ids that vanish": a consumed id survives
/// iff it (or its first fan-out copy) still appears in `result`.
///
/// The lineage `Transform` consumes *every* dropped id — including a mid-pass
/// fresh transient a re-run inlined again and then dropped: such a transient was
/// produced by an earlier `Copy` step in this same log, so consuming it composes
/// cleanly at collapse. The discard is pure machinery (`Nature::Machinery`,
/// empty blame) and mints nothing (substitution already ran, sharing ids), so
/// the step flushes a pure discard (`produced: []`).
fn record_drops(consumed: &HashSet<NodeId>, result: &Expr, label: RewriteLabel) {
    let mut surviving = HashSet::new();
    collect_ids(result, &mut surviving);
    let mut dropped: Vec<NodeId> = Vec::new();
    for id in consumed {
        if !surviving.contains(id) {
            dropped.push(*id);
        }
    }
    if !dropped.is_empty() {
        dropped.sort_unstable();
        let _g = lineage::step(label, dropped, Vec::new(), Nature::Machinery);
    }
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
        let refinement = Refinement::born(pred);
        let ty = Type::Refinement(Box::new(Type::Base(BaseType::Int)), refinement);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn iterable_domain_refinement_wraps_iterable() {
        use crate::ccl::Refinement;
        use std::rc::Rc;
        let pred = Rc::new(TypedExpr::lit(Lit::Bool(true)));
        let refinement = Refinement::born(pred);
        let ty = Type::Refinement(Box::new(Type::UIntRange(3)), refinement);
        assert!(is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_fun() {
        // There are infinitely many possible Int → Int functions, so Fun-as-domain
        // has no finite, enumerable domain.
        let ty = Type::Fun {
            name: None,
            kind: crate::ccl::ty::FunKind::Compute,
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
            kind: crate::ccl::ty::FunKind::Compute,
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
            kind: crate::ccl::ty::FunKind::Compute,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Fun {
                name: None,
                kind: crate::ccl::ty::FunKind::Compute,
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
        let refinement = Refinement::born(pred);
        let inner_fun = Type::Fun {
            name: None,
            kind: crate::ccl::ty::FunKind::Compute,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        let ty = Type::Fun {
            name: None,
            kind: crate::ccl::ty::FunKind::Compute,
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
            kind: crate::ccl::ty::FunKind::Compute,
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
            kind: crate::ccl::ty::FunKind::Compute,
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
            kind: crate::ccl::ty::FunKind::Compute,
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
            kind: crate::ccl::ty::FunKind::Compute,
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
        let result = inline_and_beta_reduce(body, &Name::raw("f"), &lambda, &PredMemo::new());
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
        let result = inline_and_beta_reduce(call, &Name::raw("f"), &lambda, &PredMemo::new());
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
        let result = inline_and_beta_reduce(call, &Name::raw("f"), &lambda, &PredMemo::new());
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
        let result = inline_and_beta_reduce(
            shadowed.clone(),
            &Name::raw("f"),
            &replacement,
            &PredMemo::new(),
        );
        assert_eq!(result, shadowed);
    }

    // Refined outer parameter — discharged by the argument's own type
    // -----------------------------------------------------------------------

    /// A literal's singleton (`5 : {Int | __elem == 5}`) reaches the outer
    /// lambda's `param.ty` through coalesce's `refresh_lambda_param_slot`, so
    /// the refined-parameter branch of [`inline_and_beta_reduce`] — and its hard
    /// `assert!` — is live on an ordinary UDF call path rather than dead. The
    /// argument's own type *is* the demanded refinement, so the precondition is
    /// discharged and substitution proceeds.
    ///
    /// Shape mirrors a list-returning UDF over a scalar parameter,
    /// `def rep(k): for x in [1, 2, 3]: yield k` called as `rep(5)`: the outer
    /// `λ k` takes the argument's singleton as its domain, and beta-reduction
    /// leaves the inner iteration lambda with `5` substituted for `k`.
    #[test]
    fn refined_outer_param_discharged_by_literal_argument() {
        let int = Type::Base(BaseType::Int);
        let singleton = crate::ccl::infer::lit_singleton(&Lit::Int(5));
        let range = Type::UIntRange(3);
        let list = fn_ty(range.clone(), int.clone());
        let udf_ty = fn_ty(singleton.clone(), list.clone());

        // λ k : {Int | __elem == 5} → λ __iter_record : [0, 2] → k
        let inner = TypedExpr::lambda(
            "__iter_record",
            range.clone(),
            TypedExpr::var("k").with_ty(int.clone()),
        )
        .with_ty(list.clone());
        let outer = TypedExpr::lambda("k", singleton.clone(), inner).with_ty(udf_ty.clone());

        // 5 ▷ rep, with the argument carrying its singleton.
        let arg = TypedExpr::lit(Lit::Int(5)).with_ty(singleton);
        let call = TypedExpr::apply(arg.clone(), TypedExpr::var("rep").with_ty(udf_ty))
            .with_ty(list.clone());
        let expr = TypedExpr::let_bind("rep", outer, call);

        let result = inline_non_iterable_lambdas(expr);

        let expected = TypedExpr::lambda("__iter_record", range, arg).with_ty(list);
        assert_eq!(result, expected);
    }

    /// The complement: a parameter refinement the argument does *not* carry is a
    /// precondition beta-reduction would silently drop, so the assert fires
    /// rather than substituting. Pins the guard that keeps
    /// [`refinement_discharged_by`] from being weakened to "any refined param is
    /// fine" — e.g. if specialization were ever keyed modulo refinements, one
    /// literal's singleton could reach the param slot of a call made at another.
    #[test]
    #[should_panic(expected = "does not entail")]
    fn refined_outer_param_not_entailed_by_argument_asserts() {
        let int = Type::Base(BaseType::Int);
        let demanded = crate::ccl::infer::lit_singleton(&Lit::Int(5));
        let supplied = crate::ccl::infer::lit_singleton(&Lit::Int(7));
        let udf_ty = fn_ty(demanded.clone(), int.clone());

        let lambda = TypedExpr::lambda("k", demanded, TypedExpr::var("k").with_ty(int.clone()))
            .with_ty(udf_ty.clone());
        let arg = TypedExpr::lit(Lit::Int(7)).with_ty(supplied);
        let call = TypedExpr::apply(arg, TypedExpr::var("f").with_ty(udf_ty)).with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", lambda, call);

        let _ = inline_non_iterable_lambdas(expr);
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
    // Lineage recording: the `RewriteStep`s inline opens fully explain its
    // rewrites. Folding the drained log between the input and output panes must
    // surface no recording-bug leak, and the fan-out (`Copy`) / discard shapes
    // appear where expected.
    // -----------------------------------------------------------------------

    use crate::ccl::lineage::{Leak, Op, SourceProjection, collapse};
    use crate::ccl::provenance::Pass;

    /// Collect every main-tree id in `expr`.
    fn ids(expr: &Expr) -> HashSet<NodeId> {
        let mut acc = HashSet::new();
        collect_ids(expr, &mut acc);
        acc
    }

    /// Inline `input`, then fold the drained lineage log between the input and
    /// output panes. Returns the output tree, the collapse leaks, and the number
    /// of `Copy` steps recorded.
    fn inline_and_collapse(input: Expr) -> (Expr, Vec<Leak>, usize) {
        let input_ids = ids(&input);
        let (output, log) = inline_with_lineage(input);
        let output_ids = ids(&output);
        let copies = log
            .iter()
            .filter(|s| matches!(s.op, Op::Copy { .. }))
            .count();
        let (_map, _proj, leaks) = collapse(
            &[(Pass::Inline, log)],
            &input_ids,
            &output_ids,
            &SourceProjection::new(),
        );
        (output, leaks, copies)
    }

    /// A collapse over a self-contained inline pane pair must surface no leak of
    /// any kind: inline's steps consume/produce live ids only and account for
    /// every input's fate (these fixtures have no unrecorded neighbour pass).
    fn assert_clean(leaks: &[Leak]) {
        assert!(
            leaks.is_empty(),
            "inline pane pair must be leak-free: {leaks:?}"
        );
    }

    #[test]
    fn fanout_at_single_call_site_freshens_the_inlined_copy() {
        // let f: Int → Int = λ x → x in Apply(3, f)  — a single call site.
        // Beta-reduces to `3`; the lambda body is freshened at the duplication
        // site (recorded as `Copy`s) and the `Let`/redex scaffolding is dropped.
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let call = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
            TypedExpr::var("f").with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let input = TypedExpr::let_bind("f", lambda, call);

        let (_output, leaks, copies) = inline_and_collapse(input);
        assert_clean(&leaks);
        assert!(
            copies >= 1,
            "the inlined body must record fan-out Copy steps"
        );
    }

    #[test]
    fn bare_udf_used_twice_records_fanout_copies() {
        // let f: Int → Int = λ x → x in Tuple[f, f]  — two *bare* uses, so each
        // occurrence gets a full freshened copy of the lambda that survives into
        // the output.
        let int = Type::Base(BaseType::Int);
        let fun = fn_ty(int.clone(), int.clone());
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fun.clone());
        let body = TypedExpr::tuple(vec![
            TypedExpr::var("f").with_ty(fun.clone()),
            TypedExpr::var("f").with_ty(fun.clone()),
        ])
        .with_ty(Type::Tuple(vec![fun.clone(), fun.clone()]));
        let input = TypedExpr::let_bind("f", lambda, body);

        let (_output, leaks, copies) = inline_and_collapse(input);
        assert_clean(&leaks);
        assert!(
            copies >= 1,
            "a >=2-use inline must record fan-out Copy steps"
        );
    }

    #[test]
    fn alias_rewrite_is_leak_free() {
        // let f = id in f  — pure alias α-rename; the `Let` and the `Var f`
        // occurrence vanish, `id` survives.
        let fun = fn_ty(Type::UIntRange(3), Type::Base(BaseType::Int));
        let id_expr = TypedExpr::var("id").with_ty(fun.clone());
        let body = TypedExpr::var("f").with_ty(fun);
        let expr = TypedExpr::let_bind("f", id_expr, body);

        let (_output, leaks, _copies) = inline_and_collapse(expr);
        assert_clean(&leaks);
    }

    #[test]
    fn unused_let_discards_everything_leak_free() {
        // let f: Int → Int = id in Lit(42)  — f never used, so the whole
        // binding (the `Let` and the bound `Var id`) is discarded; only Lit(42)
        // survives.
        let int = Type::Base(BaseType::Int);
        let id_expr = TypedExpr::var("id").with_ty(fn_ty(int.clone(), int.clone()));
        let body = TypedExpr::lit(Lit::Int(42)).with_ty(int);
        let expr = TypedExpr::let_bind("f", id_expr, body);

        let (output, leaks, copies) = inline_and_collapse(expr);
        assert_clean(&leaks);
        assert_eq!(copies, 0, "an unused binding fans nothing out");
        // Only the `Lit(42)` survives.
        assert!(matches!(output.node, TypedExprNode::Lit(Lit::Int(42))));
    }

    #[test]
    fn preserves_ids_on_untouched_program() {
        // A program with nothing to inline (scalar `let x = 2 in x + 1`) is
        // reproduced verbatim, ids and all — id preservation is behaviour-neutral.
        let expr = scalar_let();
        let input_ids = ids(&expr);

        let (output, log) = inline_with_lineage(expr);
        // Nothing to rewrite ⇒ no steps recorded.
        assert!(
            log.is_empty(),
            "an untouched program records no steps: {log:?}"
        );
        // Every input id survives with its identity intact.
        assert_eq!(ids(&output), input_ids);
    }
}

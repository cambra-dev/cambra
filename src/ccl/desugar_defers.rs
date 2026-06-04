//! Desugar `Defer`/`Feed`/`Define`/`ExprStmt` nodes into structural
//! let-chain bindings, per-scope `to_<defer>` Record fields, and
//! refined-source channels.
//!
//! Runs **after** [`crate::ccl::lower`] and **before** [`crate::ccl::infer`].
//! After this pass, no [`TypedExprNode::Defer`], [`TypedExprNode::Feed`],
//! [`TypedExprNode::Define`], or [`TypedExprNode::ExprStmt`] nodes remain
//! in the tree — every downstream pass treats those variants as
//! `unreachable!`.
//!
//! # Prototype status
//!
//! **This pass is a prototype.**  The shapes it handles cover the
//! current end-to-end test corpus, but several open design questions
//! remain — most notably the substitution-vs-Record-fields direction
//! for defer-mediating UDFs (see [`LambdaClass`] and the smart walker
//! entry points), and the N-arm Case-with-feeds gap (see
//! [`empty_channel`]).  Expect the algorithm to be reworked rather
//! than incrementally patched.  The umbrella tracking entry lives in
//! `docs/plan.md` under "Tech Debt — `desugar_defers` prototype".
//!
//! # Vocabulary
//!
//! Throughout this module, a **channel** is the expression that
//! resolves a deferred binding: the value the cluster's let-wrap
//! ultimately binds to `d_i`.  For a single `<<` feed the channel is
//! that feed's value (possibly `Unit`-lifted to `Fun(Unit, T)` at
//! top level); for multiple feeds it is their `++`-union; for feeds
//! inside an iteration scope it is the companion `Apply`/`Compose`/
//! `Loop` that mirrors the iteration shape and yields the feed value
//! instead of `Unit`.
//!
//! # Transformation (cluster algorithm)
//!
//! For a cluster of consecutive `let d_i = Defer in …` bindings,
//! `desugar` performs four steps:
//!
//! 1. **Feed extraction.**  Walk the cluster body and collect every
//!    `Feed(d_i, V)` / `Define(d_i, V)` plus the iteration context
//!    they sit in (Compose/Apply/Loop/Case), producing a channel
//!    expression for each `d_i`.
//! 2. **Channel assembly.**  Combine multiple feeds per defer via
//!    `++` ([`TypedExprNode::CollectionUnion`]); lift scalar feeds
//!    to `Fun(Unit, T)`; emit refined-source channels for filter-feed
//!    Case shapes.
//! 3. **α-renaming downstream of the cluster wrap.**  When a channel
//!    captures a free variable whose name is rebound by a `Let`
//!    *between* the cluster wrap site and the original feed
//!    position, [`rename_shadows_then_bind`] α-renames the shadow so
//!    the channel keeps referring to the value it saw at the feed.
//! 4. **Topological emission.**  Emit the cluster's `let d_i =
//!    <channel_i> in …` bindings at the cluster wrap site in
//!    topological order — a defer whose channel references another
//!    cluster defer is bound *after* the one it references.
//!
//! ## Cross-cluster sequencing
//!
//! Defers separated by intervening non-`Defer` lets (`let d_1 = D in
//! let z = E in let d_2 = D in …`) form *separate* clusters.  Each
//! is processed innermost-first.  When the outer cluster's
//! [`rename_shadows_then_bind`] walks the post-inner-processing chain
//! and finds a `Let` whose `bound_expr` references one of its own
//! cluster names, the outer cluster's bindings are emitted at that
//! `Let`'s position rather than at the body's terminal — so a defer
//! is always bound before any expression that mentions it.
//!
//! # Where to read more
//!
//! The full design — two-phase structure (chain rewriter +
//! cluster channelization), per-shape extraction paths (Compose/Apply
//! iteration lambdas, Loop body absorption, filter-feed Case, Case-arm
//! fan-out, defer-mediating UDF smart walker, defer-returning lift,
//! alias inlining), error modes, known gaps, and a navigation map for
//! the source — lives in `src/ccl/design-desugar-defers.md`.
//!
//! The function-level docs in this file explain individual moving
//! parts; this module comment is the entry point.

use std::collections::{HashMap, HashSet};
use std::fmt;

use std::cell::RefCell;
use std::rc::Rc;

use crate::ccl::{
    BaseType, Branch, Expr, Lit, Pattern, Refinement, RefinementKind, Type, TypedExpr,
    TypedExprNode, ccl_utils::count_free, next_refinement_id, walk_loop_children,
};

/// Errors that can arise while desugaring `Defer`/`Feed`/`Define` nodes.
#[derive(Debug, PartialEq)]
pub enum DeferError {
    /// A deferred binding had no corresponding `Feed` or `Define` in its scope.
    NoFeedOrDefine(String),
    /// A deferred binding had more than one `Define` in its scope.
    MultipleDefinitions(String),
    /// Both `Feed` and `Define` were found for the same deferred binding.
    FeedsAndDefinesMixed(String),
    /// A `Define` appeared inside a context where it is not allowed
    /// (e.g. inside a Loop body, Compose element, or Case branch).
    NestedDefinition,
    /// A `Feed` references a defer-handle that was never bound by a
    /// surrounding `let d = Defer`.
    UnboundDeferHandle(String),
    /// A cluster of defers has channels that reference each other
    /// cyclically (e.g. `x ≪= y; y ≪= x`).  Resolving this would
    /// require letrec semantics that CCL does not yet support.  The
    /// payload names one of the defers on the cycle.
    MutuallyRecursiveCycle(String),
}

impl fmt::Display for DeferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeferError::NoFeedOrDefine(name) => {
                write!(f, "deferred binding '{name}' has no feed or define")
            }
            DeferError::MultipleDefinitions(name) => {
                write!(f, "deferred binding '{name}' has multiple definitions")
            }
            DeferError::FeedsAndDefinesMixed(name) => {
                write!(f, "deferred binding '{name}' has both feeds and a define")
            }
            DeferError::NestedDefinition => {
                write!(f, "<<= must occur as a top-level statement")
            }
            DeferError::UnboundDeferHandle(name) => {
                write!(f, "feed/define references unbound defer handle '{name}'")
            }
            DeferError::MutuallyRecursiveCycle(name) => {
                write!(
                    f,
                    "deferred bindings form a mutually recursive cycle through '{name}'"
                )
            }
        }
    }
}

/// Recognise the filter-feed pattern: a two-branch `Case` matching
/// `{guard → Feed(defer_name, V); true → Unit}`.  Returns
/// `Some((guard, V))` on a match, `None` otherwise.
///
/// This is the desugar-pre-inference counterpart of `lambda_elim`'s
/// `is_filter_case_body`: pre-elim Lambdas wrapping such a Case need
/// their channel emitted as a refined Lambda rather than a Record-
/// over-Cases (which would produce a `to_d: V` vs `to_d: Unit` arm
/// shape mismatch).
///
/// FIXME(desugar_defers-prototype): only the 2-arm shape is recognised;
/// 3+-arm Cases with feeds in some-but-not-all arms fall through to
/// [`empty_channel`].  See the umbrella entry in `docs/plan.md` ("Tech
/// Debt — `desugar_defers` prototype") for the planned N-arm refinement-
/// based fan-out.
fn try_extract_filter_feed(body: &Expr, defer_name: &str) -> Option<(Expr, Expr)> {
    let branches = match &body.node {
        // The filter-feed shape is a guard-only `if` (no scrutinee).
        TypedExprNode::Case {
            scrutinee: None,
            branches,
        } => branches,
        _ => return None,
    };
    if branches.len() != 2 {
        return None;
    }
    let arm1 = &branches[1];
    if !matches!(&arm1.guard.node, TypedExprNode::Lit(Lit::Bool(true))) {
        return None;
    }
    if !matches!(&arm1.body.node, TypedExprNode::Lit(Lit::Unit)) {
        return None;
    }
    let arm0 = &branches[0];
    if let TypedExprNode::Feed { name, value } = &arm0.body.node
        && name == defer_name
    {
        return Some((arm0.guard.clone(), (**value).clone()));
    }
    None
}

/// Attempt to apply the defer-returning lift to a `Let` binding.
///
/// Pattern: `let y = (let x = Defer in body_x) in body_y` where
/// `body_x` is *defer-returning* (ends in `Var(x)` after walking
/// through any `ExprStmt`/`Let` chains).
///
/// Rewrites to: `let y = Defer in body_x[x → y] with Var(y) replaced
/// by body_y`.  The substitution `x → Var(y)` is done via
/// [`pre_infer_substitute`], which also renames the *target* string of
/// `Feed`/`Define` nodes when the replacement is a `Var` — so
/// `Feed("x", …)` becomes `Feed("y", …)` automatically.
///
/// Also handles an optional `ExprStmt` prefix on `bound_expr`: the
/// heads of any leading ExprStmts become a prefix that's prepended to
/// the lifted body, with stale Feed/Define target names renamed to `y`.
fn try_lift_defer(binding_name: &str, bound_expr: &Expr, body: &Expr) -> Option<Expr> {
    let mut prefix: Vec<Expr> = Vec::new();
    let mut current = bound_expr.clone();
    while let TypedExprNode::ExprStmt {
        expr: head,
        body: tail,
    } = current.node
    {
        prefix.push(*head);
        current = *tail;
    }
    let (inner_name, inner_body_x) = match current.node {
        TypedExprNode::Let {
            binding: inner_binding,
            bound_expr: inner_be,
            body: inner_body,
        } if matches!(inner_be.node, TypedExprNode::Defer)
            && is_defer_returning(&inner_body, &inner_binding.name) =>
        {
            (inner_binding.name, *inner_body)
        }
        _ => return None,
    };

    // `body_x[x → y]` — also renames Feed/Define targets named `x` to `y`.
    let y_var = Expr::var(binding_name);
    let inner_subst = pre_infer_substitute(inner_body_x, &inner_name, &y_var);

    // Wrap `body_y` with the prefix (renaming stale feed targets to `y`).
    let mut new_outer_body = body.clone();
    for head in prefix.into_iter().rev() {
        let renamed_head = match head.node {
            TypedExprNode::Feed { name: _, value } => TypedExpr {
                ty: head.ty,
                node: TypedExprNode::Feed {
                    name: binding_name.to_string(),
                    value,
                },
                user_annotation: None,
            },
            TypedExprNode::Define { name: _, value } => TypedExpr {
                ty: head.ty,
                node: TypedExprNode::Define {
                    name: binding_name.to_string(),
                    value,
                },
                user_annotation: None,
            },
            _ => head,
        };
        new_outer_body = Expr::expr_stmt(renamed_head, new_outer_body);
    }
    // Splice `new_outer_body` in at the trailing `Var(y)` of
    // `inner_subst`, so the lifted body comes BEFORE the original outer
    // body (preserving execution order: inner-then-outer).
    let spliced = replace_result_var(inner_subst, new_outer_body);

    Some(Expr::let_bind(
        binding_name.to_string(),
        Expr::new(TypedExprNode::Defer),
        spliced,
    ))
}

/// Return `true` if `expr` ends in `Var(name)` after walking through
/// any leading `ExprStmt`/`Let` chains (the body's terminal position).
fn is_defer_returning(expr: &Expr, name: &str) -> bool {
    match &expr.node {
        TypedExprNode::Var(n) => n == name,
        TypedExprNode::ExprStmt { body, .. } => is_defer_returning(body, name),
        TypedExprNode::Let { binding, body, .. } => {
            binding.name != name && is_defer_returning(body, name)
        }
        _ => false,
    }
}

/// Replace the trailing `Var(_)` at the terminal of `expr` (walking
/// through `ExprStmt`/`Let` chains) with `replacement`.
///
/// Caller is responsible for ensuring `expr` actually ends in a
/// `Var` (e.g. via [`is_defer_returning`]).
fn replace_result_var(expr: Expr, replacement: Expr) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let new_node = match node {
        TypedExprNode::Var(_) => return replacement,
        TypedExprNode::ExprStmt { expr: e, body } => TypedExprNode::ExprStmt {
            expr: e,
            body: Box::new(replace_result_var(*body, replacement)),
        },
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => TypedExprNode::Let {
            binding,
            bound_expr,
            body: Box::new(replace_result_var(*body, replacement)),
        },
        _ => panic!("replace_result_var: expression doesn't end in a Var"),
    };
    TypedExpr {
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Classification of a let-bound lambda by its interaction with defers.
///
/// The desugar pass treats each class differently at call sites:
/// - [`LambdaClass::VarBody`]: pure α-rename — `f(arg)` reduces to
///   `body[param → arg]` (a `Var`).
/// - [`LambdaClass::ParamAsTarget`]: the function's body uses the
///   lambda's param as a `Feed`/`Define` target.  At each call site,
///   the body's feeds logically target the call's arg; channel
///   contributions are extracted by substituting param → arg.
/// - [`LambdaClass::DeferIntroducing`]: the function's body
///   *creates* a fresh `Defer` per call.  The defer must be floated
///   to a new lambda param so each call site can allocate its own
///   fresh `Defer` value.
/// - [`LambdaClass::Plain`]: the function doesn't interact with
///   defers.  No special handling needed.
///
/// Classification is done in order of structural specificity:
/// `VarBody` first (most specific), then `DeferIntroducing` (must
/// float before treating as anything else), then `ParamAsTarget`,
/// then `Plain`.  This order matters: a body that *both* introduces
/// a defer *and* uses the param as a target is classified as
/// `DeferIntroducing`, because the float transformation must happen
/// before per-call extraction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LambdaClass {
    VarBody,
    ParamAsTarget,
    DeferIntroducing,
    Plain,
}

/// Classify a let-bound `lambda` by its defer-interaction pattern.
/// Returns [`LambdaClass::Plain`] if `lambda` is not a `Lambda` node.
fn classify_lambda(lambda: &Expr) -> LambdaClass {
    let TypedExprNode::Lambda { param, body, .. } = &lambda.node else {
        return LambdaClass::Plain;
    };
    if matches!(&body.node, TypedExprNode::Var(_)) {
        return LambdaClass::VarBody;
    }
    if contains_defer(body) {
        return LambdaClass::DeferIntroducing;
    }
    if contains_feed_or_define_for(body, &param.name) {
        return LambdaClass::ParamAsTarget;
    }
    // Post-float DeferIntroducing form: `λp → λ__floated → body`
    // where `body` either uses `__floated` as a feed target or
    // returns `__floated`.  We treat this as `DeferIntroducing` so
    // the smart cluster walker handles it.
    if let TypedExprNode::Lambda {
        param: inner_param,
        body: inner_body,
        ..
    } = &body.node
        && (matches!(&inner_body.node, TypedExprNode::Var(name) if name == &inner_param.name)
            || contains_feed_or_define_for(inner_body, &inner_param.name))
    {
        return LambdaClass::DeferIntroducing;
    }
    LambdaClass::Plain
}

/// If `lambda` is a [`LambdaClass::DeferIntroducing`] function whose
/// body has the shape `λ p → let x = Defer in inner`, rewrite it to
/// `λ p → λ __floated_x → inner[x → __floated_x]` so the internal
/// `Defer` becomes an explicit second parameter.
///
/// Returns `None` if `lambda` doesn't match the simple float-able
/// shape — e.g. the `Defer` is nested inside a non-trivial outer
/// expression rather than appearing as the immediate `let`-binding.
/// We will widen the shape match as we encounter more patterns
/// in test cases; for now we handle the canonical lowering shape:
///
/// ```text
/// def f(n):                          λn → λ__floated_x →
///   x = defer()           ───►         inner_body[x → __floated_x]
///   inner_body[x]
///   x
/// ```
///
/// After float the lambda has class [`LambdaClass::ParamAsTarget`]
/// — the floated param is the defer-target, and the body's feeds
/// (which originally targeted `x`) now target `__floated_x`.
fn float_defer_in_lambda(lambda: Expr) -> Option<Expr> {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = lambda;
    let TypedExprNode::Lambda {
        param,
        body,
        refinement,
    } = node
    else {
        return None;
    };
    let (modified_body, floated_name) = extract_defer_binding(*body)?;
    let inner_lambda = Expr::lambda(&floated_name, Type::Hole, modified_body);
    let outer_lambda = TypedExpr {
        node: TypedExprNode::Lambda {
            param,
            body: Box::new(inner_lambda),
            refinement,
        },
        ty,
        user_annotation,
    };
    Some(outer_lambda)
}

/// Walk `body` looking for the first `let x = Defer in inner` binding,
/// and remove it.  Returns the modified body — with the `Defer` let
/// collapsed and `x` renamed to `__floated_x` everywhere inside its
/// scope — and the floated name.  Returns `None` if no `Defer`
/// binding is found.
///
/// The walk descends through prefix `Let` and `ExprStmt` nodes
/// (everything that wraps the body's "main work" without changing the
/// scope shape).  Stopping when we hit other constructs (`Lambda`,
/// `Apply`, …) keeps the float to the function's *own* defer rather
/// than nested-closure defers.
fn extract_defer_binding(body: Expr) -> Option<(Expr, String)> {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = body;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body: inner,
        } => {
            if matches!(bound_expr.node, TypedExprNode::Defer) {
                // Found it.  Rename binding.name → __floated_<name>
                // throughout the inner body.
                let floated_name = format!("__floated_{}", binding.name);
                let renamed =
                    pre_infer_substitute(*inner, &binding.name, &Expr::var(&floated_name));
                return Some((renamed, floated_name));
            }
            // Not the Defer-let — descend into inner, keeping this
            // let in place.
            let (modified_inner, floated_name) = extract_defer_binding(*inner)?;
            let new_body = TypedExpr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(modified_inner),
                },
                ty,
                user_annotation,
            };
            Some((new_body, floated_name))
        }
        TypedExprNode::ExprStmt { expr, body: inner } => {
            // Descend through ExprStmt's body.  We intentionally do
            // *not* recurse into `expr` because that would be looking
            // inside an iteration's side-effect chain rather than the
            // function's own structural defer.
            let (modified_inner, floated_name) = extract_defer_binding(*inner)?;
            let new_body = TypedExpr {
                node: TypedExprNode::ExprStmt {
                    expr,
                    body: Box::new(modified_inner),
                },
                ty,
                user_annotation,
            };
            Some((new_body, floated_name))
        }
        _ => None,
    }
}

/// Return `true` if `expr` is an `Apply` chain whose root call (or
/// any nested call) targets a [`LambdaClass::DeferIntroducing`]
/// function registered in `ctx`.  Used by [`rewrite_chains_in_scope`]
/// to decide whether a let-binding's bound expression needs the
/// fresh-`Defer` wrap.
///
/// **Not idempotent against already-wrapped DI forms.**  Given an
/// expression shaped like `Apply { function: Apply { function:
/// Var(DI_fn), argument: _ }, argument: Var(_) }` (the output of
/// [`wrap_di_calls_in_chain`]), this function returns `true` because
/// the recursion into `function` finds the inner `Var(DI_fn)`.  A
/// caller that fed a wrapped form back through `chain_has_di` and
/// then wrapped on the `true` result would double-wrap the chain.
/// Today's only caller is [`rewrite_chains_in_scope`], which wraps
/// once and returns the result inside an `ExprStmt` without recursing
/// through the wrapped tree — so the wrapped shape never re-enters
/// this function in production.  An audit panic (`unreachable!`) was
/// kept in place during development and confirmed no production path
/// hits the wrapped form; see commit history for details.  Future
/// callers must preserve this invariant.
///
/// The recursion into `argument`/`function` below is for
/// composed-chain detection (DI nested inside DI/PaT), not for
/// idempotency.
fn chain_has_di(expr: &Expr, ctx: &DesugarCtx) -> bool {
    match &expr.node {
        TypedExprNode::Apply { function, argument } => {
            if let TypedExprNode::Var(fname) = &function.node
                && let Some(finfo) = ctx.lookup_function(fname)
                && finfo.class == LambdaClass::DeferIntroducing
            {
                return true;
            }
            chain_has_di(argument, ctx) || chain_has_di(function, ctx)
        }
        _ => false,
    }
}

/// Wrap each `Apply(arg, Var(f))` in `expr` whose target `f` is a
/// [`LambdaClass::DeferIntroducing`] function (after float) with the
/// missing second application of `Var(defer_name)`:
///
/// ```text
/// Apply(arg, Var(f))  ⟹  Apply(Apply(arg, Var(f)), Var(defer_name))
/// ```
///
/// In CCL's `Apply { function, argument }` notation that's:
///
/// ```text
/// Apply { function: Var(f), argument: arg }
///   ⟹  Apply { function: Apply { function: Var(f), argument: arg },
///              argument: Var(defer_name) }
/// ```
///
/// The doubled application supplies the floated defer-handle so the
/// curried `λp → λ__floated → body` reduces to `body[p=arg,
/// __floated=defer_name]` at evaluation.
///
/// For composed DI-DI chains like `doubles(add_one(xs))` (both DI),
/// each DI call needs its **own** fresh defer — they're separate
/// values flowing through the chain.  The *outermost* DI call uses
/// `outermost_defer` (typically the let-binding's name).  Inner DI
/// calls get fresh names allocated via [`DesugarCtx::fresh_floated_name`];
/// those names are returned via `fresh_defers` so the caller can emit
/// the corresponding `let __fresh = Defer in …` allocations.
///
/// Walks top-down so the outermost DI is identified first.
fn wrap_di_calls_in_chain(
    expr: Expr,
    outermost_defer: &str,
    ctx: &mut DesugarCtx,
) -> (Expr, Vec<String>) {
    let mut fresh_defers = Vec::new();
    let mut outermost_consumed = false;
    let wrapped = wrap_di_calls_helper(
        expr,
        outermost_defer,
        &mut outermost_consumed,
        &mut fresh_defers,
        ctx,
    );
    (wrapped, fresh_defers)
}

fn wrap_di_calls_helper(
    expr: Expr,
    outermost_defer: &str,
    outermost_consumed: &mut bool,
    fresh_defers: &mut Vec<String>,
    ctx: &mut DesugarCtx,
) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    match node {
        TypedExprNode::Apply { function, argument } => {
            // Determine if this Apply is itself a DI call before
            // recursing — so the outermost DI claims `outermost_defer`
            // first (top-down).
            let is_di = matches!(&function.node, TypedExprNode::Var(fname)
                if ctx.lookup_function(fname).is_some_and(|f| f.class == LambdaClass::DeferIntroducing));
            let this_defer = if is_di {
                if !*outermost_consumed {
                    *outermost_consumed = true;
                    outermost_defer.to_string()
                } else {
                    let fresh = ctx.fresh_floated_name("inner");
                    fresh_defers.push(fresh.clone());
                    fresh
                }
            } else {
                String::new()
            };
            let argument = wrap_di_calls_helper(
                *argument,
                outermost_defer,
                outermost_consumed,
                fresh_defers,
                ctx,
            );
            let function = wrap_di_calls_helper(
                *function,
                outermost_defer,
                outermost_consumed,
                fresh_defers,
                ctx,
            );
            let inner = TypedExpr {
                node: TypedExprNode::Apply {
                    function: Box::new(function),
                    argument: Box::new(argument),
                },
                ty: ty.clone(),
                user_annotation: user_annotation.clone(),
            };
            if is_di {
                TypedExpr {
                    node: TypedExprNode::Apply {
                        function: Box::new(inner),
                        argument: Box::new(Expr::var(&this_defer)),
                    },
                    ty,
                    user_annotation,
                }
            } else {
                inner
            }
        }
        other => TypedExpr {
            node: other,
            ty,
            user_annotation,
        },
    }
}

/// Walk `expr` and rewrite defer-mediating UDF call patterns:
///
/// - `Apply(arg, Var(f))` where `f` is [`LambdaClass::VarBody`]: replace
///   with `body[param → arg]`.  Pure α-rename; no defer interaction.
/// - `let y = chain in rest` where `chain` is an `Apply` chain
///   involving at least one [`LambdaClass::DeferIntroducing`] call:
///   rewrite to
///   `let y = Defer in ExprStmt(wrap_di_calls_in_chain(chain, y), rest)`.
///   The body of the chain (along with any [`LambdaClass::ParamAsTarget`]
///   calls in it) gets channelized when the cluster algorithm walks
///   `y`'s scope — the smart walker matches the wrapped Apply form
///   and walks into the function bodies via logical param
///   substitution.
/// - [`LambdaClass::ParamAsTarget`] calls outside a let-binding-with-DI
///   are left intact: the smart walker handles them directly when the
///   cluster algorithm processes the relevant outer defer.
///
/// FIXME(desugar_defers-prototype): the [`LambdaClass`] dispatch and
/// the smart-walker plumbing in [`try_smart_walk_pat`] /
/// [`try_smart_walk_di`] are a working sketch.  The open design
/// question — Record-of-`to_<target>`-fields vs. body substitution at
/// the call site — has not been settled.  Expect rework rather than
/// patches.  See the umbrella entry in `docs/plan.md` ("Tech Debt —
/// `desugar_defers` prototype").
fn rewrite_chains_in_scope(expr: Expr, ctx: &mut DesugarCtx) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let new_node = match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // If the let binds a defer-mediating Lambda, register it
            // in ctx so chain detection downstream sees calls to it
            // as DI/PaT.  Without this, a chain like
            // `doubles(add_one(xs))` (both DI) processed inside
            // `add_one`'s let-arm would miss `doubles` because it's
            // not registered yet — leaving `doubles`'s call unwrapped.
            if let TypedExprNode::Lambda { .. } = &bound_expr.node {
                let class = classify_lambda(&bound_expr);
                if class != LambdaClass::Plain {
                    let lambda = if class == LambdaClass::DeferIntroducing {
                        float_defer_in_lambda((*bound_expr).clone())
                            .unwrap_or_else(|| (*bound_expr).clone())
                    } else {
                        (*bound_expr).clone()
                    };
                    // Phase 1 registers with the original (un-body-rewritten)
                    // lambda — the chain rewriter only needs class + name
                    // for call-shape detection.  Phase 2 will re-register
                    // with the rewritten lambda and the populated
                    // `feed_targets` / `primary_target` fields used by the
                    // smart walker's Record-projection logic.
                    let info = FunctionInfo {
                        class,
                        lambda: lambda.clone(),
                        feed_targets: Vec::new(),
                        primary_target: String::new(),
                    };
                    let prev = ctx.register_function(binding.name.clone(), info);
                    let new_body = rewrite_chains_in_scope(*body, ctx);
                    ctx.unregister_function(&binding.name, prev);
                    return Expr::let_bind(binding.name.clone(), lambda, new_body);
                }
            }
            // Check chain status BEFORE recursing — we want to use
            // `binding.name` as the float defer (so the outer scope
            // can add more feeds via alias-inline of the let-binding).
            // Recursing into bound_expr first would wrap any inner DI
            // chain with a fresh defer, losing the chance to use
            // `binding.name`.
            if chain_has_di(&bound_expr, ctx) {
                let (wrapped, fresh_defers) =
                    wrap_di_calls_in_chain(*bound_expr, &binding.name, ctx);
                let new_body = rewrite_chains_in_scope(*body, ctx);
                // Emit `let binding.name = Defer in let fresh_0 =
                // Defer in … let fresh_N = Defer in ExprStmt(wrapped,
                // body)`.  The fresh defers (inner-wrap DI calls) are
                // the INNER lets so [`channelize_cluster`]'s reverse
                // iteration processes them first — their feeds are
                // nested inside the wrapped chain, and processing
                // them first leaves the outer call's structure
                // intact for the outermost DI smart-walker match.
                let mut result = Expr::expr_stmt(wrapped, new_body);
                for fresh in fresh_defers.into_iter().rev() {
                    result = Expr::let_bind(fresh, Expr::new(TypedExprNode::Defer), result);
                }
                result = Expr::let_bind(
                    binding.name.clone(),
                    Expr::new(TypedExprNode::Defer),
                    result,
                );
                return result;
            }
            let bound_expr = rewrite_chains_in_scope(*bound_expr, ctx);
            let body = rewrite_chains_in_scope(*body, ctx);
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(bound_expr),
                body: Box::new(body),
            }
        }
        TypedExprNode::Apply { function, argument } => {
            // For an Apply at expression position (not consumed by a
            // surrounding `let y = …`'s `bound_expr`), if it's a DI
            // chain we still need to allocate a fresh defer to host
            // the channel.  Check BEFORE recursing so inner DI calls
            // are wrapped with the SAME fresh defer (via
            // [`wrap_di_calls_in_chain`]).
            let expr_for_check = TypedExpr {
                node: TypedExprNode::Apply { function, argument },
                ty: ty.clone(),
                user_annotation: user_annotation.clone(),
            };
            if chain_has_di(&expr_for_check, ctx) {
                let fresh = ctx.fresh_floated_name("chain");
                let (wrapped, inner_fresh_defers) =
                    wrap_di_calls_in_chain(expr_for_check, &fresh, ctx);
                // Same nesting order as the Let case: outermost
                // (`fresh`) is the OUTER let; inner-wrap defers are
                // INNER lets so the cluster algo processes them first.
                let mut result = Expr::expr_stmt(wrapped, Expr::var(&fresh));
                for fresh_inner in inner_fresh_defers.into_iter().rev() {
                    result = Expr::let_bind(fresh_inner, Expr::new(TypedExprNode::Defer), result);
                }
                result = Expr::let_bind(fresh.clone(), Expr::new(TypedExprNode::Defer), result);
                return result;
            }
            // Not a DI chain.  Recurse into function and argument
            // (might be nested ParamAsTarget chains, alias-inlines,
            // or non-defer code).  Then apply VarBody α-rename if
            // the Apply directly calls a VarBody function.
            let TypedExpr {
                node:
                    TypedExprNode::Apply {
                        function: outer_function,
                        argument: outer_argument,
                    },
                ..
            } = expr_for_check
            else {
                unreachable!("we just constructed an Apply")
            };
            let function = rewrite_chains_in_scope(*outer_function, ctx);
            let argument = rewrite_chains_in_scope(*outer_argument, ctx);
            if let TypedExprNode::Var(fname) = &function.node
                && let Some(finfo) = ctx.lookup_function(fname)
                && finfo.class == LambdaClass::VarBody
            {
                let TypedExprNode::Lambda { param, body, .. } = &finfo.lambda.node else {
                    unreachable!("VarBody classifier guarantees Lambda")
                };
                return pre_infer_substitute((**body).clone(), &param.name, &argument);
            }
            TypedExprNode::Apply {
                function: Box::new(function),
                argument: Box::new(argument),
            }
        }
        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(rewrite_chains_in_scope(*left, ctx)),
            op,
            right: Box::new(rewrite_chains_in_scope(*right, ctx)),
        },
        TypedExprNode::UnaryOp(op, inner) => {
            TypedExprNode::UnaryOp(op, Box::new(rewrite_chains_in_scope(*inner, ctx)))
        }
        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(rewrite_chains_in_scope(*input, ctx)),
            kind,
        },
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => TypedExprNode::Lambda {
            param,
            body: Box::new(rewrite_chains_in_scope(*body, ctx)),
            refinement,
        },
        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(
            elts.into_iter()
                .map(|e| rewrite_chains_in_scope(e, ctx))
                .collect(),
        ),
        TypedExprNode::List(elts) => TypedExprNode::List(
            elts.into_iter()
                .map(|e| rewrite_chains_in_scope(e, ctx))
                .collect(),
        ),
        TypedExprNode::Compose(elts) => TypedExprNode::Compose(
            elts.into_iter()
                .map(|e| rewrite_chains_in_scope(e, ctx))
                .collect(),
        ),
        TypedExprNode::CollectionUnion(elts) => TypedExprNode::CollectionUnion(
            elts.into_iter()
                .map(|e| rewrite_chains_in_scope(e, ctx))
                .collect(),
        ),
        TypedExprNode::Record(fields) => TypedExprNode::Record(
            fields
                .into_iter()
                .map(|(n, e)| (n, rewrite_chains_in_scope(e, ctx)))
                .collect(),
        ),
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => TypedExprNode::Case {
            scrutinee: scrutinee.map(|s| Box::new(rewrite_chains_in_scope(*s, ctx))),
            branches: branches
                .into_iter()
                .map(
                    |Branch {
                         pattern,
                         guard,
                         body,
                     }| Branch {
                        pattern,
                        guard: rewrite_chains_in_scope(guard, ctx),
                        body: rewrite_chains_in_scope(body, ctx),
                    },
                )
                .collect(),
        },
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => walk_loop_children(params, init_args, source, loop_body, None, |e| {
            rewrite_chains_in_scope(e, ctx)
        }),
        TypedExprNode::ExprStmt { expr, body } => TypedExprNode::ExprStmt {
            expr: Box::new(rewrite_chains_in_scope(*expr, ctx)),
            body: Box::new(rewrite_chains_in_scope(*body, ctx)),
        },
        TypedExprNode::Feed { name, value } => TypedExprNode::Feed {
            name,
            value: Box::new(rewrite_chains_in_scope(*value, ctx)),
        },
        TypedExprNode::Define { name, value } => TypedExprNode::Define {
            name,
            value: Box::new(rewrite_chains_in_scope(*value, ctx)),
        },
        leaf @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer) => leaf,
        TypedExprNode::Error => crate::unexpected_error_node!(),
        // Variant constructors / Match are not yet emitted by lowering
        // (§3.2 surface-syntax workstream lands separately); desugar_defers
        // runs on the lowered AST so it cannot see them today.
        TypedExprNode::VariantCtor { .. } => {
            unreachable!("desugar_defers: VariantCtor not yet emitted by lowering")
        }
    };
    TypedExpr {
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Return `true` if `expr` contains a `Defer` node anywhere
/// (transitively).
fn contains_defer(expr: &Expr) -> bool {
    matches!(expr.node, TypedExprNode::Defer) || expr.any_child(contains_defer)
}

/// Return `true` if any nested `Let` or `Lambda` inside `expr` rebinds
/// `name` (shadowing it).  Used by the alias-inline check to avoid
/// substituting an alias name with a source name that would be captured
/// by a shadowing rebind inside the body.
fn rebinds(expr: &Expr, name: &str) -> bool {
    // Recognise binder variants that introduce `name` directly.  Lambda's
    // refinement and Let's bound_expr live in the outer scope (not bound
    // by the param/binding), but if they themselves contain a rebind of
    // `name` further down, `any_child` finds it via structural recursion
    // below — no need to short-circuit on the binder structure here.
    let here = match &expr.node {
        TypedExprNode::Let { binding, .. } => binding.name == name,
        TypedExprNode::Lambda { param, .. } => param.name == name,
        TypedExprNode::Loop { params, .. } => params.iter().any(|p| p.name == name),
        TypedExprNode::Case { branches, .. } => branches
            .iter()
            .any(|b| b.pattern.as_ref().is_some_and(|p| p.binding.name == name)),
        _ => false,
    };
    here || expr.any_child(|c| rebinds(c, name))
}

/// Return `true` if `expr` contains any `Feed(target, …)` or
/// `Define(target, …)` node where `target == name`, respecting shadowing
/// by `Let`/`Lambda` bindings that rebind `name`.
fn contains_feed_or_define_for(expr: &Expr, name: &str) -> bool {
    match &expr.node {
        // Hit: the Feed/Define's target string matches.  Also recurse into
        // the value (a Feed value could itself contain another
        // Feed/Define of the same name).
        TypedExprNode::Feed { name: t, value } | TypedExprNode::Define { name: t, value } => {
            t == name || contains_feed_or_define_for(value, name)
        }
        // Binder variants need shadowing-aware recursion: descend into
        // bodies only when the binder doesn't shadow `name`.  The
        // bound_expr / init_args / source positions are outside the
        // binder's scope and are walked unconditionally.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            contains_feed_or_define_for(bound_expr, name)
                || (binding.name != name && contains_feed_or_define_for(body, name))
        }
        TypedExprNode::Lambda { param, body, .. } => {
            param.name != name && contains_feed_or_define_for(body, name)
        }
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
            ..
        } => {
            init_args
                .iter()
                .any(|e| contains_feed_or_define_for(e, name))
                || contains_feed_or_define_for(source, name)
                || (!params.iter().any(|p| p.name == name)
                    && contains_feed_or_define_for(loop_body, name))
        }
        _ => expr.any_child(|c| contains_feed_or_define_for(c, name)),
    }
}

/// Substitute every free `Var(name)` in `expr` with `replacement`.
///
/// A simpler variant of [`crate::ccl::lambda_elim::substitute`] that does
/// not require the expression to be type-checked — desugar runs
/// pre-inference where types are still `Hole`s.  When `replacement` is a
/// `Var(new_name)`, `Feed`/`Define` nodes whose target string matches
/// `name` are also renamed to `new_name`; this is the α-renaming that
/// makes alias-inlining for defer handles correct.
fn pre_infer_substitute(expr: Expr, name: &str, replacement: &Expr) -> Expr {
    let replacement_name = match &replacement.node {
        TypedExprNode::Var(n) => Some(n.clone()),
        _ => None,
    };
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let new_node = match node {
        TypedExprNode::Var(n) if n == name => return replacement.clone(),
        TypedExprNode::Var(n) => TypedExprNode::Var(n),
        leaf @ (TypedExprNode::Lit(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer) => leaf,
        TypedExprNode::Apply { function, argument } => TypedExprNode::Apply {
            function: Box::new(pre_infer_substitute(*function, name, replacement)),
            argument: Box::new(pre_infer_substitute(*argument, name, replacement)),
        },
        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(pre_infer_substitute(*left, name, replacement)),
            op,
            right: Box::new(pre_infer_substitute(*right, name, replacement)),
        },
        TypedExprNode::UnaryOp(op, inner) => TypedExprNode::UnaryOp(
            op,
            Box::new(pre_infer_substitute(*inner, name, replacement)),
        ),
        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(pre_infer_substitute(*input, name, replacement)),
            kind,
        },
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            // Param shadows `name` inside the body.
            let body = if param.name == name {
                *body
            } else {
                pre_infer_substitute(*body, name, replacement)
            };
            TypedExprNode::Lambda {
                param,
                body: Box::new(body),
                refinement,
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_expr = pre_infer_substitute(*bound_expr, name, replacement);
            let body = if binding.name == name {
                *body
            } else {
                pre_infer_substitute(*body, name, replacement)
            };
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(bound_expr),
                body: Box::new(body),
            }
        }
        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(
            elts.into_iter()
                .map(|e| pre_infer_substitute(e, name, replacement))
                .collect(),
        ),
        TypedExprNode::List(elts) => TypedExprNode::List(
            elts.into_iter()
                .map(|e| pre_infer_substitute(e, name, replacement))
                .collect(),
        ),
        TypedExprNode::Compose(elts) => TypedExprNode::Compose(
            elts.into_iter()
                .map(|e| pre_infer_substitute(e, name, replacement))
                .collect(),
        ),
        TypedExprNode::CollectionUnion(elts) => TypedExprNode::CollectionUnion(
            elts.into_iter()
                .map(|e| pre_infer_substitute(e, name, replacement))
                .collect(),
        ),
        TypedExprNode::Record(fields) => TypedExprNode::Record(
            fields
                .into_iter()
                .map(|(n, e)| (n, pre_infer_substitute(e, name, replacement)))
                .collect(),
        ),
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => TypedExprNode::Case {
            scrutinee: scrutinee.map(|s| Box::new(pre_infer_substitute(*s, name, replacement))),
            branches: branches
                .into_iter()
                .map(
                    |Branch {
                         pattern,
                         guard,
                         body,
                     }| Branch {
                        pattern,
                        guard: pre_infer_substitute(guard, name, replacement),
                        body: pre_infer_substitute(body, name, replacement),
                    },
                )
                .collect(),
        },
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => walk_loop_children(params, init_args, source, loop_body, Some(name), |e| {
            pre_infer_substitute(e, name, replacement)
        }),
        TypedExprNode::ExprStmt { expr: e, body } => TypedExprNode::ExprStmt {
            expr: Box::new(pre_infer_substitute(*e, name, replacement)),
            body: Box::new(pre_infer_substitute(*body, name, replacement)),
        },
        // Feed/Define nodes: rename the target string when the
        // replacement is itself a Var, and substitute inside the value.
        TypedExprNode::Feed {
            name: target,
            value,
        } => TypedExprNode::Feed {
            name: if target == name {
                replacement_name.clone().unwrap_or(target)
            } else {
                target
            },
            value: Box::new(pre_infer_substitute(*value, name, replacement)),
        },
        TypedExprNode::Define {
            name: target,
            value,
        } => TypedExprNode::Define {
            name: if target == name {
                replacement_name.clone().unwrap_or(target)
            } else {
                target
            },
            value: Box::new(pre_infer_substitute(*value, name, replacement)),
        },
        TypedExprNode::Error => crate::unexpected_error_node!(),
        TypedExprNode::VariantCtor { .. } => {
            unreachable!("desugar_defers: VariantCtor not yet emitted by lowering")
        }
    };
    TypedExpr {
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Recorded information about a defer-mediating function currently in
/// scope.  Lives in [`DesugarCtx::functions`].  See the design doc at
/// `src/ccl/design-desugar-defers.md` for the chain rewriter and
/// smart-walker mechanics.
#[derive(Clone)]
struct FunctionInfo {
    /// The function's defer-interaction class.  Determines how the
    /// chain rewriter treats this function at call sites.
    class: LambdaClass,
    /// The lambda after any pre-walk transformations (float for
    /// [`LambdaClass::DeferIntroducing`]) and, for Phase 2
    /// registrations, the body rewrite that produced a contributions
    /// `Record`.  Phase 1 registrations carry the un-rewritten
    /// lambda (chain rewriter only needs class + name for call-shape
    /// detection).
    lambda: Expr,
    /// All defer targets the function's body feeds, primary target
    /// first.  Empty when registered by Phase 1 (which doesn't rewrite
    /// the body and therefore doesn't know the full target set);
    /// populated by Phase 2 after [`rewrite_lambda_to_return_contributions`].
    ///
    /// At call sites, the smart walker uses these names to construct
    /// the per-target `Record` projection that becomes the cluster's
    /// channel contribution.
    feed_targets: Vec<String>,
    /// The primary target — the lambda-param-side defer name (PaT
    /// param, or floated inner param for DI).  At call sites this
    /// maps to the call's first argument; closure-captured targets
    /// in [`Self::feed_targets`] keep their own names across the
    /// function boundary.  Empty string when registered by Phase 1.
    primary_target: String,
}

/// Mutable state threaded through the desugar walk.
///
/// Holds a monotonic counter used to generate fresh α-renames when the
/// cluster-binding wrap needs to shield a channel's free-variable
/// reference from a downstream `Let` shadow (see
/// [`rename_shadows_then_bind`]), plus a lexically-scoped map of
/// defer-mediating functions in scope, consulted by the chain
/// rewriter at call sites.
struct DesugarCtx {
    counter: u64,
    /// Defer-mediating functions in lexical scope, keyed by binding
    /// name.  Populated by [`desugar`]'s `Let` arm when classification
    /// flags a lambda as non-`Plain`; the previous binding (if any)
    /// is saved and restored on scope exit so shadowing is handled
    /// correctly.
    functions: HashMap<String, FunctionInfo>,
}

impl DesugarCtx {
    fn new() -> Self {
        Self {
            counter: 0,
            functions: HashMap::new(),
        }
    }

    fn fresh_shadow_rename(&mut self, name: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("__shadowed_{name}_{n}")
    }

    /// Mint a fresh name for the defer allocated at one direct call
    /// site of a [`LambdaClass::DeferIntroducing`] function.  The
    /// `defer_name` part is the original (pre-float) defer's name,
    /// kept as a breadcrumb so debug output is readable.
    fn fresh_floated_name(&mut self, defer_name: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("__floated_{defer_name}_{n}")
    }

    /// Register a defer-mediating function as in-scope.  Returns the
    /// previous binding under `name` (if any) so the caller can
    /// restore it when the lexical scope ends.
    fn register_function(&mut self, name: String, info: FunctionInfo) -> Option<FunctionInfo> {
        self.functions.insert(name, info)
    }

    /// Pop a function registration on scope exit.  Restores the saved
    /// previous binding (if any).
    fn unregister_function(&mut self, name: &str, prev: Option<FunctionInfo>) {
        match prev {
            Some(p) => {
                self.functions.insert(name.to_string(), p);
            }
            None => {
                self.functions.remove(name);
            }
        }
    }

    fn lookup_function(&self, name: &str) -> Option<&FunctionInfo> {
        self.functions.get(name)
    }
}

/// The field name on the per-scope result Record that carries the channel
/// contributions for defer `d`.
fn channel_field_name(defer_name: &str) -> String {
    format!("to_{defer_name}")
}

/// Eliminate all `Defer`/`Feed`/`Define` nodes from `expr`.
///
/// Walks the expression top-down.  Every `let d = Defer in body` triggers
/// the channelization rewrite described in the module docs.  After this
/// pass returns, no `Defer`, `Feed`, or `Define` nodes remain — any
/// residue is reported as [`DeferError::UnboundDeferHandle`].
///
/// As a final step, every `ExprStmt(e, b)` is collapsed to `b`.  The
/// variant only existed as a vehicle for surfacing `Feed`/`Define` sites
/// in statement position; once those have been extracted into source
/// channels, the surrounding `ExprStmt`'s `e` argument is a pure
/// `Unit`-typed value that can be dropped.  Doing this in `desugar_defers`
/// (rather than leaving it for `simplify`) means no later pass needs to
/// pattern-match `ExprStmt`.
pub fn run(expr: Expr) -> Result<Expr, DeferError> {
    let mut ctx = DesugarCtx::new();
    // Phase 1: chain-rewrite defer-mediating UDF call sites.  Walks
    // the tree top-down registering defer-mediating functions and
    // wrapping their direct call chains with `let fresh = Defer in
    // ExprStmt(wrapped_call, …)` shapes (using the let-binding's name
    // as the outermost defer where possible, fresh defers for
    // composed inner DI calls).  After this pass `ctx.functions` is
    // empty again — registrations unregister on scope exit.
    let rewritten = rewrite_chains_in_scope(expr, &mut ctx);
    // Phase 2: cluster channelization.  Walks the rewritten tree,
    // processes `let d = Defer in …` clusters, extracting feeds and
    // building each defer's channel.  Defer-mediating function
    // bindings are re-registered here so the smart cluster walker
    // (`extract_for_defer`) can match `Apply(Var(d), Var(g))` and
    // `Apply(Var(d), Apply(arg, Var(f)))` forms produced by Phase 1.
    let rewritten = desugar(rewritten, &mut ctx)?;
    let rewritten = drop_expr_stmts(rewritten);
    assert_no_defer_residue(&rewritten)?;
    Ok(rewritten)
}

/// Collapse every `ExprStmt(e, b)` to `b`, recursing structurally.
///
/// Safe to do after the main desugar walk: every remaining `e` is pure
/// (its `Feed`/`Define` sites have been extracted, leaving `Unit`
/// residue), so dropping it is value-preserving.
fn drop_expr_stmts(expr: Expr) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let new_node = match node {
        TypedExprNode::ExprStmt { body, .. } => return drop_expr_stmts(*body),
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => TypedExprNode::Let {
            binding,
            bound_expr: Box::new(drop_expr_stmts(*bound_expr)),
            body: Box::new(drop_expr_stmts(*body)),
        },
        TypedExprNode::Apply { function, argument } => TypedExprNode::Apply {
            function: Box::new(drop_expr_stmts(*function)),
            argument: Box::new(drop_expr_stmts(*argument)),
        },
        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(drop_expr_stmts(*left)),
            op,
            right: Box::new(drop_expr_stmts(*right)),
        },
        TypedExprNode::UnaryOp(op, inner) => {
            TypedExprNode::UnaryOp(op, Box::new(drop_expr_stmts(*inner)))
        }
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => TypedExprNode::Lambda {
            param,
            body: Box::new(drop_expr_stmts(*body)),
            refinement,
        },
        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(drop_expr_stmts(*input)),
            kind,
        },
        TypedExprNode::Tuple(elts) => {
            TypedExprNode::Tuple(elts.into_iter().map(drop_expr_stmts).collect())
        }
        TypedExprNode::List(elts) => {
            TypedExprNode::List(elts.into_iter().map(drop_expr_stmts).collect())
        }
        TypedExprNode::Compose(elts) => {
            TypedExprNode::Compose(elts.into_iter().map(drop_expr_stmts).collect())
        }
        TypedExprNode::CollectionUnion(elts) => {
            TypedExprNode::CollectionUnion(elts.into_iter().map(drop_expr_stmts).collect())
        }
        TypedExprNode::Record(fields) => TypedExprNode::Record(
            fields
                .into_iter()
                .map(|(n, e)| (n, drop_expr_stmts(e)))
                .collect(),
        ),
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => TypedExprNode::Case {
            scrutinee: scrutinee.map(|s| Box::new(drop_expr_stmts(*s))),
            branches: branches
                .into_iter()
                .map(|b| Branch {
                    pattern: b.pattern,
                    guard: drop_expr_stmts(b.guard),
                    body: drop_expr_stmts(b.body),
                })
                .collect(),
        },
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => TypedExprNode::Loop {
            params,
            init_args: init_args.into_iter().map(drop_expr_stmts).collect(),
            source: Box::new(drop_expr_stmts(*source)),
            loop_body: Box::new(drop_expr_stmts(*loop_body)),
        },
        // Feed/Define get caught by assert_no_defer_residue downstream.
        node @ (TypedExprNode::Feed { .. }
        | TypedExprNode::Define { .. }
        | TypedExprNode::Defer
        | TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)) => node,
        TypedExprNode::Error => crate::unexpected_error_node!(),
        TypedExprNode::VariantCtor { .. } => {
            unreachable!("desugar_defers: VariantCtor not yet emitted by lowering")
        }
    };
    TypedExpr {
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Confirm that no `Defer`/`Feed`/`Define` nodes remain after desugar.
fn assert_no_defer_residue(expr: &Expr) -> Result<(), DeferError> {
    match &expr.node {
        TypedExprNode::Defer => Err(DeferError::UnboundDeferHandle("<defer>".into())),
        TypedExprNode::Feed { name, .. } | TypedExprNode::Define { name, .. } => {
            Err(DeferError::UnboundDeferHandle(name.clone()))
        }
        TypedExprNode::Let {
            bound_expr, body, ..
        } => {
            assert_no_defer_residue(bound_expr)?;
            assert_no_defer_residue(body)
        }
        TypedExprNode::Apply { function, argument } => {
            assert_no_defer_residue(function)?;
            assert_no_defer_residue(argument)
        }
        TypedExprNode::BinOp { left, right, .. } => {
            assert_no_defer_residue(left)?;
            assert_no_defer_residue(right)
        }
        TypedExprNode::UnaryOp(_, inner) | TypedExprNode::Aggregate { input: inner, .. } => {
            assert_no_defer_residue(inner)
        }
        TypedExprNode::Lambda { body, .. } => assert_no_defer_residue(body),
        TypedExprNode::Tuple(elts)
        | TypedExprNode::List(elts)
        | TypedExprNode::Compose(elts)
        | TypedExprNode::CollectionUnion(elts) => elts.iter().try_for_each(assert_no_defer_residue),
        TypedExprNode::Record(fields) => fields
            .iter()
            .try_for_each(|(_, e)| assert_no_defer_residue(e)),
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                assert_no_defer_residue(s)?;
            }
            branches.iter().try_for_each(|b| {
                assert_no_defer_residue(&b.guard)?;
                assert_no_defer_residue(&b.body)
            })
        }
        TypedExprNode::Loop {
            init_args,
            source,
            loop_body,
            ..
        } => {
            init_args.iter().try_for_each(assert_no_defer_residue)?;
            assert_no_defer_residue(source)?;
            assert_no_defer_residue(loop_body)
        }
        TypedExprNode::ExprStmt { expr, body } => {
            assert_no_defer_residue(expr)?;
            assert_no_defer_residue(body)
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_) => Ok(()),
        TypedExprNode::Error => crate::unexpected_error_node!(),
        TypedExprNode::VariantCtor { .. } => {
            unreachable!("desugar_defers: VariantCtor not yet emitted by lowering")
        }
    }
}

/// Recursively walk `expr`, looking for `let d = Defer in body` bindings.
///
/// When found, processes the binding via [`channelize_defer`] (feed path) or
/// inlines the define value directly (define path).  All other nodes are
/// recursed into structurally.
fn desugar(expr: Expr, ctx: &mut DesugarCtx) -> Result<Expr, DeferError> {
    if matches!(expr.node, TypedExprNode::Error) {
        crate::unexpected_error_node!();
    }
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } if matches!(bound_expr.node, TypedExprNode::Defer) => {
            // Collect the entire cluster of consecutive `let d_i = Defer`
            // bindings so they can be channelized together with
            // topological ordering — cross-defer channel references like
            // `define(x, y)` work in either direction only when the
            // emitted let-chain orders bindings by their data dependencies.
            //
            // Stripping one defer at a time and stacking the bindings in
            // processing order breaks for at least one of `x ≪= y; y ≪=
            // [0,1]` (where x depends on y) or `x ≪= [0,1]; y ≪= x`
            // (where y depends on x) — the wrap site doesn't know which.
            let mut defer_names = vec![binding.name];
            let mut current_body = *body;
            loop {
                match current_body.node {
                    TypedExprNode::Let {
                        binding: b,
                        bound_expr: be,
                        body: inner,
                    } if matches!(be.node, TypedExprNode::Defer) => {
                        defer_names.push(b.name);
                        current_body = *inner;
                    }
                    other => {
                        current_body = TypedExpr {
                            node: other,
                            ty: current_body.ty,
                            user_annotation: current_body.user_annotation,
                        };
                        break;
                    }
                }
            }
            // Recurse into the body first to handle any nested
            // non-clustered defers (inner `let d = Defer in ...`
            // separated from this cluster by other lets).
            let body_rewritten = desugar(current_body, ctx)?;
            channelize_cluster(&defer_names, body_rewritten, ctx)
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // Defer-mediating UDFs: register the function in
            // [`DesugarCtx::functions`] so the chain rewriter +
            // smart cluster walker (in [`extract_for_defer`]) can
            // handle calls to it without leaving copies of the body
            // in the final AST.  See `src/ccl/design-desugar-defers.md`
            // for the mechanism + known gaps (notably the higher-order
            // use case and the `count_free`-based binding drop).
            //
            // For [`LambdaClass::DeferIntroducing`] we first float
            // the internal `Defer` into a new lambda param, so
            // calls take the floated defer as a second arg.  The
            // chain rewriter wraps direct call sites accordingly.
            //
            // After registering and rewriting the body, the
            // function binding is dropped because all direct calls
            // have been replaced with `Var(fresh_defer)` by the
            // rewriter + smart walker — leaving `f` unreferenced.
            if matches!(&bound_expr.node, TypedExprNode::Lambda { .. }) {
                let class = classify_lambda(&bound_expr);
                if class != LambdaClass::Plain {
                    // Phase 1 already floated DI lambdas during chain
                    // rewriting, so the lambda in our tree is already
                    // in post-float shape.  Defensive `unwrap_or_else`
                    // covers the case where Phase 1 missed a float
                    // (e.g. unusual DI shape) — `float_defer_in_lambda`
                    // returns None on already-floated input, so this
                    // is a no-op on the common path.
                    let floated_lambda = if class == LambdaClass::DeferIntroducing {
                        float_defer_in_lambda((*bound_expr).clone())
                            .unwrap_or_else(|| (*bound_expr).clone())
                    } else {
                        (*bound_expr).clone()
                    };
                    // Body rewrite: replace the lambda's body with a
                    // `Record({to_<target_1>: …, …})` of per-target
                    // contributions.  The function now returns
                    // contributions instead of its defer-handle param;
                    // call sites project the relevant field.  See
                    // `src/ccl/design-desugar-defers.md` for the full
                    // mechanism.
                    let rewritten =
                        rewrite_lambda_to_return_contributions(floated_lambda, class, ctx)?;
                    let rewritten_lambda = rewritten.lambda.clone();
                    let info = FunctionInfo {
                        class,
                        lambda: rewritten.lambda,
                        feed_targets: rewritten.targets,
                        primary_target: rewritten.primary_target,
                    };
                    let prev = ctx.register_function(binding.name.clone(), info);
                    let desugared_body = desugar(*body, ctx)?;
                    ctx.unregister_function(&binding.name, prev);
                    // Drop the binding if `f` is unreferenced.  In the
                    // return-value design call sites add the
                    // statically-projected contribution directly to
                    // feeds (not via `Var(f)`), so direct-call-only
                    // functions typically end up unreferenced and get
                    // dropped here.  Functions referenced indirectly
                    // (passed to `map`, aliased, etc.) survive — that
                    // path is a known gap (see design doc).
                    if count_free(&binding.name, &desugared_body) == 0 {
                        return Ok(desugared_body);
                    }
                    return Ok(TypedExpr {
                        node: TypedExprNode::Let {
                            binding,
                            bound_expr: Box::new(rewritten_lambda),
                            body: Box::new(desugared_body),
                        },
                        ty,
                        user_annotation,
                    });
                }
            }
            // Defer-returning let-lift: `let y = (… let x = Defer in
            // body_x) in body_y` where body_x is defer-returning (ends
            // in `Var(x)`) merges the inner and outer defer scopes
            // into `let y = Defer in body_y` — the inner `x` is renamed
            // to `y` so any `Feed("x", …)` becomes `Feed("y", …)` and
            // the surrounding cluster channelization picks them up.
            //
            // This pattern arises from UDF inlining of defer-returning
            // functions: `let y = f(arg)` where f's body is `let x =
            // Defer in x` inlines to `let y = (let x = Defer in x) in
            // body_y`, and the lift collapses the two scopes.
            if let Some(lifted) = try_lift_defer(&binding.name, &bound_expr, &body) {
                return desugar(lifted, ctx);
            }
            // Let-of-defer-returning-let collapse: `let y = (let z =
            // E in Var(z)) in body_y` is equivalent to `let z = E in
            // body_y[y → z]`.  Surfaces a deeper `Defer` (inside E)
            // so the outer try_lift_defer can fire on a subsequent
            // pass.  Triggered by nested UDF inlines whose ANF
            // introduced an intermediate alias.
            if let TypedExprNode::Let {
                binding: inner_binding,
                bound_expr: inner_be,
                body: inner_body,
            } = &bound_expr.node
                && is_defer_returning(inner_body, &inner_binding.name)
                && contains_defer(inner_be)
            {
                let inner_name = inner_binding.name.clone();
                let inner_be = (**inner_be).clone();
                let inner_body = (**inner_body).clone();
                // Replace the trailing Var(inner_name) inside inner_body
                // with the outer body_y, so the inner scope's contents
                // run *before* body_y (preserving execution order).
                let spliced = replace_result_var(inner_body, *body);
                // Rename inner_name → binding.name in the spliced body
                // so the inner defer is exposed under the outer let-y
                // name for subsequent passes.
                let renamed = pre_infer_substitute(spliced, &inner_name, &Expr::var(&binding.name));
                let collapsed = Expr::let_bind(binding.name.clone(), inner_be, renamed);
                return desugar(collapsed, ctx);
            }
            // Recurse first so any inner aliases / UDF-inlines get
            // resolved before we check this outer binding.
            let bound_expr = desugar(*bound_expr, ctx)?;
            let body = desugar(*body, ctx)?;
            // Alias inlining: `let y = Var(x) in body` becomes
            // `body[y → x]`.  Needed before defer channelization so
            // `Feed(y, …)` nodes (which really write to the upstream
            // defer `x`) are recognized.
            //
            // [`pre_infer_substitute`] renames the *target* string of
            // `Feed`/`Define` nodes when the replacement is a `Var`,
            // so `Feed("y", …)` becomes `Feed("x", …)` automatically.
            //
            // Only fires when:
            //   (1) the body contains a `Feed/Define` for this
            //       binding (so the alias is being used as a defer
            //       handle), AND
            //   (2) the body doesn't rebind the source variable (so
            //       the α-renaming is capture-safe).
            if let TypedExprNode::Var(source_name) = &bound_expr.node
                && contains_feed_or_define_for(&body, &binding.name)
                && !rebinds(&body, source_name)
            {
                let substituted = pre_infer_substitute(body, &binding.name, &bound_expr);
                return Ok(substituted);
            }
            Ok(TypedExpr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr: Box::new(bound_expr),
                    body: Box::new(body),
                },
                ty,
                user_annotation,
            })
        }
        // All other variants (Apply/BinOp/Lambda/Loop/…, leaves, and the
        // Feed/Define pass-through that gets caught by
        // [`assert_no_defer_residue`] if it survives) just recurse
        // structurally into every child.
        other => {
            let mut expr = TypedExpr {
                node: other,
                ty,
                user_annotation,
            };
            expr.try_map_children(|c| desugar(c, ctx))?;
            Ok(expr)
        }
    }
}

/// Process a cluster of consecutive `let d_i = Defer in …` bindings.
///
/// Walks `body` once per defer to extract its feeds/defines, then emits
/// the bindings at the body's terminal in *topological order* — a defer
/// whose channel value references another cluster defer is bound *after*
/// the referenced defer.  This makes both `x ≪= y; y ≪= [0, 1]` (x
/// depends on y) and `x ≪= [0, 1]; y ≪= x` (y depends on x) emit a
/// well-scoped let-chain without requiring letrec or substitution.
///
/// Each defer's channel is built using the same rules as
/// [`channelize_defer`]: a single feed passes through, multiple feeds
/// union via [`TypedExprNode::CollectionUnion`], a `Define` value is
/// used directly, and top-level scalar feeds are lifted to `Fun(Unit,
/// T)` via the `λ __unused → V` wrap inside `extract_for_defer`.
fn channelize_cluster(
    defer_names: &[String],
    body: Expr,
    ctx: &mut DesugarCtx,
) -> Result<Expr, DeferError> {
    // Extract feeds/defines for each defer.  `rewritten` accumulates the
    // body's Feed/Define replacements as we process each defer in turn.
    let mut channels: HashMap<String, Expr> = HashMap::new();
    let mut rewritten = body;
    for name in defer_names.iter().rev() {
        // Process innermost defer first so its feeds are picked up before
        // the outer defer's walk; the outer walk wouldn't see them anyway
        // since extract_for_defer matches by name.  Processing order is
        // not load-bearing here because each defer extracts only its own
        // feeds.
        let mut feeds = Vec::new();
        let mut define: Option<Expr> = None;
        rewritten = extract_for_defer(rewritten, name, &mut feeds, &mut define, false, ctx)?;
        let channel = match (feeds.is_empty(), define) {
            (true, None) => return Err(DeferError::NoFeedOrDefine(name.clone())),
            (true, Some(d)) => d,
            (false, None) => combine_feed_values(feeds),
            (false, Some(_)) => return Err(DeferError::FeedsAndDefinesMixed(name.clone())),
        };
        channels.insert(name.clone(), channel);
    }
    // Topologically order the bindings: a defer whose channel references
    // another cluster defer is bound after that defer.
    let order = topo_sort_cluster(defer_names, &channels)?;
    // Wrap the body's terminal with the cluster's let-chain in order —
    // first α-renaming any downstream Let-shadows of channel free
    // variables so the channels keep referring to the values they
    // captured at their original feed positions.
    let protected: HashSet<String> = compute_protected_set(&rewritten, &channels);
    Ok(rename_shadows_then_bind(
        rewritten, &order, channels, &protected, ctx,
    ))
}

/// Compute the set of variable names that channel expressions reference
/// and that are also free in `body` — i.e., names defined *outside*
/// `body` whose values channels were captured from.  Any `Let n = …`
/// inside `body` that rebinds such a name is a shadow that must be
/// α-renamed before the cluster wrap, otherwise channels would
/// silently read the rebound value instead of the captured one.
///
/// Channel-only free variables (e.g. `__acc_stream_N` bindings
/// introduced *inside* `body` by `lower_mutation_loop`) are excluded
/// because the channel's reference correctly resolves to the binding
/// inside `body`; renaming would break the link.
fn compute_protected_set(body: &Expr, channels: &HashMap<String, Expr>) -> HashSet<String> {
    let mut channel_fvs: HashSet<String> = HashSet::new();
    for c in channels.values() {
        collect_free_vars(c, &mut channel_fvs);
    }
    let mut body_fvs: HashSet<String> = HashSet::new();
    collect_free_vars(body, &mut body_fvs);
    channel_fvs.intersection(&body_fvs).cloned().collect()
}

/// Walk `expr` through `Let`/`ExprStmt` bodies to its terminal,
/// α-renaming any `Let n = E in inner` where `n ∈ protected_set` so
/// the inner shadowing is broken.  At the terminal, emit the cluster's
/// let-chain in topological order.
fn rename_shadows_then_bind(
    expr: Expr,
    order: &[String],
    channels: HashMap<String, Expr>,
    protected: &HashSet<String>,
    ctx: &mut DesugarCtx,
) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } if protected.contains(&binding.name) => {
            // Shadow: rename to a fresh name and α-substitute the body so
            // any inner references use the new name.  The bound_expr is
            // left alone — its references to `binding.name` (e.g.
            // `(__acc_stream_1 ≫ .step, x) ▷ last_or_default` where `x`
            // is the outer binding) resolve outward correctly.
            let fresh = ctx.fresh_shadow_rename(&binding.name);
            let new_body = pre_infer_substitute(*body, &binding.name, &Expr::var(&fresh));
            let new_binding = crate::ccl::TypedBinding {
                name: fresh,
                ty: binding.ty,
                user_annotation: binding.user_annotation,
            };
            TypedExpr {
                node: TypedExprNode::Let {
                    binding: new_binding,
                    bound_expr,
                    body: Box::new(rename_shadows_then_bind(
                        new_body, order, channels, protected, ctx,
                    )),
                },
                ty,
                user_annotation,
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // If this Let's `bound_expr` references any of the
            // cluster's binding names, emit the cluster's bindings
            // *here* (before this Let) rather than continuing down
            // to the body's terminal — otherwise the cluster binding
            // would be lexically after the reference and unbound at
            // its use site.
            //
            // Triggered most commonly when an *inner* cluster's
            // processing left a `let y = Var(x)` in the chain
            // (`y`'s channel was `Var(x)` of an outer defer) and the
            // outer cluster's wrap now needs to put `let x = …`
            // before that `let y`.  See `test_feed_and_define_operators`
            // cases 10–11 for the cross-cluster-references-through-
            // intervening-let pattern this targets.
            let references_cluster = order
                .iter()
                .any(|n| channels.contains_key(n) && count_free(n, &bound_expr) > 0);
            if references_cluster {
                let original_let = TypedExpr {
                    node: TypedExprNode::Let {
                        binding,
                        bound_expr,
                        body,
                    },
                    ty,
                    user_annotation,
                };
                return emit_cluster_then(original_let, order, channels);
            }
            TypedExpr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(rename_shadows_then_bind(
                        *body, order, channels, protected, ctx,
                    )),
                },
                ty,
                user_annotation,
            }
        }
        TypedExprNode::ExprStmt { expr: e, body } => TypedExpr {
            node: TypedExprNode::ExprStmt {
                expr: e,
                body: Box::new(rename_shadows_then_bind(
                    *body, order, channels, protected, ctx,
                )),
            },
            ty,
            user_annotation,
        },
        other => {
            let terminal = TypedExpr {
                node: other,
                ty,
                user_annotation,
            };
            emit_cluster_then(terminal, order, channels)
        }
    }
}

/// Capture the let-chain prefix of `expr` — a list of `(name,
/// bound_expr)` pairs representing each `Let` at the head of the
/// expression.  Stops at the first non-`Let` node.  Used by the
/// smart walker to wrap feeds extracted from a substituted body
/// with the lets they reference.
fn capture_let_chain_prefix(expr: &Expr) -> Vec<(String, Expr)> {
    let mut out = Vec::new();
    let mut current = expr;
    while let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &current.node
    {
        out.push((binding.name.clone(), (**bound_expr).clone()));
        current = body;
    }
    out
}

/// Wrap `inner` with a sequence of `let name_i = bound_expr_i in …`
/// from `prefix` (outermost first), so the let-chain scopes `inner`.
fn wrap_with_let_prefix(prefix: &[(String, Expr)], inner: Expr) -> Expr {
    let mut result = inner;
    for (name, bound) in prefix.iter().rev() {
        result = Expr::let_bind(name.clone(), bound.clone(), result);
    }
    result
}

/// Wrap `inner` with the cluster's `let n_i = channel_i in …` bindings
/// in topological order (so dependencies are bound before dependents).
fn emit_cluster_then(inner: Expr, order: &[String], mut channels: HashMap<String, Expr>) -> Expr {
    let mut result = inner;
    for name in order.iter().rev() {
        if let Some(channel) = channels.remove(name) {
            result = Expr::let_bind(name.clone(), channel, result);
        }
    }
    result
}

/// Collect every free `Var` name in `expr` into `out`, respecting
/// shadowing by enclosing `Let`/`Lambda` bindings on the term spine.
///
/// Also walks references hidden in **type positions**:
/// - `expr.ty` refinement predicates
/// - `expr.user_annotation` refinement predicates (set by
///   [`extract_for_defer`]'s filter-feed rewrite)
/// - `Lambda::refinement` predicates
///
/// Without these, a channel that references an outer let-binding only
/// through a refinement predicate would be missed by
/// [`compute_protected_set`], leaving a downstream `Let` shadow
/// undetected and the channel silently reading the wrong value at the
/// cluster bind site.
///
/// Shadowing inside type-position predicates is intentionally not
/// tracked — the goal here is "does the channel reference this name
/// anywhere," not "does the name occur free per lexical-scope
/// rules."  This matches [`crate::ccl::ccl_utils::count_free`]'s
/// behaviour on type refinements.
fn collect_free_vars(expr: &Expr, out: &mut HashSet<String>) {
    fn rec(expr: &Expr, bound: &mut Vec<String>, out: &mut HashSet<String>) {
        // Type-position predicates on this node (`expr.ty` and any
        // user-supplied annotation) are visited unconditionally — they
        // belong to the *outer* scope, and shadowing inside them isn't
        // tracked here.
        collect_free_vars_in_type(&expr.ty, out);
        if let Some(ann) = &expr.user_annotation {
            collect_free_vars_in_type(ann, out);
        }
        match &expr.node {
            TypedExprNode::Var(name) => {
                if !bound.iter().any(|b| b == name) {
                    out.insert(name.clone());
                }
            }
            // Binder variants need scope-aware recursion: positions
            // outside the binder (bound_expr, init_args, source, Lambda
            // refinement) see the outer scope; positions inside see the
            // binder's name added to `bound`.
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => {
                rec(bound_expr, bound, out);
                bound.push(binding.name.clone());
                rec(body, bound, out);
                bound.pop();
            }
            TypedExprNode::Lambda {
                param,
                body,
                refinement,
            } => {
                if let Some(r) = refinement {
                    // The Lambda's own refinement lives in the *outer*
                    // scope (before the param is bound), so visit it
                    // before pushing `param.name`.
                    let RefinementKind::Predicate(pred_rc) = &r.kind;
                    if let Ok(pred) = pred_rc.try_borrow() {
                        rec(&pred, bound, out);
                    }
                }
                bound.push(param.name.clone());
                rec(body, bound, out);
                bound.pop();
            }
            TypedExprNode::Loop {
                params,
                init_args,
                source,
                loop_body,
                ..
            } => {
                for e in init_args {
                    rec(e, bound, out);
                }
                rec(source, bound, out);
                for p in params {
                    bound.push(p.name.clone());
                }
                rec(loop_body, bound, out);
                for _ in params {
                    bound.pop();
                }
            }
            _ => expr.walk_children(|c| rec(c, bound, out)),
        }
    }
    let mut bound = Vec::new();
    rec(expr, &mut bound, out);
}

/// Walk `ty` for any [`RefinementKind::Predicate`] expressions and
/// collect their free variables into `out`.  Structural recursion via
/// [`Type::walk_children`] so every compound type variant (`Fun`,
/// `Tuple`, `Union`, `Record`, `PartialTuple`, `PartialRecord`) is
/// covered uniformly.
///
/// `try_borrow().ok()` silently treats an actively-mutated predicate
/// as "no references"; callers run between passes when no predicate
/// is being walked elsewhere, so the under-count is safe in practice.
fn collect_free_vars_in_type(ty: &Type, out: &mut HashSet<String>) {
    if let Type::Refinement(_, refinement) = ty {
        let RefinementKind::Predicate(pred_rc) = &refinement.kind;
        if let Ok(pred) = pred_rc.try_borrow() {
            // Refinement predicates are themselves CCL expressions;
            // recurse into them through `collect_free_vars` so their
            // own type-position predicates and shadowing are
            // handled consistently.
            collect_free_vars(&pred, out);
        }
    }
    ty.walk_children(|child| collect_free_vars_in_type(child, out));
}

/// Return the cluster defers in an order such that, for any defer `d`
/// whose channel references another cluster defer `d'`, `d'` appears
/// *earlier* in the returned vector (so it is bound first in the
/// emitted let-chain).
///
/// Uses [`count_free`] to detect references.  Detects cycles (mutually
/// recursive defer references) and reports them as a clear panic since
/// the resolution would require letrec semantics that CCL doesn't yet
/// support.
fn topo_sort_cluster(
    defer_names: &[String],
    channels: &HashMap<String, Expr>,
) -> Result<Vec<String>, DeferError> {
    let names: Vec<String> = defer_names.to_vec();
    // Build dependency edges: d_i depends on d_j if d_i's channel references Var(d_j).
    let mut deps: HashMap<&str, Vec<&str>> = HashMap::new();
    for d in &names {
        let mut d_deps = Vec::new();
        if let Some(channel) = channels.get(d) {
            for other in &names {
                if other != d && count_free(other, channel) > 0 {
                    d_deps.push(other.as_str());
                }
            }
        }
        deps.insert(d.as_str(), d_deps);
    }
    let mut sorted: Vec<String> = Vec::with_capacity(names.len());
    let mut visited: HashSet<String> = HashSet::new();
    let mut visiting: HashSet<String> = HashSet::new();
    fn visit(
        name: &str,
        deps: &HashMap<&str, Vec<&str>>,
        visited: &mut HashSet<String>,
        visiting: &mut HashSet<String>,
        sorted: &mut Vec<String>,
    ) -> Result<(), DeferError> {
        if visited.contains(name) {
            return Ok(());
        }
        if visiting.contains(name) {
            // Cycle — currently unsupported.
            return Err(DeferError::MutuallyRecursiveCycle(name.to_string()));
        }
        visiting.insert(name.to_string());
        if let Some(dep_list) = deps.get(name) {
            for dep in dep_list {
                visit(dep, deps, visited, visiting, sorted)?;
            }
        }
        visiting.remove(name);
        visited.insert(name.to_string());
        sorted.push(name.to_string());
        Ok(())
    }
    for d in &names {
        visit(d, &deps, &mut visited, &mut visiting, &mut sorted)?;
    }
    Ok(sorted)
}

/// Combine multiple feed values into a single channel expression.
///
/// Walk `expr` collecting every defer-target name referenced by a
/// `Feed`/`Define` node, respecting `Let`/`Lambda` shadowing on the
/// term spine.  Used to identify the full set of defers a function's
/// body feeds (param + closure-captured) before rewriting the body to
/// a per-target contributions Record.
fn collect_feed_target_names(expr: &Expr) -> Vec<String> {
    fn rec(expr: &Expr, bound: &mut Vec<String>, out: &mut HashSet<String>) {
        match &expr.node {
            TypedExprNode::Feed { name, value } | TypedExprNode::Define { name, value } => {
                if !bound.iter().any(|b| b == name) {
                    out.insert(name.clone());
                }
                rec(value, bound, out);
            }
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => {
                rec(bound_expr, bound, out);
                bound.push(binding.name.clone());
                rec(body, bound, out);
                bound.pop();
            }
            TypedExprNode::Lambda { param, body, .. } => {
                bound.push(param.name.clone());
                rec(body, bound, out);
                bound.pop();
            }
            TypedExprNode::Apply { function, argument } => {
                rec(function, bound, out);
                rec(argument, bound, out);
            }
            TypedExprNode::BinOp { left, right, .. } => {
                rec(left, bound, out);
                rec(right, bound, out);
            }
            TypedExprNode::UnaryOp(_, inner) | TypedExprNode::Aggregate { input: inner, .. } => {
                rec(inner, bound, out);
            }
            TypedExprNode::Tuple(elts)
            | TypedExprNode::List(elts)
            | TypedExprNode::Compose(elts)
            | TypedExprNode::CollectionUnion(elts) => {
                for e in elts {
                    rec(e, bound, out);
                }
            }
            TypedExprNode::Record(fields) => {
                for (_, e) in fields {
                    rec(e, bound, out);
                }
            }
            TypedExprNode::Case {
                scrutinee,
                branches,
            } => {
                if let Some(s) = scrutinee {
                    rec(s, bound, out);
                }
                for b in branches {
                    // A structural pattern binds its payload name over the
                    // branch's guard and body.
                    let pushed = if let Some(p) = &b.pattern {
                        bound.push(p.binding.name.clone());
                        true
                    } else {
                        false
                    };
                    rec(&b.guard, bound, out);
                    rec(&b.body, bound, out);
                    if pushed {
                        bound.pop();
                    }
                }
            }
            TypedExprNode::Loop {
                params,
                init_args,
                source,
                loop_body,
                ..
            } => {
                for e in init_args {
                    rec(e, bound, out);
                }
                rec(source, bound, out);
                for p in params {
                    bound.push(p.name.clone());
                }
                rec(loop_body, bound, out);
                for _ in params {
                    bound.pop();
                }
            }
            TypedExprNode::ExprStmt { expr: e, body } => {
                rec(e, bound, out);
                rec(body, bound, out);
            }
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::Defer => {}
            TypedExprNode::Error => crate::unexpected_error_node!(),
            TypedExprNode::VariantCtor { .. } => {
                unreachable!("desugar_defers: VariantCtor not yet emitted by lowering")
            }
        }
    }
    let mut targets: HashSet<String> = HashSet::new();
    rec(expr, &mut Vec::new(), &mut targets);
    let mut sorted: Vec<String> = targets.into_iter().collect();
    // Deterministic order so generated field names compare reliably.
    sorted.sort();
    sorted
}

/// Output of [`rewrite_lambda_to_return_contributions`].
struct RewrittenFunction {
    /// The lambda with body replaced by the contributions Record.
    lambda: Expr,
    /// All defer targets the body feeds, primary target first.
    targets: Vec<String>,
    /// Primary target — the lambda-param-side defer name.  For PaT,
    /// this is the lambda's only param; for DI, the floated inner
    /// param.  Other entries in `targets` are closure-captured
    /// defers whose names cross the function boundary unchanged.
    primary_target: String,
}

/// Rewrite a defer-mediating lambda's body to return a `Record` whose
/// fields carry the contributions to each defer the body feeds.
///
/// For `ParamAsTarget` (`λp → body`): walks `body` once per target.
/// For `DeferIntroducing` (post-float, `λp → λ__floated → body`):
/// walks the inner lambda's `body` once per target.
///
/// The rewritten body discards the original terminal value
/// (typically `Var(target)`) and yields the contributions Record
/// instead.  At call sites, the smart walker emits an
/// `Apply(call_expr, Proj("to_<target>"))` to pull each defer's
/// contribution out for the surrounding cluster.
fn rewrite_lambda_to_return_contributions(
    lambda: Expr,
    class: LambdaClass,
    ctx: &mut DesugarCtx,
) -> Result<RewrittenFunction, DeferError> {
    // VarBody (`λp → Var(name)`) is a pure α-rename — no feeds in the
    // body, no rewrite needed.  Pass the lambda through unchanged
    // with an empty target set.
    if class == LambdaClass::VarBody {
        return Ok(RewrittenFunction {
            lambda,
            targets: Vec::new(),
            primary_target: String::new(),
        });
    }
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = lambda;
    match (class, node) {
        (
            LambdaClass::ParamAsTarget,
            TypedExprNode::Lambda {
                param,
                body,
                refinement,
            },
        ) => {
            let primary_target = param.name.clone();
            let cr = build_contributions_record(*body, &primary_target, ctx)?;
            Ok(RewrittenFunction {
                lambda: TypedExpr {
                    node: TypedExprNode::Lambda {
                        param,
                        body: Box::new(cr.body),
                        refinement,
                    },
                    ty,
                    user_annotation,
                },
                targets: cr.targets,
                primary_target,
            })
        }
        (
            LambdaClass::DeferIntroducing,
            TypedExprNode::Lambda {
                param: outer_param,
                body: outer_body,
                refinement: outer_refinement,
            },
        ) => {
            let TypedExpr {
                node: outer_body_node,
                ty: outer_body_ty,
                user_annotation: outer_body_ann,
            } = *outer_body;
            let TypedExprNode::Lambda {
                param: inner_param,
                body: inner_body,
                refinement: inner_refinement,
            } = outer_body_node
            else {
                unreachable!("DI post-float guarantees outer body is a Lambda");
            };
            let primary_target = inner_param.name.clone();
            let cr = build_contributions_record(*inner_body, &primary_target, ctx)?;
            let new_inner = TypedExpr {
                node: TypedExprNode::Lambda {
                    param: inner_param,
                    body: Box::new(cr.body),
                    refinement: inner_refinement,
                },
                ty: outer_body_ty,
                user_annotation: outer_body_ann,
            };
            Ok(RewrittenFunction {
                lambda: TypedExpr {
                    node: TypedExprNode::Lambda {
                        param: outer_param,
                        body: Box::new(new_inner),
                        refinement: outer_refinement,
                    },
                    ty,
                    user_annotation,
                },
                targets: cr.targets,
                primary_target,
            })
        }
        _ => unreachable!(
            "rewrite_lambda_to_return_contributions called on non-defer-mediating lambda"
        ),
    }
}

/// Result of [`build_contributions_record`].
struct ContributionsRecord {
    /// The lambda body's new value — typically a `Record({to_<target>:
    /// V, …})` wrapped in any let-chain prefix the original body had.
    /// This is what the lambda returns at runtime; downstream passes
    /// see and typecheck this expression normally.
    body: Expr,
    /// Targets in deterministic order, primary target first.
    targets: Vec<String>,
}

/// Walk `body` per target in `collect_feed_target_names(body)`,
/// extract feeds for each, and build a `Record` whose `to_<target>`
/// field carries the combined contributions.
///
/// `primary_target` is placed first in the returned target list so
/// the caller can identify it for call-site projection mapping.
fn build_contributions_record(
    body: Expr,
    primary_target: &str,
    ctx: &mut DesugarCtx,
) -> Result<ContributionsRecord, DeferError> {
    let raw_targets = collect_feed_target_names(&body);
    // Reorder so the primary target is first.
    let mut targets: Vec<String> = Vec::with_capacity(raw_targets.len().max(1));
    if raw_targets.iter().any(|t| t == primary_target) {
        targets.push(primary_target.to_string());
    }
    for t in &raw_targets {
        if t != primary_target {
            targets.push(t.clone());
        }
    }
    // If the body has no feeds at all, the function would have been
    // classified as `Plain` and we wouldn't be rewriting it.  But the
    // classifier handles `DeferIntroducing` via a `contains_defer`
    // check (a defer with no feeds is still DI), so emit the empty
    // record gracefully here.
    if targets.is_empty() {
        return Ok(ContributionsRecord {
            body: Expr::new(TypedExprNode::Record(Vec::new())),
            targets,
        });
    }

    // Walk the body once per target, accumulating each target's feeds
    // into a Record field.  Each pass operates on the body modified
    // by previous passes (Feed nodes for earlier targets replaced by
    // `Unit`); feeds for other targets are passed through unchanged.
    let mut current_body = body;
    let mut fields: Vec<(String, Expr)> = Vec::with_capacity(targets.len());
    for target in &targets {
        let mut feeds: Vec<Expr> = Vec::new();
        let mut define: Option<Expr> = None;
        current_body =
            extract_for_defer(current_body, target, &mut feeds, &mut define, false, ctx)?;
        let contribution = match (feeds.is_empty(), define) {
            (true, None) => continue, // target was collected but no feeds for it — skip.
            (true, Some(d)) => d,
            (false, None) => combine_feed_values(feeds),
            (false, Some(_)) => return Err(DeferError::FeedsAndDefinesMixed(target.clone())),
        };
        fields.push((channel_field_name(target), contribution));
    }
    // The stripped body may carry a let-chain prefix (typically `let
    // __acc_stream_N = Loop {…} in …` from generator-with-mutation
    // lowering; sometimes plain user `let n = 0`s) whose bindings the
    // contributions reference.  We're discarding `current_body` —
    // the function's new body is the contributions Record — so wrap
    // the Record with the surrounding lets so any
    // `Var(__acc_stream_N)` inside the contributions stays bound when
    // the lambda is evaluated.
    let prefix = capture_let_chain_prefix(&current_body);
    let record = Expr::new(TypedExprNode::Record(fields));
    let body = if prefix.is_empty() {
        record
    } else {
        wrap_with_let_prefix(&prefix, record)
    };
    Ok(ContributionsRecord { body, targets })
}

/// A single feed value passes through unchanged.  Multiple feed values
/// are merged via [`TypedExprNode::CollectionUnion`] — the dedicated
/// N-ary collection-union node — which compiles to a `UnionOperator`
/// downstream.
fn combine_feed_values(mut feeds: Vec<Expr>) -> Expr {
    debug_assert!(!feeds.is_empty());
    if feeds.len() == 1 {
        return feeds.pop().unwrap();
    }
    Expr::collection_union(feeds)
}

/// Synthesize the per-target Feed contributions for a defer-mediating
/// UDF call.
///
/// In the return-value design, each defer-mediating function has been
/// rewritten at its definition site to return
/// `Record({to_<target_1>: contribs_1, …})` (see
/// [`rewrite_lambda_to_return_contributions`]).  At each call site, the
/// runtime value of the call is this Record; each target's
/// contribution is the call's projection of the corresponding
/// `to_<target>` field.
///
/// This helper takes the original call expression and the function's
/// recorded targets, and:
/// - pushes the projection for **our** cluster's contribution
///   (`call ▷ Proj("to_<current_target>")`) onto `feeds`, and
/// - returns an `ExprStmt` chain that emits
///   `Feed(<other_target>, call ▷ Proj("to_<other_target>"))` nodes
///   at the call site for any *other* targets (closure-captured
///   defers).  Those Feed nodes get picked up by other clusters'
///   standard walks when they process their own defers.  The chain's
///   final value is `Var(defer_name)` — the call's reduction.
///
/// **`Var(defer_name)` substitution.**  The chain rewriter wrapped DI
/// calls with `Var(<defer>)` as the second argument so the curried
/// `λp → λ__floated → body` would fully reduce.  In the return-value
/// design `__floated` is unused inside the rewritten body (the Record
/// fields are extracted from Feeds, which now live in the Record
/// itself, not at the wrap site).  Keeping the `Var(<defer>)` in the
/// projection expression would create a self-referential
/// `let <defer> = … Var(<defer>) … in …` binding (the channel
/// expression references the very binding it constructs), which CCL
/// doesn't support without letrec.  We substitute `Var(<defer>)` with
/// `Lit::Unit` inside the call expression before projecting, since
/// the rewritten body discards the second argument anyway.  Same fix
/// for PaT: the param's value is unused after rewrite, so the call's
/// `Var(<defer>)` argument is replaced with `Lit::Unit`.
///
/// `current_target` is the function-side name (i.e. one of
/// `finfo.feed_targets`) that maps to the current cluster.  For PaT
/// calls this is `finfo.primary_target`; for closure-captured calls
/// it's the captured defer name.
fn smart_walk_synthesize_call_contributions(
    call_expr: &Expr,
    finfo: &FunctionInfo,
    current_target: &str,
    defer_name: &str,
    feeds: &mut Vec<Expr>,
) -> Expr {
    // The call's `ty` / `user_annotation` are the original Apply's
    // type slots — i.e. the defer-handle type (`Fun(D, T)`) that the
    // call originally produced.  We reuse them for the residue
    // `Var(defer_name)`, since the cluster's defer-handle binding
    // carries the same type.
    let residue_var = || TypedExpr {
        node: TypedExprNode::Var(defer_name.to_string()),
        ty: call_expr.ty.clone(),
        user_annotation: call_expr.user_annotation.clone(),
    };
    // Defer-returning-no-feeds case: the function introduces a defer
    // and returns it without adding any contributions of its own
    // (`def f(n): x = defer(); x`).  Its rewritten body is an empty
    // `Record({})`, which can't be projected from.  Skip both the
    // primary projection and any closure-capture synthesis — the
    // call's contribution is empty, and the surrounding cluster
    // collects feeds from outside the function (typical: `let y =
    // f(10) in for i in src: y << i`).
    if finfo.feed_targets.is_empty() {
        return residue_var();
    }
    // Replace `Var(defer_name)` with `Lit::Unit` in the call
    // expression to avoid self-referential channel bindings.  See the
    // doc comment for the full rationale.
    let neutered_call = pre_infer_substitute(call_expr.clone(), defer_name, &Expr::lit(Lit::Unit));
    // Project the current target's field into `feeds`.  We project
    // only if the function actually has a `to_<current_target>` field
    // (closure-captured targets may exist without the function
    // contributing to the primary target itself).
    if finfo.feed_targets.iter().any(|t| t == current_target) {
        let projection = Expr::apply(
            neutered_call.clone(),
            Expr::proj_field(channel_field_name(current_target)),
        );
        feeds.push(projection);
    }
    // For every other target the function feeds, synthesize a Feed
    // node at the call site so other clusters pick up their
    // contributions.  Closure-captured defer names are stable across
    // the function boundary; the primary-target's caller-side name is
    // the current cluster's `defer_name`, but we only synthesize for
    // *other* targets here.
    let mut result = residue_var();
    for target in &finfo.feed_targets {
        if target == current_target {
            continue;
        }
        // For non-current targets, the caller-side defer name is the
        // function-side target name itself (closure capture — the
        // function references this name lexically, so it resolves to
        // the surrounding scope at the call site).
        let other_projection = Expr::apply(
            neutered_call.clone(),
            Expr::proj_field(channel_field_name(target)),
        );
        result = Expr::expr_stmt(Expr::feed(target.clone(), other_projection), result);
    }
    result
}

/// Try to handle `Apply { argument, function: Var(g) }` as a direct
/// [`LambdaClass::ParamAsTarget`] call whose primary defer maps to
/// our cluster: `argument == Var(defer_name)`.
///
/// On match: projects the function's `to_<primary_target>` field as
/// our cluster's contribution, synthesizes Feed nodes at the call
/// site for any closure-captured defers the function also feeds, and
/// returns `Var(defer_name)` (PaT's reduction — returns the param).
///
/// Returns `None` on no match.
///
/// FIXME(desugar_defers-prototype): part of the unresolved
/// Record-of-`to_<target>`-fields vs. body-substitution design
/// question for defer-mediating UDFs.  See the umbrella entry in
/// `docs/plan.md` ("Tech Debt — `desugar_defers` prototype").
fn try_smart_walk_pat(
    function: &Expr,
    argument: &Expr,
    outer_ty: &Type,
    outer_ann: &Option<Type>,
    defer_name: &str,
    feeds: &mut Vec<Expr>,
    ctx: &DesugarCtx,
) -> Option<Expr> {
    let TypedExprNode::Var(fname) = &function.node else {
        return None;
    };
    let finfo = ctx.lookup_function(fname)?;
    if finfo.class != LambdaClass::ParamAsTarget {
        return None;
    }
    if !matches!(&argument.node, TypedExprNode::Var(n) if n == defer_name) {
        return None;
    }
    // Build the call expression (the original `Apply { function,
    // argument }` reassembled).  Its runtime value is the function's
    // contributions Record; projections of `to_<target>` fields give
    // each target's contribution.
    let call_expr = TypedExpr {
        node: TypedExprNode::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument.clone()),
        },
        ty: outer_ty.clone(),
        user_annotation: outer_ann.clone(),
    };
    Some(smart_walk_synthesize_call_contributions(
        &call_expr,
        finfo,
        &finfo.primary_target,
        defer_name,
        feeds,
    ))
}

/// Try to handle the [`LambdaClass::DeferIntroducing`] post-float,
/// post-wrap call shape:
///   `Apply { function: Apply { function: Var(f), argument: outer_arg },
///            argument: Var(defer_name) }`
///
/// (The chain rewriter wraps every DI call with the missing
/// `Var(<defer>)` second argument to supply the floated defer-handle
/// param — see [`wrap_di_calls_in_chain`].)
///
/// On match: projects the function's `to_<primary_target>` field as
/// our cluster's contribution, synthesizes closure-capture Feeds for
/// other targets, and returns `Var(defer_name)` (the call's reduction
/// — the floated defer).
///
/// Returns `None` on no match.
///
/// FIXME(desugar_defers-prototype): part of the unresolved
/// Record-of-`to_<target>`-fields vs. body-substitution design
/// question for defer-mediating UDFs.  See the umbrella entry in
/// `docs/plan.md` ("Tech Debt — `desugar_defers` prototype").
fn try_smart_walk_di(
    function: &Expr,
    argument: &Expr,
    outer_ty: &Type,
    outer_ann: &Option<Type>,
    defer_name: &str,
    feeds: &mut Vec<Expr>,
    ctx: &DesugarCtx,
) -> Option<Expr> {
    let TypedExprNode::Var(arg_name) = &argument.node else {
        return None;
    };
    if arg_name != defer_name {
        return None;
    }
    let TypedExprNode::Apply {
        function: inner_func,
        ..
    } = &function.node
    else {
        return None;
    };
    let TypedExprNode::Var(fname) = &inner_func.node else {
        return None;
    };
    let finfo = ctx.lookup_function(fname)?;
    if finfo.class != LambdaClass::DeferIntroducing {
        return None;
    }
    let call_expr = TypedExpr {
        node: TypedExprNode::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument.clone()),
        },
        ty: outer_ty.clone(),
        user_annotation: outer_ann.clone(),
    };
    Some(smart_walk_synthesize_call_contributions(
        &call_expr,
        finfo,
        &finfo.primary_target,
        defer_name,
        feeds,
    ))
}

/// Walk `expr` collecting `Feed`/`Define` nodes for `defer_name`.
///
/// - Every `Feed(defer_name, V)` is replaced with `Lit::Unit`, and `V` is
///   pushed into `feeds`.
/// - The (single) `Define(defer_name, V)` (if any) is recorded in `define`,
///   replaced with `Lit::Unit`.
/// - Other defers' Feed/Define nodes are left untouched (an outer pass will
///   handle them).
///
/// The walk respects shadowing: a nested `let defer_name = …` (binding the
/// same name) stops the search inside that binding's body.
///
/// `in_inner_scope` is `true` when the walk has crossed a [`TypedExprNode::Lambda`],
/// [`TypedExprNode::Loop`] (body), or [`TypedExprNode::Case`] branch boundary —
/// `Define` is disallowed in those contexts since the desugared binding
/// would need to escape the inner scope.
fn extract_for_defer(
    expr: Expr,
    defer_name: &str,
    feeds: &mut Vec<Expr>,
    define: &mut Option<Expr>,
    in_inner_scope: bool,
    ctx: &DesugarCtx,
) -> Result<Expr, DeferError> {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let node = match node {
        TypedExprNode::Feed { name, value } if name == defer_name => {
            // Top-level (non-iteration) Feeds carry scalar values that need
            // lifting to `Fun(Unit, T)` to match the defer-handle's
            // expected function shape (the consumer compiles to a
            // SealedFunction operator with Unit domain).  Inside an
            // iteration scope (Lambda body / Loop body), the surrounding
            // Compose/Loop machinery already provides the function shape,
            // so we leave the value scalar — the Compose-with-Lambda case
            // above wraps it with its own `λ x → V` companion.
            let value = *value;
            let lifted = if in_inner_scope {
                value
            } else {
                Expr::lambda("__unused", Type::Base(BaseType::Unit), value)
            };
            feeds.push(lifted);
            TypedExprNode::Lit(Lit::Unit)
        }
        TypedExprNode::Define { name, value } if name == defer_name => {
            if in_inner_scope {
                return Err(DeferError::NestedDefinition);
            }
            if define.is_some() {
                return Err(DeferError::MultipleDefinitions(defer_name.to_string()));
            }
            *define = Some(*value);
            TypedExprNode::Lit(Lit::Unit)
        }
        // Pass through Feed/Define for *other* defers — they'll be processed
        // by a different `channelize_defer` call.
        node @ (TypedExprNode::Feed { .. } | TypedExprNode::Define { .. }) => node,
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // Special case: `let bind = Loop {...} in body`.  Process the
            // Loop's body for feeds and augment its result Record with a
            // `to_<defer>` field if any are found; emit the channel
            // contribution as `Var(bind) ▷ Proj("to_<defer>")` so the
            // loop expression appears only once in the tree.  Without
            // this special case the generic Loop arm clones the Loop
            // into the channel projection, duplicating the entire
            // recurrence cycle in the operator graph.
            if matches!(bound_expr.node, TypedExprNode::Loop { .. }) && binding.name != defer_name {
                let new_bound_expr = process_loop_for_defer(
                    *bound_expr,
                    defer_name,
                    Some(&binding.name),
                    feeds,
                    ctx,
                )?;
                let body =
                    extract_for_defer(*body, defer_name, feeds, define, in_inner_scope, ctx)?;
                TypedExprNode::Let {
                    binding,
                    bound_expr: Box::new(new_bound_expr),
                    body: Box::new(body),
                }
            } else {
                let bound_expr =
                    extract_for_defer(*bound_expr, defer_name, feeds, define, in_inner_scope, ctx)?;
                let body = if binding.name == defer_name {
                    // Inner let shadows the defer name; do not descend.
                    *body
                } else {
                    // Track which feeds get added during the body
                    // walk so we can wrap them with this let's
                    // binding if their free vars reference it.
                    // Without this, an extracted channel like
                    // `Apply(src, λx → V_with_n)` (from a generator
                    // function body with `let n = … in for-loop`)
                    // would float out to the cluster's bind site
                    // with `n` unbound.
                    let prev_len = feeds.len();
                    let new_body =
                        extract_for_defer(*body, defer_name, feeds, define, in_inner_scope, ctx)?;
                    // Wrap each feed extracted during the body walk
                    // with this let-binding.  We always wrap (rather
                    // than testing `count_free`) because the binding
                    // may be referenced through `user_annotation`
                    // refinements (e.g. filter-feed guards) that
                    // `count_free` doesn't currently traverse; if the
                    // binding turns out to be unused in a feed, later
                    // simplification can drop it.
                    for feed in feeds.iter_mut().skip(prev_len) {
                        let placeholder = Expr::new(TypedExprNode::Lit(Lit::Unit));
                        let original = std::mem::replace(feed, placeholder);
                        *feed = Expr::let_bind(binding.name.clone(), bound_expr.clone(), original);
                    }
                    new_body
                };
                TypedExprNode::Let {
                    binding,
                    bound_expr: Box::new(bound_expr),
                    body: Box::new(body),
                }
            }
        }
        TypedExprNode::ExprStmt { expr: e, body } => TypedExprNode::ExprStmt {
            expr: Box::new(extract_for_defer(
                *e,
                defer_name,
                feeds,
                define,
                in_inner_scope,
                ctx,
            )?),
            body: Box::new(extract_for_defer(
                *body,
                defer_name,
                feeds,
                define,
                in_inner_scope,
                ctx,
            )?),
        },
        TypedExprNode::Apply { function, argument } => {
            // Smart-walker: defer-mediating UDF calls.  See the design
            // doc and the chain-rewriter for how these get into the
            // tree.  By matching here we make the cluster algorithm
            // walk *through* a known UDF call, applying logical param
            // substitution while looking for feeds — without
            // physically duplicating the function's body in the
            // output tree.
            if let Some(result) = try_smart_walk_pat(
                &function,
                &argument,
                &ty,
                &user_annotation,
                defer_name,
                feeds,
                ctx,
            ) {
                return Ok(result);
            }
            if let Some(result) = try_smart_walk_di(
                &function,
                &argument,
                &ty,
                &user_annotation,
                defer_name,
                feeds,
                ctx,
            ) {
                return Ok(result);
            }
            // List comprehensions and for-comprehensions lower to
            // `Apply(prefix, Lambda(x, body))`.  When the body contains a
            // feed, we need to expose the per-iteration channel as a
            // companion `Apply(prefix, Lambda(x, V))` — the same iteration
            // shape but yielding the feed value instead of `Unit`.
            //
            // Without this special case, the inner Lambda would be handled
            // by the generic Lambda arm, which wraps each feed in
            // `Lambda(x, V)` — losing the surrounding `Apply(prefix, …)`
            // context that connects the lambda to its iteration source.
            if let TypedExprNode::Lambda {
                param,
                body: lambda_body,
                refinement,
            } = function.node.clone()
                && param.name != defer_name
            {
                // Filter-feed pattern: `λ p → Case({g → Feed(d, V); true →
                // Unit})`.  Recognized so we can emit the channel as a
                // *refined* Lambda — `Lambda(p, V, refinement: g)` — and
                // collapse the original Lambda's body to Unit.  Without
                // this, the generic Case handler wraps both arms in
                // mismatched Records (`to_d: V` vs `to_d: unit`) which
                // fails inference.
                if let Some((guard, feed_value)) = try_extract_filter_feed(&lambda_body, defer_name)
                {
                    let new_argument = extract_for_defer(
                        *argument.clone(),
                        defer_name,
                        feeds,
                        define,
                        in_inner_scope,
                        ctx,
                    )?;
                    // Same refinement strategy as the Compose case
                    // above: build `pred = source ≫ (λ p → guard)` and
                    // attach `Refinement(_, pred)` to the source's
                    // *domain* (via `user_annotation` so infer carries
                    // it through), then compose `refined_source ≫ (λ
                    // p → V)` as the channel.
                    let pred_lambda = Expr::lambda(&param.name, param.ty.clone(), guard);
                    let pred_on_source = Expr::apply(new_argument.clone(), pred_lambda);
                    let refinement_struct = Refinement {
                        id: next_refinement_id(),
                        description: "filter-feed".to_string(),
                        kind: RefinementKind::Predicate(Rc::new(RefCell::new(pred_on_source))),
                    };
                    let mut refined_argument = new_argument.clone();
                    refined_argument.user_annotation = Some(Type::fun(
                        Type::Refinement(Box::new(Type::Hole), refinement_struct),
                        Type::Hole,
                    ));
                    let channel_lambda = Expr::lambda(&param.name, param.ty.clone(), feed_value);
                    let channel = Expr::apply(refined_argument, channel_lambda);
                    feeds.push(channel);
                    let unit_body = Expr::lit(Lit::Unit);
                    let new_function = Expr::lambda(&param.name, param.ty.clone(), unit_body);
                    return Ok(TypedExpr {
                        node: TypedExprNode::Apply {
                            function: Box::new(new_function),
                            argument: Box::new(new_argument),
                        },
                        ty,
                        user_annotation,
                    });
                }

                let mut lambda_feeds: Vec<Expr> = Vec::new();
                let mut lambda_define: Option<Expr> = None;
                let new_lambda_body = extract_for_defer(
                    *lambda_body,
                    defer_name,
                    &mut lambda_feeds,
                    &mut lambda_define,
                    true,
                    ctx,
                )?;
                if lambda_define.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                let new_argument = extract_for_defer(
                    *argument.clone(),
                    defer_name,
                    feeds,
                    define,
                    in_inner_scope,
                    ctx,
                )?;
                for v in lambda_feeds {
                    let channel_lambda = Expr::lambda(&param.name, param.ty.clone(), v);
                    let channel = Expr::apply(new_argument.clone(), channel_lambda);
                    feeds.push(channel);
                }
                let new_function = TypedExpr {
                    node: TypedExprNode::Lambda {
                        param,
                        body: Box::new(new_lambda_body),
                        refinement,
                    },
                    ty: function.ty.clone(),
                    user_annotation: function.user_annotation.clone(),
                };
                TypedExprNode::Apply {
                    function: Box::new(new_function),
                    argument: Box::new(new_argument),
                }
            } else {
                let new_function =
                    extract_for_defer(*function, defer_name, feeds, define, in_inner_scope, ctx)?;
                let new_argument =
                    extract_for_defer(*argument, defer_name, feeds, define, in_inner_scope, ctx)?;
                // Re-check DI/PaT patterns on the reconstructed
                // Apply.  Composed chains like `g(f(10))` come in
                // here: the inner f-call has been reduced to
                // `Var(defer_name)` by the recursive walk, exposing
                // the outer Apply as a direct PaT/DI call.  We pass
                // `wrap_prefix_from_transformed = false` because the
                // recursion already wrapped any prefixes at its own
                // level; the reduction here just hands back
                // `Var(defer_name)`.
                if let Some(result) = try_smart_walk_pat(
                    &new_function,
                    &new_argument,
                    &ty,
                    &user_annotation,
                    defer_name,
                    feeds,
                    ctx,
                ) {
                    return Ok(result);
                }
                if let Some(result) = try_smart_walk_di(
                    &new_function,
                    &new_argument,
                    &ty,
                    &user_annotation,
                    defer_name,
                    feeds,
                    ctx,
                ) {
                    return Ok(result);
                }
                TypedExprNode::Apply {
                    function: Box::new(new_function),
                    argument: Box::new(new_argument),
                }
            }
        }
        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(extract_for_defer(
                *left,
                defer_name,
                feeds,
                define,
                in_inner_scope,
                ctx,
            )?),
            op,
            right: Box::new(extract_for_defer(
                *right,
                defer_name,
                feeds,
                define,
                in_inner_scope,
                ctx,
            )?),
        },
        TypedExprNode::UnaryOp(op, inner) => TypedExprNode::UnaryOp(
            op,
            Box::new(extract_for_defer(
                *inner,
                defer_name,
                feeds,
                define,
                in_inner_scope,
                ctx,
            )?),
        ),
        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(extract_for_defer(
                *input,
                defer_name,
                feeds,
                define,
                in_inner_scope,
                ctx,
            )?),
            kind,
        },
        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(
            elts.into_iter()
                .map(|e| extract_for_defer(e, defer_name, feeds, define, in_inner_scope, ctx))
                .collect::<Result<_, _>>()?,
        ),
        TypedExprNode::List(elts) => TypedExprNode::List(
            elts.into_iter()
                .map(|e| extract_for_defer(e, defer_name, feeds, define, in_inner_scope, ctx))
                .collect::<Result<_, _>>()?,
        ),
        TypedExprNode::Compose(elts) => {
            // Composes commonly carry Lambdas whose bodies contain feeds —
            // e.g. `src ≫ (λ x → Feed(d, x*N))` lowered from `for x in src:
            // d << x*N`.  When that happens the feed value references the
            // lambda's param, which is only in scope inside the lambda.  To
            // expose this value to the enclosing defer-bind site, we build
            // a *companion* Compose for each per-iteration feed: take the
            // prefix of compose elements before the lambda, append
            // `Lambda(x, V)`, and emit that Compose as a feed
            // contribution.  The original lambda's body has its feeds
            // replaced with `Unit`.
            //
            // Non-lambda elements (and lambdas without inner feeds) recurse
            // normally — feeds picked up there will be directly bound at
            // the surrounding scope.
            let mut new_elts: Vec<Expr> = Vec::with_capacity(elts.len());
            for elt in elts.into_iter() {
                let elt_ty = elt.ty.clone();
                let elt_user_ann = elt.user_annotation.clone();
                match elt.node {
                    TypedExprNode::Lambda {
                        param,
                        body,
                        refinement,
                    } if param.name != defer_name => {
                        // Filter-feed: `λ p → Case({g → Feed(d, V); true →
                        // Unit})` becomes a refined-Lambda channel
                        // (`λ p with {g} → V`) plus a Lambda whose body
                        // is `Unit`.  See [`try_extract_filter_feed`].
                        if let Some((guard, feed_value)) =
                            try_extract_filter_feed(&body, defer_name)
                        {
                            // Construct the refined source the same way
                            // [`crate::ccl::lambda_elim`]'s filter-pattern
                            // rewrite does: `predicate = source ≫ (λ p →
                            // guard)` (a `Fun(source_domain, Bool)` over
                            // the iteration index), then wrap source's
                            // *domain* in `Refinement(_, pred)` so the
                            // operator graph restricts the iteration to
                            // indices where the guard holds.
                            let source_prefix = if new_elts.len() == 1 {
                                new_elts[0].clone()
                            } else {
                                Expr::compose(new_elts.clone())
                            };
                            let pred_lambda = Expr::lambda(&param.name, param.ty.clone(), guard);
                            let pred_on_source =
                                Expr::compose(vec![source_prefix.clone(), pred_lambda]);
                            let refinement_struct = Refinement {
                                id: next_refinement_id(),
                                description: "filter-feed".to_string(),
                                kind: RefinementKind::Predicate(Rc::new(RefCell::new(
                                    pred_on_source,
                                ))),
                            };
                            let mut refined_prefix = source_prefix.clone();
                            refined_prefix.user_annotation = Some(Type::fun(
                                Type::Refinement(Box::new(Type::Hole), refinement_struct),
                                Type::Hole,
                            ));
                            let channel_lambda =
                                Expr::lambda(&param.name, param.ty.clone(), feed_value);
                            let channel_expr = Expr::compose(vec![refined_prefix, channel_lambda]);
                            feeds.push(channel_expr);
                            // The original Lambda's body becomes `Unit`
                            // (matching the Case's non-feeding-arm
                            // value); after lambda elim it composes
                            // with the unrefined source to a no-op
                            // iteration.
                            let new_lambda = TypedExpr {
                                node: TypedExprNode::Lambda {
                                    param,
                                    body: Box::new(Expr::lit(Lit::Unit)),
                                    refinement,
                                },
                                ty: elt_ty,
                                user_annotation: elt_user_ann,
                            };
                            new_elts.push(new_lambda);
                            continue;
                        }
                        let mut lambda_feeds: Vec<Expr> = Vec::new();
                        let mut lambda_define: Option<Expr> = None;
                        let new_body = extract_for_defer(
                            *body,
                            defer_name,
                            &mut lambda_feeds,
                            &mut lambda_define,
                            true,
                            ctx,
                        )?;
                        if lambda_define.is_some() {
                            return Err(DeferError::NestedDefinition);
                        }
                        // Emit per-feed companion composes BEFORE pushing
                        // the rewritten lambda — `new_elts` is the prefix
                        // up to (but not including) this element, which is
                        // exactly the surrounding context the feed value
                        // needs.
                        for v in lambda_feeds {
                            let channel_lambda = Expr::lambda(&param.name, Type::Hole, v);
                            let mut channel_elts = new_elts.clone();
                            channel_elts.push(channel_lambda);
                            // A single-element "compose" is just that
                            // element; otherwise build a Compose.
                            let channel_expr = if channel_elts.len() == 1 {
                                channel_elts.into_iter().next().unwrap()
                            } else {
                                Expr::compose(channel_elts)
                            };
                            feeds.push(channel_expr);
                        }
                        new_elts.push(TypedExpr {
                            node: TypedExprNode::Lambda {
                                param,
                                body: Box::new(new_body),
                                refinement,
                            },
                            ty: elt_ty,
                            user_annotation: elt_user_ann,
                        });
                    }
                    other => {
                        let elt = TypedExpr {
                            node: other,
                            ty: elt_ty,
                            user_annotation: elt_user_ann,
                        };
                        new_elts.push(extract_for_defer(
                            elt,
                            defer_name,
                            feeds,
                            define,
                            in_inner_scope,
                            ctx,
                        )?);
                    }
                }
            }
            TypedExprNode::Compose(new_elts)
        }
        TypedExprNode::CollectionUnion(elts) => TypedExprNode::CollectionUnion(
            elts.into_iter()
                .map(|e| extract_for_defer(e, defer_name, feeds, define, in_inner_scope, ctx))
                .collect::<Result<_, _>>()?,
        ),
        TypedExprNode::Record(fields) => {
            let mut new_fields = Vec::with_capacity(fields.len());
            for (n, e) in fields {
                new_fields.push((
                    n,
                    extract_for_defer(e, defer_name, feeds, define, in_inner_scope, ctx)?,
                ));
            }
            TypedExprNode::Record(new_fields)
        }
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            // Lambda body is an inner scope.  Feeds extracted from inside
            // may reference the param, so each channel contribution must
            // be re-wrapped with the same Lambda before bubbling up to
            // the caller — otherwise param references would be unbound
            // in the outer scope.
            //
            // (The Compose-with-Lambda case above handles the more
            // specific pattern `prefix ≫ (λx → Feed(d, V))` directly,
            // producing a `prefix ≫ (λx → V)` Compose channel.  This
            // generic Lambda arm covers Lambdas that aren't the tail
            // element of a Compose — e.g. a top-level Lambda body that
            // contains an ExprStmt-wrapped Compose-with-feed.)
            let mut local_feeds: Vec<Expr> = Vec::new();
            let mut local_define: Option<Expr> = None;
            let body = if param.name == defer_name {
                *body
            } else {
                extract_for_defer(
                    *body,
                    defer_name,
                    &mut local_feeds,
                    &mut local_define,
                    true,
                    ctx,
                )?
            };
            if local_define.is_some() {
                return Err(DeferError::NestedDefinition);
            }
            for v in local_feeds {
                feeds.push(Expr::lambda(&param.name, param.ty.clone(), v));
            }
            TypedExprNode::Lambda {
                param,
                body: Box::new(body),
                refinement,
            }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            // Case branches: each branch is an inner scope.  When *some*
            // arm contains a feed for `defer_name`, we wrap each arm's
            // terminal in `Record({result, to_<d>})` with an Empty channel
            // for arms that don't feed (so all arms share the same Record
            // shape), and the Case's outer value becomes that Record.  The
            // surrounding scope's channel contribution is `case ▷
            // Proj("to_<d>")` and the surrounding `result` is `case ▷
            // Proj("result")`.
            //
            // For arms with feeds where the feed value references arm-local
            // bindings, the Record wrap inside the arm keeps those bindings
            // in scope at the publication site.
            let mut per_branch: Vec<(Option<Pattern>, Expr, Vec<Expr>, Expr)> =
                Vec::with_capacity(branches.len());
            let mut any_feed = false;
            for Branch {
                pattern,
                guard,
                body,
            } in branches
            {
                let mut branch_feeds = Vec::new();
                let mut branch_define = None;
                let body = extract_for_defer(
                    body,
                    defer_name,
                    &mut branch_feeds,
                    &mut branch_define,
                    true,
                    ctx,
                )?;
                if branch_define.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                if !branch_feeds.is_empty() {
                    any_feed = true;
                }
                per_branch.push((pattern, guard, branch_feeds, body));
            }
            if any_feed {
                let new_branches: Vec<Branch> = per_branch
                    .into_iter()
                    .map(|(pattern, guard, branch_feeds, body)| {
                        let channel = if branch_feeds.is_empty() {
                            empty_channel()
                        } else {
                            combine_feed_values(branch_feeds)
                        };
                        // Build the arm's per-branch Record at its terminal.
                        let wrapped = augment_terminal_with_channel(body, defer_name, channel);
                        Branch {
                            pattern,
                            guard,
                            body: wrapped,
                        }
                    })
                    .collect();
                let case_expr = TypedExpr {
                    node: TypedExprNode::Case {
                        scrutinee: scrutinee.clone(),
                        branches: new_branches,
                    },
                    ty: ty.clone(),
                    user_annotation: user_annotation.clone(),
                };
                feeds.push(Expr::apply(
                    case_expr.clone(),
                    Expr::proj_field(channel_field_name(defer_name)),
                ));
                return Ok(Expr::apply(case_expr, Expr::proj_field("result")));
            }
            TypedExprNode::Case {
                scrutinee,
                branches: per_branch
                    .into_iter()
                    .map(|(pattern, guard, _, body)| Branch {
                        pattern,
                        guard,
                        body,
                    })
                    .collect(),
            }
        }
        loop_node @ TypedExprNode::Loop { .. } => {
            // A bare Loop without an enclosing `let bind = Loop {...}`
            // wrapper.  In practice [`crate::ccl::lower::lower_mutation_loop`]
            // always binds the Loop to a fresh name, so this path
            // duplicates the recurrence cycle and is undesirable.  Delegate
            // to [`process_loop_for_defer`] with no binding name, which
            // pushes the cloned loop as the channel value.
            let loop_expr = TypedExpr {
                node: loop_node,
                ty,
                user_annotation,
            };
            return process_loop_for_defer(loop_expr, defer_name, None, feeds, ctx);
        }
        // Leaf nodes — no feeds possible.
        node @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer) => node,
        TypedExprNode::Error => crate::unexpected_error_node!(),
        TypedExprNode::VariantCtor { .. } => {
            unreachable!("desugar_defers: VariantCtor not yet emitted by lowering")
        }
    };
    Ok(TypedExpr {
        node,
        ty,
        user_annotation,
    })
}

/// Walk `expr` through `Let`/`ExprStmt` bodies to its terminal and wrap
/// with `Record({result: <terminal>, to_<defer>: channel})`.
///
/// Used by the Case-branch arm to publish the per-branch channel value.
fn augment_terminal_with_channel(expr: Expr, defer_name: &str, channel: Expr) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => TypedExpr {
            node: TypedExprNode::Let {
                binding,
                bound_expr,
                body: Box::new(augment_terminal_with_channel(*body, defer_name, channel)),
            },
            ty,
            user_annotation,
        },
        TypedExprNode::ExprStmt { expr: e, body } => TypedExpr {
            node: TypedExprNode::ExprStmt {
                expr: e,
                body: Box::new(augment_terminal_with_channel(*body, defer_name, channel)),
            },
            ty,
            user_annotation,
        },
        other => {
            let terminal = TypedExpr {
                node: other,
                ty,
                user_annotation,
            };
            Expr::new(TypedExprNode::Record(vec![
                ("result".to_string(), terminal),
                (channel_field_name(defer_name), channel),
            ]))
        }
    }
}

/// Process a `Loop` expression for `defer_name`, optionally using
/// `binding_name` to reference the loop's bound name when emitting the
/// channel projection.
///
/// - Walks the loop body for `Feed(defer_name, V)` nodes.
/// - If found, augments the body's terminal `Record({step, …})` with a
///   `to_<defer>: V` field (using [`augment_loop_body_record`]).
/// - Pushes `Var(binding) ▷ Proj("to_<defer>")` (or the cloned loop value
///   when no binding name is available) into `feeds` as the loop's
///   per-iteration channel contribution to the enclosing scope.
///
/// Init args and source are evaluated outside the loop's parameter scope;
/// feeds inside them contribute directly to the enclosing scope and are
/// extracted by recursing through [`extract_for_defer`].
fn process_loop_for_defer(
    loop_expr: Expr,
    defer_name: &str,
    binding_name: Option<&str>,
    feeds: &mut Vec<Expr>,
    ctx: &DesugarCtx,
) -> Result<Expr, DeferError> {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = loop_expr;
    let TypedExprNode::Loop {
        params,
        init_args,
        source,
        loop_body,
    } = node
    else {
        unreachable!("process_loop_for_defer called on non-Loop")
    };
    let mut local_feeds: Vec<Expr> = Vec::new();
    let mut local_define: Option<Expr> = None;
    let new_init: Vec<Expr> = init_args
        .into_iter()
        .map(|e| extract_for_defer(e, defer_name, feeds, &mut local_define, false, ctx))
        .collect::<Result<_, _>>()?;
    if local_define.is_some() {
        return Err(DeferError::NestedDefinition);
    }
    let new_source = Box::new(extract_for_defer(
        *source,
        defer_name,
        feeds,
        &mut local_define,
        false,
        ctx,
    )?);
    if local_define.is_some() {
        return Err(DeferError::NestedDefinition);
    }
    let body_shadows = params.iter().any(|p| p.name == defer_name);
    if body_shadows {
        return Ok(TypedExpr {
            node: TypedExprNode::Loop {
                params,
                init_args: new_init,
                source: new_source,
                loop_body,
            },
            ty,
            user_annotation,
        });
    }
    // Loop bodies are always emitted as `Lambda(p, inner)` by
    // [`crate::ccl::lower::lower_mutation_loop`].  We descend INTO that
    // Lambda's body to extract feeds without re-wrapping them in the
    // same Lambda — the Lambda is the iteration's domain, not an outer
    // function scope, so per-iteration feed values stay raw and get
    // placed directly into the body's terminal Record via
    // [`augment_loop_body_record`].
    let TypedExpr {
        node: loop_body_node,
        ty: loop_body_ty,
        user_annotation: loop_body_ann,
    } = *loop_body;
    let (new_loop_body, body_feeds) = match loop_body_node {
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            let mut body_feeds: Vec<Expr> = Vec::new();
            let mut body_define: Option<Expr> = None;
            let new_inner = extract_for_defer(
                *body,
                defer_name,
                &mut body_feeds,
                &mut body_define,
                true,
                ctx,
            )?;
            if body_define.is_some() {
                return Err(DeferError::NestedDefinition);
            }
            let new_lambda = TypedExpr {
                node: TypedExprNode::Lambda {
                    param,
                    body: Box::new(new_inner),
                    refinement,
                },
                ty: loop_body_ty,
                user_annotation: loop_body_ann,
            };
            (new_lambda, body_feeds)
        }
        other => {
            // Non-Lambda loop body — defer to the generic path.  Should
            // not happen in practice with current lowering.
            let mut body_feeds: Vec<Expr> = Vec::new();
            let mut body_define: Option<Expr> = None;
            let body_expr = TypedExpr {
                node: other,
                ty: loop_body_ty,
                user_annotation: loop_body_ann,
            };
            let new_body = extract_for_defer(
                body_expr,
                defer_name,
                &mut body_feeds,
                &mut body_define,
                true,
                ctx,
            )?;
            if body_define.is_some() {
                return Err(DeferError::NestedDefinition);
            }
            (new_body, body_feeds)
        }
    };
    if body_feeds.is_empty() {
        feeds.append(&mut local_feeds);
        return Ok(TypedExpr {
            node: TypedExprNode::Loop {
                params,
                init_args: new_init,
                source: new_source,
                loop_body: Box::new(new_loop_body),
            },
            ty,
            user_annotation,
        });
    }
    // Each feed-site inside the loop body contributes a separate
    // per-iteration stream over the loop's domain.  We can't combine the
    // raw scalar values inside the body via `++` (collection union expects
    // function-typed operands), so we emit one `to_<defer>_<k>` field per
    // feed site and union the resulting outer projections instead.
    let n_feeds = body_feeds.len();
    let tap_fields: Vec<String> = (0..n_feeds)
        .map(|k| format!("{}_{}", channel_field_name(defer_name), k))
        .collect();
    let new_body =
        augment_loop_body_record_multi(new_loop_body, tap_fields.iter().zip(body_feeds))?;
    let new_loop = TypedExpr {
        node: TypedExprNode::Loop {
            params,
            init_args: new_init,
            source: new_source,
            loop_body: Box::new(new_body),
        },
        ty,
        user_annotation,
    };
    // Build the outer channel: one `Var(binding) ▷ Proj("to_<d>_<k>")`
    // projection per feed, unioned via `++`.  When there's no binding to
    // reference the loop by, we clone the loop into each projection —
    // this duplicates the recurrence cycle but [`lower_mutation_loop`]
    // always binds the loop to a fresh name in practice.
    let channels: Vec<Expr> = tap_fields
        .iter()
        .map(|field| match binding_name {
            Some(name) => Expr::compose(vec![Expr::var(name), Expr::proj_field(field)]),
            None => Expr::compose(vec![new_loop.clone(), Expr::proj_field(field)]),
        })
        .collect();
    let combined = combine_feed_values(channels);
    feeds.push(combined);
    feeds.append(&mut local_feeds);
    Ok(new_loop)
}

/// Augment a loop body's terminal Record with multiple per-feed fields
/// in one walk.  Each `(field_name, value)` pair contributes one Record
/// field; subsequent fields are appended to the same terminal Record.
fn augment_loop_body_record_multi<'a, I>(expr: Expr, fields: I) -> Result<Expr, DeferError>
where
    I: IntoIterator<Item = (&'a String, Expr)>,
{
    let mut result = expr;
    for (field_name, value) in fields {
        result = augment_loop_body_record_named(result, field_name, value)?;
    }
    Ok(result)
}

/// Augment a loop body's terminal Record with an additional field of the
/// given name.  Walks through `Let`/`ExprStmt`/`Lambda` wrappers to the
/// deepest `Record` literal.
fn augment_loop_body_record_named(
    expr: Expr,
    field_name: &str,
    value: Expr,
) -> Result<Expr, DeferError> {
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let node = match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => TypedExprNode::Let {
            binding,
            bound_expr,
            body: Box::new(augment_loop_body_record_named(*body, field_name, value)?),
        },
        TypedExprNode::ExprStmt { expr: e, body } => TypedExprNode::ExprStmt {
            expr: e,
            body: Box::new(augment_loop_body_record_named(*body, field_name, value)?),
        },
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => TypedExprNode::Lambda {
            param,
            body: Box::new(augment_loop_body_record_named(*body, field_name, value)?),
            refinement,
        },
        TypedExprNode::Record(mut fields) => {
            fields.push((field_name.to_string(), value));
            TypedExprNode::Record(fields)
        }
        other => {
            // Not a Record literal — wrap.
            let terminal = TypedExpr {
                node: other,
                ty: ty.clone(),
                user_annotation: user_annotation.clone(),
            };
            return Ok(Expr::new(TypedExprNode::Record(vec![
                ("result".to_string(), terminal),
                (field_name.to_string(), value),
            ])));
        }
    };
    Ok(TypedExpr {
        node,
        ty,
        user_annotation,
    })
}

/// Build an "empty" channel value for Case branches that don't directly
/// feed a defer.
///
/// **Known limitation — this emits `Lit::Unit`, which is type-wrong
/// for the position.**  Each branch's `to_<d>` Record field sits at
/// scalar position (the surrounding `extract_for_defer` runs with
/// `in_inner_scope = true`, so feed values are kept raw rather than
/// lifted to `Fun(Unit, T)`).  For all Case arms to unify, every
/// `to_<d>` field must have the same type as the feeding arms
/// produce (`T`).  `Unit` only unifies with itself, so the Case-arm
/// fan-out only typechecks today when the feeding arms produce
/// scalar `Unit` values.
///
/// **Why we don't patch the type in place.**  We considered adding a
/// `TypedExprNode::EmptyValue` variant with a fresh `Type::Infer` so
/// the per-arm Record types unify.  That fixes the typecheck error
/// but doesn't fix the runtime semantics: the Case fan-out would
/// still produce a per-iteration `to_<d>` value for *every*
/// iteration, including ones where the implicit `true → unit` arm
/// fires.  The defer's downstream consumer would see a phantom
/// placeholder in the stream where the user expects no contribution
/// at all.  Trading a typecheck error for a silent miscompile is a
/// net regression.
///
/// **The real fix is refinement-based fan-out** (generalize
/// [`try_extract_filter_feed`] to N arms).  For each feeding arm
/// `i`, build a refined source whose predicate is
/// `¬g_0 ∧ ¬g_1 ∧ … ∧ ¬g_{i-1} ∧ g_i`, and contribute
/// `refined_source ≫ (λ p → feed_value)` to the cluster channel
/// via `++`.  Arms without feeds contribute nothing — no empty
/// placeholder needed.  Both the typecheck and the runtime gap
/// vanish together.
///
/// See [`tests/compilation_pipeline.rs`]'s
/// `multi_arm_case_with_some_feeding_branches_is_a_known_gap` for
/// the stacked-gap walkthrough and the recommended fix shape.
///
/// The common two-arm `if cond: d << x` case is handled by
/// [`try_extract_filter_feed`] without ever calling `empty_channel`,
/// which is why this gap doesn't bite realistic programs today.
///
/// FIXME(desugar_defers-prototype): the N-arm Case fan-out is one of
/// the open items tracked under the umbrella entry in `docs/plan.md`
/// ("Tech Debt — `desugar_defers` prototype").
fn empty_channel() -> Expr {
    Expr::lit(Lit::Unit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BinOpKind, Lit, symbolic::symbolic};

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }
    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    // -----------------------------------------------------------------
    // lambda classification + defer-float helpers
    // -----------------------------------------------------------------

    /// `λx → x` — pure identity is [`LambdaClass::VarBody`].
    #[test]
    fn classify_identity_is_varbody() {
        let lambda = Expr::lambda("x", Type::Hole, var("x"));
        assert_eq!(classify_lambda(&lambda), LambdaClass::VarBody);
    }

    /// `λn → let x = Defer in x` — defer-introducing.
    #[test]
    fn classify_defer_introducing() {
        let body = Expr::let_bind("x", Expr::new(TypedExprNode::Defer), var("x"));
        let lambda = Expr::lambda("n", Type::Hole, body);
        assert_eq!(classify_lambda(&lambda), LambdaClass::DeferIntroducing);
    }

    /// `λc → feed(c, 100); c` — param-as-target.
    #[test]
    fn classify_param_as_target() {
        let body = Expr::expr_stmt(Expr::feed("c".into(), lit(100)), var("c"));
        let lambda = Expr::lambda("c", Type::Hole, body);
        assert_eq!(classify_lambda(&lambda), LambdaClass::ParamAsTarget);
    }

    /// `λx → x + 1` — plain function, no defer interaction.
    #[test]
    fn classify_plain() {
        let body = Expr::new(TypedExprNode::BinOp {
            left: Box::new(var("x")),
            op: BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
            right: Box::new(lit(1)),
        });
        let lambda = Expr::lambda("x", Type::Hole, body);
        assert_eq!(classify_lambda(&lambda), LambdaClass::Plain);
    }

    /// `λp → let x = Defer in feed(x, p); x` floats to
    /// `λp → λ__floated_x → feed(__floated_x, p); __floated_x`.
    #[test]
    fn float_defer_introducing_lambda() {
        let inner = Expr::expr_stmt(Expr::feed("x".into(), var("p")), var("x"));
        let body = Expr::let_bind("x", Expr::new(TypedExprNode::Defer), inner);
        let lambda = Expr::lambda("p", Type::Hole, body);
        let floated = float_defer_in_lambda(lambda).expect("should float");

        // Expect a Lambda whose body is another Lambda (the floated
        // defer param) whose body has feeds targeting the floated name.
        let TypedExprNode::Lambda {
            param: outer_param,
            body: outer_body,
            ..
        } = floated.node
        else {
            panic!("expected outer Lambda after float");
        };
        assert_eq!(outer_param.name, "p");
        let TypedExprNode::Lambda {
            param: inner_param,
            body: inner_body,
            ..
        } = outer_body.node
        else {
            panic!("expected inner Lambda after float (the floated param)");
        };
        assert_eq!(inner_param.name, "__floated_x");
        // The inner body should be `ExprStmt(Feed("__floated_x", p), Var("__floated_x"))`.
        let TypedExprNode::ExprStmt {
            expr: feed_node,
            body: ret_node,
        } = inner_body.node
        else {
            panic!("expected ExprStmt as inner body");
        };
        let TypedExprNode::Feed {
            name: feed_name, ..
        } = feed_node.node
        else {
            panic!("expected Feed node");
        };
        assert_eq!(feed_name, "__floated_x", "feed target renamed to floated");
        let TypedExprNode::Var(ret_name) = ret_node.node else {
            panic!("expected Var as return");
        };
        assert_eq!(ret_name, "__floated_x", "return renamed to floated");
    }

    /// Non-DeferIntroducing lambdas return `None` from `float_defer_in_lambda`.
    #[test]
    fn float_returns_none_for_param_as_target() {
        let body = Expr::expr_stmt(Expr::feed("c".into(), lit(100)), var("c"));
        let lambda = Expr::lambda("c", Type::Hole, body);
        assert!(float_defer_in_lambda(lambda).is_none());
    }

    /// Non-Lambda input returns `None`.
    #[test]
    fn float_returns_none_for_non_lambda() {
        assert!(float_defer_in_lambda(var("x")).is_none());
    }

    /// `λxs → let n = 0 in let x = Defer in body` — the `Defer` is
    /// nested under a let-prefix.  [`extract_defer_binding`] must
    /// descend through the prefix so float still succeeds.
    #[test]
    fn classify_and_float_through_let_prefix() {
        let inner = Expr::expr_stmt(Expr::feed("x".into(), var("xs")), var("x"));
        let defer_let = Expr::let_bind("x", Expr::new(TypedExprNode::Defer), inner);
        let n_let = Expr::let_bind("n", lit(0), defer_let);
        let lambda = Expr::lambda("xs", Type::Hole, n_let);
        // Classification recognises this as DeferIntroducing (the
        // body still `contains_defer`).
        assert_eq!(classify_lambda(&lambda), LambdaClass::DeferIntroducing);
        let floated = float_defer_in_lambda(lambda).expect("should float through prefix");
        // After float, outer Lambda's body is a Lambda whose body is
        // `let n = 0 in ExprStmt(Feed(__floated_x, xs), __floated_x)`.
        let TypedExprNode::Lambda { body: outer, .. } = floated.node else {
            panic!()
        };
        let TypedExprNode::Lambda {
            param: inner_param,
            body: inner_body,
            ..
        } = outer.node
        else {
            panic!()
        };
        assert_eq!(inner_param.name, "__floated_x");
        let TypedExprNode::Let { binding, body, .. } = inner_body.node else {
            panic!("expected let-prefix preserved under floated lambda")
        };
        assert_eq!(binding.name, "n");
        // The let-prefix's body should be the renamed inner.
        let TypedExprNode::ExprStmt { expr, .. } = body.node else {
            panic!()
        };
        let TypedExprNode::Feed { name, .. } = expr.node else {
            panic!()
        };
        assert_eq!(name, "__floated_x");
    }

    /// Post-float curried form: `λn → λ__floated_x → __floated_x`
    /// should still be classified as `DeferIntroducing` so the
    /// smart walker recognises it.
    #[test]
    fn classify_post_float_curried_form() {
        let inner = Expr::lambda("__floated_x", Type::Hole, var("__floated_x"));
        let outer = Expr::lambda("n", Type::Hole, inner);
        assert_eq!(classify_lambda(&outer), LambdaClass::DeferIntroducing);
    }

    /// `λn → λ__floated → feed(__floated, n); __floated` — body uses
    /// the inner param as a feed target.  Recognised as DI.
    #[test]
    fn classify_post_float_curried_with_param_feed() {
        let inner_body =
            Expr::expr_stmt(Expr::feed("__floated".into(), var("n")), var("__floated"));
        let inner = Expr::lambda("__floated", Type::Hole, inner_body);
        let outer = Expr::lambda("n", Type::Hole, inner);
        assert_eq!(classify_lambda(&outer), LambdaClass::DeferIntroducing);
    }

    // -----------------------------------------------------------------
    // Chain rewriter helpers: chain_has_di, wrap_di_calls_in_chain
    // -----------------------------------------------------------------

    /// Shared helper for tests that need a `FunctionInfo` for the
    /// chain rewriter's call-shape detection.  The chain rewriter
    /// only looks at `class`, so the per-target fields are empty —
    /// real Phase 2 registration populates them via
    /// [`rewrite_lambda_to_return_contributions`].
    fn test_function_info(class: LambdaClass, lambda: Expr) -> FunctionInfo {
        FunctionInfo {
            class,
            lambda,
            feed_targets: Vec::new(),
            primary_target: String::new(),
        }
    }

    fn ctx_with_di(name: &str) -> DesugarCtx {
        let mut ctx = DesugarCtx::new();
        let lambda = Expr::lambda(
            "p",
            Type::Hole,
            Expr::lambda("__floated", Type::Hole, var("__floated")),
        );
        ctx.register_function(
            name.into(),
            test_function_info(LambdaClass::DeferIntroducing, lambda),
        );
        ctx
    }

    fn ctx_with_pat(name: &str) -> DesugarCtx {
        let mut ctx = DesugarCtx::new();
        let body = Expr::expr_stmt(Expr::feed("c".into(), lit(100)), var("c"));
        let lambda = Expr::lambda("c", Type::Hole, body);
        ctx.register_function(
            name.into(),
            test_function_info(LambdaClass::ParamAsTarget, lambda),
        );
        ctx
    }

    /// `Apply(arg, Var(f))` with `f` DI: `chain_has_di` returns true.
    #[test]
    fn chain_has_di_simple() {
        let ctx = ctx_with_di("f");
        let expr = Expr::apply(lit(10), var("f"));
        assert!(chain_has_di(&expr, &ctx));
    }

    /// `Apply(arg, Var(g))` with `g` ParamAsTarget: not DI by itself.
    #[test]
    fn chain_has_di_pat_alone_is_not_di() {
        let ctx = ctx_with_pat("g");
        let expr = Expr::apply(var("d"), var("g"));
        assert!(!chain_has_di(&expr, &ctx));
    }

    /// `Apply(Apply(arg, Var(f)), Var(g))` — composed PaT(DI(arg)) —
    /// has a DI call nested inside.
    #[test]
    fn chain_has_di_composed_pat_outer() {
        let mut ctx = DesugarCtx::new();
        let di_lambda = Expr::lambda(
            "p",
            Type::Hole,
            Expr::lambda("__floated", Type::Hole, var("__floated")),
        );
        ctx.register_function(
            "f".into(),
            test_function_info(LambdaClass::DeferIntroducing, di_lambda),
        );
        let pat_lambda = Expr::lambda(
            "c",
            Type::Hole,
            Expr::expr_stmt(Expr::feed("c".into(), lit(100)), var("c")),
        );
        ctx.register_function(
            "g".into(),
            test_function_info(LambdaClass::ParamAsTarget, pat_lambda),
        );
        let inner = Expr::apply(lit(10), var("f"));
        let outer = Expr::apply(inner, var("g"));
        assert!(chain_has_di(&outer, &ctx), "composed PaT-of-DI is DI");
    }

    /// `Apply(arg, Var(f))` with `f` DI gets wrapped with the
    /// requested defer name as the second-apply argument.
    #[test]
    fn wrap_di_calls_single_call() {
        let mut ctx = ctx_with_di("f");
        let expr = Expr::apply(lit(10), var("f"));
        let (wrapped, fresh) = wrap_di_calls_in_chain(expr, "y", &mut ctx);
        assert!(fresh.is_empty(), "single DI uses requested name only");
        // Expect Apply { function: Apply { function: Var(f), argument: Lit(10) }, argument: Var(y) }
        let TypedExprNode::Apply {
            function: outer_fn,
            argument: outer_arg,
        } = wrapped.node
        else {
            panic!()
        };
        let TypedExprNode::Var(arg_name) = outer_arg.node else {
            panic!()
        };
        assert_eq!(arg_name, "y");
        let TypedExprNode::Apply {
            function: inner_fn, ..
        } = outer_fn.node
        else {
            panic!()
        };
        let TypedExprNode::Var(fn_name) = inner_fn.node else {
            panic!()
        };
        assert_eq!(fn_name, "f");
    }

    /// Composed DI-DI `doubles(add_one(xs))` allocates a separate
    /// fresh defer for the inner DI call; the outermost uses the
    /// requested name.
    #[test]
    fn wrap_di_calls_composed_di_di() {
        let mut ctx = DesugarCtx::new();
        let di_lambda = Expr::lambda(
            "p",
            Type::Hole,
            Expr::lambda("__floated", Type::Hole, var("__floated")),
        );
        ctx.register_function(
            "add_one".into(),
            test_function_info(LambdaClass::DeferIntroducing, di_lambda.clone()),
        );
        ctx.register_function(
            "doubles".into(),
            test_function_info(LambdaClass::DeferIntroducing, di_lambda),
        );
        // doubles(add_one(xs)) ≡ Apply(Apply(xs, add_one), doubles)
        let inner = Expr::apply(var("xs"), var("add_one"));
        let outer = Expr::apply(inner, var("doubles"));
        let (_wrapped, fresh) = wrap_di_calls_in_chain(outer, "y", &mut ctx);
        // One fresh defer for the inner DI (add_one).  The outer
        // (doubles) uses "y".
        assert_eq!(fresh.len(), 1, "one fresh defer for inner DI");
        assert!(fresh[0].starts_with("__floated_inner_"));
    }

    /// `capture_let_chain_prefix` collects `(name, bound_expr)` pairs
    /// for each `Let` at the head of an expression, stopping at the
    /// first non-`Let` node.
    #[test]
    fn capture_let_chain_prefix_walks_through_lets() {
        let body = Expr::let_bind("a", lit(1), Expr::let_bind("b", lit(2), var("c")));
        let prefix = capture_let_chain_prefix(&body);
        assert_eq!(prefix.len(), 2);
        assert_eq!(prefix[0].0, "a");
        assert_eq!(prefix[1].0, "b");
    }

    /// `wrap_with_let_prefix` reconstructs the let-chain around an inner expression.
    #[test]
    fn wrap_with_let_prefix_reverses_capture() {
        let prefix = vec![("a".into(), lit(1)), ("b".into(), lit(2))];
        let wrapped = wrap_with_let_prefix(&prefix, var("c"));
        // Expect: let a = 1 in let b = 2 in c
        let TypedExprNode::Let {
            binding: a_b,
            body: inner1,
            ..
        } = wrapped.node
        else {
            panic!()
        };
        assert_eq!(a_b.name, "a");
        let TypedExprNode::Let {
            binding: b_b,
            body: inner2,
            ..
        } = inner1.node
        else {
            panic!()
        };
        assert_eq!(b_b.name, "b");
        let TypedExprNode::Var(c) = inner2.node else {
            panic!()
        };
        assert_eq!(c, "c");
    }

    #[test]
    fn run_single_feed() {
        let body = Expr::expr_stmt(Expr::feed("d".into(), lit(1)), var("d"));
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(expr).unwrap();
        // After desugar: let __scope_out_d_0 = (Unit; Record({result: d, to_d: 1})) in
        //                let d = __scope_out_d_0.to_d in
        //                __scope_out_d_0.result
        let s = symbolic(&result);
        // After desugar: `unit; let d = (λ __unused → 1) in d` — the
        // scalar feed value is lifted to `Fun(Unit, T)` via the
        // `λ __unused → V` wrap, then bound to the defer name.
        assert!(s.contains("__unused"), "expected const-wrap in output: {s}");
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
        assert!(!s.contains("feed"), "no Feed should remain: {s}");
    }

    /// `let d = Defer in define(d, 42); d` — Define path: bind d to V directly.
    #[test]
    fn run_define_replaces_directly() {
        let body = Expr::expr_stmt(Expr::define("d".into(), lit(42)), var("d"));
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(expr).unwrap();
        let s = symbolic(&result);
        assert!(
            s.contains("42"),
            "expected 42 to appear in result, got: {s}"
        );
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
        assert!(!s.contains("define"), "no Define should remain: {s}");
    }

    /// `let d = Defer in <body without feeds>` — error.
    #[test]
    fn run_no_feed_is_error() {
        let body = var("d");
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let err = run(expr).unwrap_err();
        assert_eq!(err, DeferError::NoFeedOrDefine("d".into()));
    }

    /// Multiple feeds: union'd via collection_union.
    #[test]
    fn run_multiple_feeds_use_collection_union() {
        let body = Expr::expr_stmt(
            Expr::feed("d".into(), lit(1)),
            Expr::expr_stmt(Expr::feed("d".into(), lit(2)), var("d")),
        );
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(expr).unwrap();
        let s = symbolic(&result);
        assert!(
            s.contains("⊎") || s.contains("Union"),
            "should use union: {s}"
        );
    }

    // -----------------------------------------------------------------
    // `run`-boundary tests for the cluster algorithm, multi-feed Loop,
    // and filter-feed Case shapes.  These exercise the bulk of
    // `extract_for_defer` / `channelize_cluster` / `process_loop_for_defer`
    // / `rename_shadows_then_bind` without going through the full
    // pipeline.
    // -----------------------------------------------------------------

    /// Cluster of three defers where channels reference each other in a
    /// chain (`a` depends on `b` depends on `c`).  After desugar, the
    /// emitted let-chain must bind `c` before `b` before `a`
    /// (topological order), regardless of source order.
    #[test]
    fn run_three_defer_cluster_topo_sorted() {
        // ```
        // a = defer()
        // b = defer()
        // c = defer()
        // a <<= b
        // b <<= c
        // c <<= [0, 1]
        // a
        // ```
        let inner = Expr::expr_stmt(
            Expr::define("a".into(), var("b")),
            Expr::expr_stmt(
                Expr::define("b".into(), var("c")),
                Expr::expr_stmt(
                    Expr::define("c".into(), Expr::list(vec![lit(0), lit(1)])),
                    var("a"),
                ),
            ),
        );
        let with_c = Expr::let_bind("c", Expr::new(TypedExprNode::Defer), inner);
        let with_b = Expr::let_bind("b", Expr::new(TypedExprNode::Defer), with_c);
        let with_a = Expr::let_bind("a", Expr::new(TypedExprNode::Defer), with_b);
        let result = run(with_a).expect("topological resolution should succeed");
        let s = symbolic(&result);
        // The emitted chain should mention all three names; `c` is the
        // sink (depends on nobody), so it must come before `b`, which
        // must come before `a`.
        let pos_a = s.find("let a").expect("missing let a in output");
        let pos_b = s.find("let b").expect("missing let b in output");
        let pos_c = s.find("let c").expect("missing let c in output");
        assert!(pos_c < pos_b, "c must be bound before b: {s}");
        assert!(pos_b < pos_a, "b must be bound before a: {s}");
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
    }

    /// Mutually recursive defer cluster: `a <<= b; b <<= a` — an
    /// unsupported letrec.  Surfaces as `MutuallyRecursiveCycle`.
    #[test]
    fn run_mutual_cycle_is_error() {
        let inner = Expr::expr_stmt(
            Expr::define("a".into(), var("b")),
            Expr::expr_stmt(Expr::define("b".into(), var("a")), var("a")),
        );
        let with_b = Expr::let_bind("b", Expr::new(TypedExprNode::Defer), inner);
        let with_a = Expr::let_bind("a", Expr::new(TypedExprNode::Defer), with_b);
        let err = run(with_a).unwrap_err();
        assert!(
            matches!(err, DeferError::MutuallyRecursiveCycle(_)),
            "expected MutuallyRecursiveCycle, got {err:?}"
        );
    }

    /// A `Loop` body that feeds the same defer at two distinct sites
    /// must surface as two `to_<defer>_<k>` Record fields (one per
    /// site) plus an outer union of the two projections — neither feed
    /// can collide with the other.
    #[test]
    fn run_loop_with_two_feeds_emits_indexed_record_fields() {
        // λp → ExprStmt(Feed("d", 1),
        //      ExprStmt(Feed("d", 2),
        //        Record({step: Var(p)})))
        let inner_record = Expr::new(TypedExprNode::Record(vec![("step".into(), var("p"))]));
        let with_two_feeds = Expr::expr_stmt(
            Expr::feed("d".into(), lit(1)),
            Expr::expr_stmt(Expr::feed("d".into(), lit(2)), inner_record),
        );
        let body_lambda = Expr::lambda("p", Type::Hole, with_two_feeds);
        let loop_expr = Expr::loop_node(
            vec!["acc".into()],
            vec![lit(0)],
            Expr::list(vec![lit(10), lit(20)]),
            body_lambda,
        );
        // ```
        // let d = Defer in
        // let stream = Loop { body Feeds d twice } in
        // stream
        // ```
        // The defer is bound *outside* the loop's let so the loop's
        // body is in `d`'s scope; the cluster algorithm walks the
        // `let stream = Loop` binding via `extract_for_defer`'s
        // Let-of-Loop special case, which delegates to
        // `process_loop_for_defer`.
        let with_stream = Expr::let_bind("stream", loop_expr, Expr::var("stream"));
        let with_d = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), with_stream);
        let result = run(with_d).expect("loop-with-two-feeds should desugar");
        let s = symbolic(&result);
        assert!(s.contains("to_d_0"), "missing to_d_0 field: {s}");
        assert!(s.contains("to_d_1"), "missing to_d_1 field: {s}");
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
        assert!(!s.contains("feed"), "no Feed should remain: {s}");
    }

    /// Three-arm Case (so the `try_extract_filter_feed` two-arm
    /// shortcut doesn't fire) where only one arm feeds — exercises
    /// the general Case-arm fan-out path that calls
    /// [`empty_channel`] for the non-feeding arms.  Verifies the
    /// desugar pass eliminates Defer/Feed and emits each non-feeding
    /// arm's `to_d` field as the [`empty_channel`] sentinel.
    #[test]
    fn run_case_branch_fan_out_emits_empty_channel_for_no_feed_arms() {
        let guard = Expr::new(TypedExprNode::BinOp {
            left: Box::new(var("x")),
            op: BinOpKind::Compare(crate::ccl::CompareKind::Greater),
            right: Box::new(lit(0)),
        });
        let feeding_arm = Branch {
            pattern: None,
            guard,
            body: Expr::feed("d".into(), var("x")),
        };
        let unrelated_arm = Branch {
            pattern: None,
            guard: Expr::lit(Lit::Bool(false)),
            body: Expr::lit(Lit::Unit),
        };
        let true_arm = Branch {
            pattern: None,
            guard: Expr::lit(Lit::Bool(true)),
            body: Expr::lit(Lit::Unit),
        };
        let case_expr = Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: vec![feeding_arm, unrelated_arm, true_arm],
        });
        let body_lambda = Expr::lambda("x", Type::Hole, case_expr);
        let source = Expr::list(vec![lit(1), lit(-1), lit(2)]);
        let apply = Expr::apply(source, body_lambda);
        let with_d = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), apply);
        let result = run(with_d).expect("case-branch feed should desugar");
        let s = symbolic(&result);
        // After desugar each arm publishes a Record({result, to_d: …}).
        assert!(s.contains("to_d"), "expected to_d field in output: {s}");
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
        assert!(!s.contains("feed"), "no Feed should remain: {s}");
    }

    // -----------------------------------------------------------------
    // `collect_free_vars` — type-position refinement traversal
    // -----------------------------------------------------------------

    /// `collect_free_vars` must descend into `user_annotation`
    /// refinement predicates.  Otherwise filter-feed channels (which
    /// stash a `Refinement(_, pred)` in `user_annotation`) hide their
    /// outer-let references from [`compute_protected_set`], and a
    /// downstream shadow goes undetected.
    #[test]
    fn collect_free_vars_descends_into_user_annotation_predicates() {
        // Build a trivial channel whose `user_annotation` carries a
        // predicate referencing `outer_n`:
        //   `Var("__chan")` with user_annotation = Fun(Refinement(Hole, pred(outer_n)), Hole)
        let pred = var("outer_n");
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(Rc::new(RefCell::new(pred))),
        };
        let annotated = TypedExpr {
            node: TypedExprNode::Var("__chan".to_string()),
            ty: Type::Hole,
            user_annotation: Some(Type::fun(
                Type::Refinement(Box::new(Type::Hole), refinement),
                Type::Hole,
            )),
        };

        let mut free: HashSet<String> = HashSet::new();
        collect_free_vars(&annotated, &mut free);
        assert!(
            free.contains("outer_n"),
            "user_annotation predicate reference should be collected: got {free:?}"
        );
        // The expression node itself names `__chan` — also collected.
        assert!(
            free.contains("__chan"),
            "expr node Var was missed: {free:?}"
        );
    }

    /// `collect_free_vars` must descend into `expr.ty` refinement
    /// predicates (the type slot, not just `user_annotation`).
    #[test]
    fn collect_free_vars_descends_into_ty_refinement_predicates() {
        let pred = var("inner_k");
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(Rc::new(RefCell::new(pred))),
        };
        let typed = TypedExpr {
            node: TypedExprNode::Lit(Lit::Unit),
            ty: Type::Fun(
                Box::new(Type::Refinement(Box::new(Type::Hole), refinement)),
                Box::new(Type::Hole),
            ),
            user_annotation: None,
        };
        let mut free: HashSet<String> = HashSet::new();
        collect_free_vars(&typed, &mut free);
        assert!(
            free.contains("inner_k"),
            "expr.ty predicate reference should be collected: got {free:?}"
        );
    }

    /// `collect_free_vars` must descend into a Lambda's
    /// [`TypedExprNode::Lambda::refinement`] (the dedicated refinement
    /// slot, not via type).  References inside the refinement live in
    /// the *outer* scope (the lambda hasn't bound its param yet), so
    /// they must be visited before the param-shadow is pushed.
    #[test]
    fn collect_free_vars_descends_into_lambda_refinement() {
        // Build `λ x with {refinement: outer_k} → x`, then check that
        // `collect_free_vars` sees both `outer_k` and *not* `x` (x is
        // bound by the lambda).
        let pred = var("outer_k");
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(Rc::new(RefCell::new(pred))),
        };
        let lambda = TypedExpr {
            node: TypedExprNode::Lambda {
                param: crate::ccl::TypedBinding {
                    name: "x".to_string(),
                    ty: Type::Hole,
                    user_annotation: None,
                },
                body: Box::new(var("x")),
                refinement: Some(refinement),
            },
            ty: Type::Hole,
            user_annotation: None,
        };
        let mut free: HashSet<String> = HashSet::new();
        collect_free_vars(&lambda, &mut free);
        assert!(
            free.contains("outer_k"),
            "Lambda::refinement reference should be collected: got {free:?}"
        );
        assert!(
            !free.contains("x"),
            "param `x` should be shadowed inside its lambda body: got {free:?}"
        );
    }
}

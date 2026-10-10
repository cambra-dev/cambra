//! Feed channelization — the feed-routing step of the unified phase.
//!
//! Eliminates `Defer`/`Feed`/`Define`/`ExprStmt` nodes by assembling each
//! `defer` channel from its `<<` / `<<=` contributions and emitting each
//! cluster of defers as one **mutually-scoped `Feed`-kind `LetRec` group** —
//! the model's "feeds are the letrec's outputs" — so cross-channel references
//! (`x <<= y`) need no binding order and a reference *cycle* among channels is
//! rejected by the letrec causality rule (channels carry no guard, so a
//! cycle has no well-founded solution). Recognition later flattens the acyclic
//! group to dependency-ordered `let`s.
//!
//! Runs **immediately after [`crate::ccl::mut_elim::run`]** in
//! [`crate::ccl::context::compile_program`], on a typed, inlined tree — but
//! *before* `lambda_elim` and `planning::plan_loops` (recognition consumes
//! the point-free normal form post-elim, so both mutable-variable and channel letrec
//! groups travel through this step and elimination intact). The phase has
//! already hoisted every in-loop feed out of its recurrence as a loop over the tap it
//! rode, `for x in tap: defer << x` ([`crate::ccl::mut_elim::hoist_feeds`]), so
//! channelization is **origin-agnostic**: it never distinguishes an accumulator-loop
//! feed from a feed-only-loop or scalar feed.
//!
//! Inference checks defer constructs on the user-shaped tree; channelization
//! validates the channel shapes it consumes. For the history constraint rules,
//! see `design/type-inference.md`, "Feed handles as invariant histories".
//!
//! **Type-preserving by construction.** Every channel node this module builds is
//! stamped with its concrete type from its children (mirroring how
//! [`crate::ccl::mut_elim`] emits a well-typed `LetRec`). The one residue
//! that construction cannot know up front — the channel *domains* — is named
//! rigidly at inference ([`Type::ChanDom`], minted per `let d = Defer`), so a
//! defer read and every node that consumes one (`d ++ d`, `sum(d)`, the trailing
//! spine) types *concretely* against the rigid name, with no `Infer` residue.
//! Closing the tree is then the pure whole-tree substitution
//! [`erase_chan_domains`] — map each `ChanDom(d)` to its assembled channel's
//! concrete domain and erase each `Feed`-kind history to its bare `Fun` — the
//! exact feed-side analog of `mut_elim::erase_mut`. There is no re-typing
//! pass; the strict post-channelization `typecheck` in `compile_program`
//! backstops the invariant.
//!
//! After this step, no [`TypedExprNode::Defer`], [`TypedExprNode::Feed`],
//! [`TypedExprNode::Define`], or [`TypedExprNode::ExprStmt`] nodes — and no
//! `Feed`/`Hole`/`Infer` types — remain in the tree; every downstream pass treats
//! those variants as `unreachable!`.
//!
//! A feed under nested loops is keyed by the tuple of the loops' positions
//! (`docs/chl-spec.md`, "8.4 Feeds are the second form of mutability"). Where no loop's source
//! reads an enclosing loop, the contribution is rebuilt over the product of the loops'
//! positions ([`nest_as_product`]); otherwise its levels are uncurried into the tuple
//! ([`flatten_nested_contribution`]). How many levels are positions is the number of loops
//! the walk crossed to reach the feed ([`Contribution`]), never read off a type. Each
//! contribution is recorded as the product of the `Feed` it came from (`channelize.feed`).
//!
//! A loop-sourced multi-arm feed `Case` — an `if`/`elif` chain or a `match` —
//! fans out into one refined-source channel per feeding arm
//! ([`try_extract_fanout_feed`]). One `Case` fans out once per deferred collection
//! it feeds, and each pass leaves the arms it did not take for the pass that will
//! ([`residual_after_fanout`]), so two defers fed from complementary arms are two
//! channels over one conditional. A feeding `Case` outside any iteration becomes a
//! gated one-shot lift when its arms are guards; only a scrutinee / pattern one is
//! rejected, with `DeferError::PartialFeedCaseUnsupported` (see the `Case` arm of
//! [`extract_for_defer`]).
//!
//! # Vocabulary
//!
//! Throughout this module, a **channel** is the expression that
//! resolves a deferred binding: the value the cluster's let-wrap
//! ultimately binds to `d_i`.  For a single `<<` feed the channel is
//! that feed's value, lifted to `Fun(Unit, T)` at top level whatever `T`
//! is; for multiple feeds it is their `++`-union; for feeds
//! inside an iteration scope it is the companion `Apply`/`Compose`/
//! `Loop` that mirrors the iteration shape and yields the feed value
//! instead of `Unit`.
//!
//! # Transformation (cluster algorithm)
//!
//! For a cluster of consecutive `let d_i = Defer in …` bindings,
//! `channelize_expr` performs three steps:
//!
//! 1. **Feed extraction.**  Walk the cluster body and collect every
//!    `Feed(d_i, V)` / `Define(d_i, V)` plus the iteration context
//!    they sit in (Compose/Apply/Loop/Case), producing a channel
//!    expression for each `d_i`.
//! 2. **Channel assembly.**  Combine multiple feeds per defer via
//!    `++` ([`TypedExprNode::Copair`]); lift scalar feeds
//!    to `Fun(Unit, T)`; emit refined-source channels for filter-feed
//!    Case shapes.
//! 3. **Topological emission.**  Emit the cluster's `let d_i =
//!    <channel_i> in …` bindings at the cluster wrap site in
//!    topological order — a defer whose channel references another
//!    cluster defer is bound *after* the one it references
//!    ([`bind_cluster_at_scope`]).
//!
//! There is deliberately no α-renaming step: uniquification runs before
//! channelization, so a channel's captured free variable can never be shadowed
//! by a `Let` on the wrap-to-feed spine (a body binder and a captured outer
//! variable never share a `uid`). [`assert_no_shadowed_captures`] enforces this
//! in debug builds.
//!
//! ## Cross-cluster sequencing
//!
//! Defers separated by intervening non-`Defer` lets (`let d_1 = D in
//! let z = E in let d_2 = D in …`) form *separate* clusters.  Each
//! is processed innermost-first.  When the outer cluster's
//! [`bind_cluster_at_scope`] walks the post-inner-processing chain
//! and finds a `Let` whose `bound_expr` references one of its own
//! cluster names, the outer cluster's bindings are emitted at that
//! `Let`'s position rather than at the body's terminal — so a defer
//! is always bound before any expression that mentions it.
//!
//! # Where to read more
//!
//! `src/ccl/design/mutability.md` ("Compilation pipeline") is the design
//! of record for this step and where it sits in the unified phase. The
//! function-level docs in this file explain individual moving parts (the cluster
//! channelization algorithm, per-shape extraction paths, defer-returning lift,
//! alias inlining, error modes); this module comment is the entry point.

use std::collections::{HashMap, HashSet};
use std::fmt;

use std::rc::Rc;

use crate::ccl::ccl_utils::{
    PredMemo, cast_target_refinement, make_cast, walk_refined_predicates,
    walk_refined_predicates_mut,
};
use crate::ccl::{
    BaseType, BindingTransparency, Branch, Builtin, Expr, FunKind, HistoryKind, Lit, Name, Pattern,
    PredicateId, Refinement, Type, TypedBinding, TypedExpr, TypedExprNode,
    ccl_utils::{apply_primitive, count_free, synthesize_arm_predicate, typed_compose, unit_expr},
    letrec::check_letrec_causal,
    provenance::{self, Located, NodeId},
};

/// A **channel type**, which this pass is the one that erases: a nominal channel
/// domain, or the `Feed` history the defer elimination dissolves.
fn is_channel_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::ChanDom(..)
            | Type::History {
                history_kind: HistoryKind::Append,
                ..
            }
    )
}

/// A type node that must not survive channelization: a channel type, or a `Hole` /
/// `Infer` stamped on a node this pass constructed or invalidated.
#[cfg(debug_assertions)]
fn is_type_residue(ty: &Type) -> bool {
    matches!(ty, Type::Hole | Type::Infer(_)) || is_channel_type(ty)
}

/// `true` when `ty` carries channelization-erasable residue anywhere in it.
///
/// [`slot_holds_type`] is the read-only mirror of [`erase_chan_domains_in_slot`], so the
/// checker reaches exactly what the eraser is answerable for: type structure and the
/// refinement predicates hanging off it.
///
/// Debug-only: its sole consumer is the `assert_no_type_residue` invariant
/// walk (the strict `typecheck` wall is the release-visible enforcement).
#[cfg(debug_assertions)]
fn has_type_residue(ty: &Type) -> bool {
    slot_holds_type(ty, &is_type_residue, &mut HashSet::new())
}

/// Errors that can arise while channelizing `Defer`/`Feed`/`Define` nodes.
#[derive(Debug, PartialEq)]
pub enum DeferError {
    /// A deferred binding had no corresponding `Feed` or `Define` in its scope.
    NoFeedOrDefine(Name),
    /// A deferred binding had more than one `Define` in its scope.
    MultipleDefinitions(Name),
    /// Both `Feed` and `Define` were found for the same deferred binding.
    FeedsAndDefinesMixed(Name),
    /// A `Define` appeared inside a context where it is not allowed
    /// (e.g. inside a Loop body, Compose element, or Case branch).
    NestedDefinition(Name),
    /// A `Feed` references a defer-handle that was never bound by a
    /// surrounding `let d = Defer`.
    UnboundDeferHandle(Name),
    /// A cluster of defers has channels that reference each other
    /// cyclically (e.g. `x ≪= y; y ≪= x`). Channels are `Feed`-kind letrec
    /// bindings and carry no `get_prev_*` guard, so a cycle has no
    /// well-founded solution — rejected by the letrec causality rule
    /// ([`crate::ccl::letrec::check_letrec_causal`]), the same law that
    /// governs overwrite recursion. The payload names one of the defers on the
    /// cycle.
    MutuallyRecursiveCycle(Name),
    /// A feeding `Case` reached the generic structural recursion — a
    /// conditional feed with no enclosing iteration source to restrict per arm
    /// (the loop-sourced multi-arm case is fanned out at the `Compose` site via
    /// [`try_extract_fanout_feed`]). A guard-only one becomes a gated one-shot
    /// lift there, over a `{Unit | π̂ᵢ}` driver; a scrutinee / pattern feed
    /// cannot be gated by a boolean predicate, so it is rejected rather than
    /// miscompiled. The payload names the defer.
    PartialFeedCaseUnsupported(Name),
}

impl fmt::Display for DeferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeferError::NoFeedOrDefine(name) => {
                let name = name.base();
                write!(f, "deferred binding '{name}' has no feed or define")
            }
            DeferError::MultipleDefinitions(name) => {
                let name = name.base();
                write!(f, "deferred binding '{name}' has multiple definitions")
            }
            DeferError::FeedsAndDefinesMixed(name) => {
                let name = name.base();
                write!(f, "deferred binding '{name}' has both feeds and a define")
            }
            DeferError::NestedDefinition(_) => {
                write!(f, "<<= must occur as a top-level statement")
            }
            DeferError::UnboundDeferHandle(name) => {
                let name = name.base();
                write!(f, "feed/define references unbound defer handle '{name}'")
            }
            DeferError::MutuallyRecursiveCycle(name) => {
                let name = name.base();
                write!(
                    f,
                    "deferred bindings form a mutually recursive cycle through '{name}'"
                )
            }
            DeferError::PartialFeedCaseUnsupported(name) => {
                let name = name.base();
                write!(
                    f,
                    "deferred binding '{name}' is fed from some but not all branches of a \
                     multi-way conditional; this shape is not supported yet"
                )
            }
        }
    }
}

impl DeferError {
    /// The deferred binding the error is about.
    fn defer(&self) -> &Name {
        match self {
            DeferError::NoFeedOrDefine(name)
            | DeferError::MultipleDefinitions(name)
            | DeferError::FeedsAndDefinesMixed(name)
            | DeferError::NestedDefinition(name)
            | DeferError::UnboundDeferHandle(name)
            | DeferError::MutuallyRecursiveCycle(name)
            | DeferError::PartialFeedCaseUnsupported(name) => name,
        }
    }
}

/// What is left of a fanned-out `Case` once `defer_name`'s feeds are extracted: the
/// same `Case` with that defer's feed arms replaced by `Unit`, and every other arm
/// left alone.
///
/// Collapsing the whole body to `Unit` instead drops a sibling defer's feeds, which
/// the cluster reports as [`DeferError::NoFeedOrDefine`].
///
/// Rebuilt from the **original** body rather than from the guard form
/// [`try_extract_fanout_feed`] matched on, so a `match` keeps its scrutinee and its
/// arm patterns for the next pass to convert at its own consumption point.
///
/// The `Case`'s own type carries across the swap: a `Feed` types as `Unit`
/// ([`crate::ccl::infer::emit`], the `Feed` rule), so replacing one with `unit` leaves
/// every arm at the type the `Case` already has.
///
/// Takes the body by value. The caller drops it, and [`Clone for TypedExpr`] mints a
/// fresh id per node, so a clone would re-identify the whole residual once per defer.
fn residual_after_fanout(body: Expr, defer_name: &Name) -> Expr {
    let TypedExpr {
        node: TypedExprNode::Case {
            scrutinee,
            branches,
        },
        ty,
        user_annotation,
        node_id,
    } = body
    else {
        unreachable!(
            "residual_after_fanout: the caller reached here through \
             `try_extract_fanout_feed`, which destructures a `Case`"
        )
    };
    let branches = branches
        .into_iter()
        .map(|b| Branch {
            body: match &b.body.node {
                TypedExprNode::Feed { name, .. } if name == defer_name => unit_expr(),
                _ => b.body,
            },
            pattern: b.pattern,
            guard: b.guard,
        })
        .collect();
    TypedExpr {
        node: TypedExprNode::Case {
            scrutinee,
            branches,
        },
        ty,
        user_annotation,
        node_id,
    }
}

/// Recognize a guard-only `Case` that feeds `defer_name` in one or more arms —
/// the channelize-stage counterpart of `lambda_elim`'s `is_filter_case_body`.
///
/// Shape (as lowered from `if g₀: d << v₀ elif g₁: d << v₁ … [else: d << vₑ]` in
/// a for-loop body): `Case { None, [g₀ → body₀; …; true → bodyₜ] }`, where each
/// `bodyᵢ` is either `Feed(defer_name, vᵢ)` (a feeding arm) or `Unit` (a
/// non-feeding arm). The trailing `true`-guarded arm is the `else` body when
/// present (a feed) or the implicit fallthrough (`Unit`) when absent — both are
/// ordinary arms here, so an `else` that feeds fans out just like a guard arm
/// (its first-match predicate is `¬⋁ⱼ gⱼ`).
///
/// **An arm feeding another deferred collection is a non-feeding arm here**, which is
/// what leaves `if c: good << i else: bad << i` fannable for either defer.
///
/// Returns each arm's `(guard, feed_value?)` in source order — `feed_value` is
/// `None` for a non-feeding arm, whose guard still participates in later arms'
/// predicate synthesis ([`synthesize_arm_predicate`]). Returns `None` (not
/// fannable) if the trailing guard is not `true` or an arm body is neither a feed
/// nor `Unit`.
///
/// A `None` on a loop-sourced `Case` has no clean rejection behind it. The generic
/// handling has no iteration source, so it gates on `Unit` with a predicate over the
/// loop binder, and the program then dies in compiler internals rather than on a
/// diagnostic: [`DeferError::PartialFeedCaseUnsupported`] for a `match`, naming the
/// wrong cause, and for an `if` either lambda elimination's rejection of the gate's
/// dependent codomain or, when an arm body is itself a conditional, an inference abort
/// naming an inference variable with no source span. Reaching the generic handling from
/// a loop is therefore a defect wherever it happens, not a fallback.
fn try_extract_fanout_feed(body: &Expr, defer_name: &Name) -> Option<Vec<(Expr, Option<Expr>)>> {
    // A `match` arm dispatches on a tag, so it reaches the fan-out as a
    // `Pattern` against a scrutinee. Convert it to the guard form first — the
    // same rewrite the induction writer applies at its own consumption point —
    // and match on the result, so the arms below are guards either way.
    let converted = matches!(
        &body.node,
        TypedExprNode::Case {
            scrutinee: Some(_),
            ..
        }
    )
    .then(|| crate::ccl::ccl_utils::tag_case_to_guard_case(body.clone()));
    let TypedExprNode::Case {
        scrutinee: None,
        branches,
    } = &converted.as_ref().unwrap_or(body).node
    else {
        return None;
    };
    if branches.len() < 2 {
        return None;
    }
    // The trailing arm is the fallthrough / `else` — its guard must be `true`.
    if !matches!(
        &branches.last().expect("len >= 2").guard.node,
        TypedExprNode::Lit(Lit::Bool(true))
    ) {
        return None;
    }
    let mut arms = Vec::with_capacity(branches.len());
    let mut any_feed = false;
    for b in branches {
        // A guard-only arm never binds a pattern.
        if b.pattern.is_some() {
            return None;
        }
        match &b.body.node {
            TypedExprNode::Feed { name, value } if name == defer_name => {
                any_feed = true;
                arms.push((b.guard.clone(), Some((**value).clone())));
            }
            // Another defer's feed, and `Unit`: neither contributes a value to this
            // defer's channel, and both leave their guard in the predicate synthesis.
            TypedExprNode::Feed { .. } | TypedExprNode::Lit(Lit::Unit) => {
                arms.push((b.guard.clone(), None))
            }
            _ => return None,
        }
    }
    any_feed.then_some(arms)
}

/// The defer-returning lift's output.
struct DeferLift {
    /// `let y = Defer in …` — the two defer scopes merged into one.
    expr: Expr,
    /// The inner defer binder, which the lift renamed to the outer name.
    inner_name: Name,
    /// The channel domain of the inner handle the lift replaced, when its type
    /// records one.
    inner_chan_dom: Option<(Name, crate::ccl::ChanLevel)>,
}

/// Whether `bound_expr` has the defer-returning lift's shape: any `ExprStmt`
/// prefix, then `let x = Defer in body_x` with `body_x` defer-returning.
///
/// [`lift_defer`] consumes its input, so the shape is decided here first. A
/// matcher that failed partway through would have to rebuild what it had already
/// taken apart, or work on a copy.
fn is_lift_shape(bound_expr: &Expr) -> bool {
    let mut current = bound_expr;
    while let TypedExprNode::ExprStmt { body, .. } = &current.node {
        current = body;
    }
    matches!(
        &current.node,
        TypedExprNode::Let { binding, bound_expr: inner_be, body }
            if matches!(inner_be.node, TypedExprNode::Defer)
                && is_defer_returning(body, &binding.name)
    )
}

/// Apply the defer-returning lift to a `Let` binding whose `bound_expr` has
/// passed [`is_lift_shape`].
///
/// Pattern: `let y = (let x = Defer in body_x) in body_y` where
/// `body_x` is *defer-returning* (ends in `Var(x)` after walking
/// through any `ExprStmt`/`Let` chains).
///
/// Rewrites to: `let y = Defer in body_x[x → y] with Var(y) replaced
/// by body_y`.  The substitution `x → Var(y)` is done via
/// [`channelize_substitute`], which also renames the *target* name of
/// `Feed`/`Define` nodes when the replacement is a `Var` — so
/// `Feed("x", …)` becomes `Feed("y", …)` automatically.
///
/// Also handles an optional `ExprStmt` prefix on `bound_expr`: the
/// heads of any leading ExprStmts become a prefix that's prepended to
/// the lifted body, with stale Feed/Define target names renamed to `y`.
fn lift_defer(binding_name: &Name, bound_expr: Expr, body: &Expr) -> DeferLift {
    let mut prefix: Vec<Expr> = Vec::new();
    let mut current = bound_expr;
    loop {
        match current.node {
            TypedExprNode::ExprStmt {
                expr: head,
                body: tail,
            } => {
                prefix.push(*head);
                current = *tail;
            }
            // Put the node back on the expression the match moved it out of; the
            // spine ends here.
            node => {
                current.node = node;
                break;
            }
        }
    }
    let TypedExprNode::Let {
        binding: inner_binding,
        bound_expr: inner_be,
        body: inner_body,
    } = current.node
    else {
        unreachable!("`lift_defer` requires the `is_lift_shape` shape")
    };
    debug_assert!(
        matches!(inner_be.node, TypedExprNode::Defer)
            && is_defer_returning(&inner_body, &inner_binding.name),
        "`lift_defer` requires the spine to end in `let x = Defer in body_x` with a \
         defer-returning `body_x` — check `is_lift_shape` first"
    );
    // Read the inner handle's channel domain off the binding this lift replaces:
    // the entry the caller records has to key on the domain name consumer types
    // carry, which for a specialization clone differs from the term binder name.
    let inner_chan_dom =
        handle_chan_dom(&inner_binding.ty).or_else(|| handle_chan_dom(&inner_be.ty));
    // Keep the inner defer's recorded handle type (`feed(ChanDom(F) ⤇ V)`) — the
    // lifted binding must carry it so cluster discovery keys the channel by the
    // domain name consumer types reference, not by the term name. (`Hole` on an
    // untyped tree, harmlessly.)
    let (inner_name, inner_handle_ty, inner_body_x) =
        (inner_binding.name, inner_be.ty, *inner_body);

    // `body_x[x → y]` — also renames Feed/Define targets named `x` to `y`.
    let inner_subst = channelize_rename(inner_body_x, &inner_name, binding_name);

    // Wrap `body_y` with the prefix (renaming stale feed targets to `y`).
    let mut new_outer_body = body.clone();
    for head in prefix.into_iter().rev() {
        let renamed_head = match head.node {
            TypedExprNode::Feed { name: _, value } => TypedExpr {
                ty: head.ty,
                node: TypedExprNode::Feed {
                    name: binding_name.clone(),
                    value,
                },
                user_annotation: None,
                // Preserve: the lifted prefix head is the same node with its
                // feed target renamed, so carry its id onto the rebuild.
                // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                node_id: head.node_id,
            },
            TypedExprNode::Define { name: _, value } => TypedExpr {
                ty: head.ty,
                node: TypedExprNode::Define {
                    name: binding_name.clone(),
                    value,
                },
                user_annotation: None,
                // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                node_id: head.node_id,
            },
            _ => head,
        };
        new_outer_body = Expr::expr_stmt(renamed_head, new_outer_body);
    }
    // Splice `new_outer_body` in at the trailing `Var(y)` of
    // `inner_subst`, so the lifted body comes BEFORE the original outer
    // body (preserving execution order: inner-then-outer).
    let spliced = replace_result_var(inner_subst, new_outer_body);

    // Rebuild the lifted let type-preservingly: the `Defer` node (and, via
    // `let_bind`, the binding slot) carries the inner handle type, and the
    // `Let` node itself the body's type.
    let out_ty = spliced.ty.clone();
    let mut defer_node = Expr::new(TypedExprNode::Defer);
    defer_node.ty = inner_handle_ty;
    let mut lifted = Expr::let_bind(binding_name, defer_node, spliced);
    lifted.ty = out_ty;
    DeferLift {
        expr: lifted,
        inner_name,
        inner_chan_dom,
    }
}

/// Return `true` if `expr` ends in `Var(name)` after walking through
/// any leading `ExprStmt`/`Let` chains (the body's terminal position).
fn is_defer_returning(expr: &Expr, name: &Name) -> bool {
    match &expr.node {
        TypedExprNode::Var(n) => n == name,
        TypedExprNode::ExprStmt { body, .. } => is_defer_returning(body, name),
        TypedExprNode::Let { binding, body, .. } => {
            &binding.name != name && is_defer_returning(body, name)
        }
        _ => false,
    }
}

/// Replace the trailing `Var(_)` at the terminal of `expr` (walking
/// through `ExprStmt`/`Let` chains) with `replacement`.
///
/// Every spine node on the way takes its **type from the new terminal**: a
/// statement's type is its body's, so a spine whose terminal is swapped for a
/// value of another type has a stale type at every node above the swap. The
/// stale type outlives channelization — a `let` that carried the lifted
/// defer's handle type still claims it over a body that now ends in the
/// program's result — and surfaces as an `Expected function type` at the
/// letrec-recognition typecheck rather than here.
///
/// Caller is responsible for ensuring `expr` actually ends in a
/// `Var` (e.g. via [`is_defer_returning`]).
fn replace_result_var(expr: Expr, replacement: Expr) -> Expr {
    let TypedExpr {
        node,
        ty: _,
        user_annotation,
        node_id,
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
    let ty = match &new_node {
        TypedExprNode::ExprStmt { body, .. } | TypedExprNode::Let { body, .. } => body.ty.clone(),
        _ => unreachable!("only the two spine arms above reach here"),
    };
    TypedExpr {
        node: new_node,
        ty,
        user_annotation,
        node_id,
    }
}

/// Return `true` if `expr` contains a `Defer` node anywhere
/// (transitively).
fn contains_defer(expr: &Expr) -> bool {
    matches!(expr.node, TypedExprNode::Defer) || expr.any_child(contains_defer)
}

/// What one feed contributes to its channel: the values it feeds, keyed by the positions of
/// the loops around it, curried one collection level per loop, outermost first. `levels`
/// counts those loops as the walk crosses them ([`extract_for_defer`]): 0 for a fed value
/// still inside its loop's body, and a feed outside every loop is keyed by the unit, one
/// level. The count is the structure's, so no type has to say which of the value's levels are
/// positions and which are the fed value's own.
struct Contribution {
    value: Expr,
    levels: usize,
    /// The `Feed` this contribution is what became of, which records each node built
    /// around it as its product.
    feed: NodeId,
}

/// A feed contribution flattened to one entry per position it was fed at.
///
/// `<<` appends at the site it is written, so a feed inside a loop contributes one value
/// per position of that loop — which is what the loop's tap holds. Inside a **nest** the
/// enclosing tap holds the inner loop's whole tap collection per enclosing position, one
/// level per level the feed sits under, so the contribution arrives curried. Flattening
/// each of those levels away is what makes the channel the innermost positions rather than
/// the groups they fall into.
///
/// `levels` is the number of loops the feed sits under, so the contribution's outer `levels`
/// collection levels are positions. A fed value may hold collections of its own, beneath
/// those: `out << [[1, 2], [3]]` appends a collection of collections whole, so nothing of it
/// is flattened.
pub(crate) fn flatten_nested_contribution(mut value: Expr, levels: usize) -> Expr {
    for level in 0..levels.saturating_sub(1) {
        let Levels {
            outer_name,
            outer,
            inner_name,
            keys,
            elem,
        } = outer_levels(&value.ty);
        let paired = keyed_by(
            vec![
                (outer_name.clone(), outer.clone()),
                (inner_name.clone(), keys.clone()),
            ],
            elem.clone(),
        );
        value = apply_primitive(value, Builtin::Uncurry, paired.clone());
        // Past the first level the outer key is the tuple this loop built, and it is spliced
        // open: a feed under three loops is keyed by the three positions, not by a pair of a
        // pair and a position (`docs/chl-spec.md`, "8.4 Feeds are the second form of
        // mutability"). A loop's own key that is a tuple stays one; only the position this
        // flattening paired is spliced.
        if level > 0 {
            let flat = spliced(outer_name.as_ref(), &outer, inner_name, keys, elem);
            let positions = Expr::list(vec![
                Expr::lit(Lit::Int(0)).with_ty(Type::Base(BaseType::Int)),
            ])
            .with_ty(Type::data_fun(
                Type::UIntRange(1),
                Type::Base(BaseType::Int),
            ));
            let flatten = apply_primitive(
                positions,
                Builtin::FlattenDomain,
                Type::fun(paired, flat.clone()),
            );
            value = crate::ccl::ccl_utils::apply_function(value, flatten, flat);
        }
    }
    value
}

/// The two outer collection levels of a contribution, `(𝑘₀ : 𝐴) ⤇ (𝑘₁ : 𝐾) ⤇ 𝐸`, opened
/// by name: `keys` (`𝐾`) may read `outer_name`, and `elem` (`𝐸`) both names. An inner loop
/// whose positions depend on the outer loop's value is the case where `𝐾` reads `𝑘₀`.
struct Levels {
    outer_name: Option<Name>,
    outer: Type,
    inner_name: Option<Name>,
    keys: Type,
    elem: Type,
}

fn outer_levels(ty: &Type) -> Levels {
    let Type::Fun {
        fun_kind: FunKind::Data(_),
        name: outer_name,
        domain: outer,
        codomain: inner,
    } = ty.peel_refinements()
    else {
        unreachable!("a contribution has a collection level per loop it was fed under")
    };
    let inner = crate::ccl::subst::open_codomain(ty, inner);
    let Type::Fun {
        fun_kind: FunKind::Data(_),
        name: inner_name,
        domain: keys,
        codomain: elem,
    } = inner.peel_refinements()
    else {
        unreachable!("a contribution has a collection level per loop it was fed under")
    };
    Levels {
        outer_name: outer_name.clone(),
        outer: (**outer).clone(),
        inner_name: inner_name.clone(),
        keys: (**keys).clone(),
        elem: crate::ccl::subst::open_codomain(inner.peel_refinements(), elem),
    }
}

/// The collection `(key : (𝑐₀ : 𝐶₀) × … × 𝐶ₙ) ⤇ 𝐸` over the telescope `components`, with
/// `elem`'s reads of each component name `𝑐ᵢ` read as `key.𝑖`. Where no component reads an
/// earlier one the key is the plain tuple ([`Type::dep_tuple`]), and where `elem` reads none
/// the function is unnamed.
fn keyed_by(components: Vec<(Option<Name>, Type)>, elem: Type) -> Type {
    let tuple = Type::dep_tuple(components.clone());
    let key = Name::fresh("__key");
    // A projection binds the key, which its component can read.
    let project = |index: usize, component: &Type| {
        Expr::apply(
            Expr::var(&key).with_ty(tuple.clone()),
            Expr::proj_index(index).with_ty(Type::pi(
                key.clone(),
                tuple.clone(),
                component.clone(),
            )),
        )
        .with_ty(component.clone())
    };
    let elem = components
        .iter()
        .enumerate()
        .filter_map(|(index, (name, _))| Some((index, name.clone()?)))
        .fold(elem, |elem, (index, name)| {
            let component = tuple
                .component_type(index, project)
                .expect("a telescope has a component per name");
            crate::ccl::subst::Subst::discharge(name, project(index, &component)).apply_type(&elem)
        });
    if crate::ccl::subst::codomain_depends_on(&key, &elem) {
        Type::pi_kinded(key, tuple, elem, FunKind::Data(None))
    } else {
        Type::data_fun(tuple, elem)
    }
}

/// The collection over `outer`'s components followed by `keys`, where `outer` is the tuple of
/// positions an earlier level built and `outer_name` the binder `keys` and `elem` read it
/// through: each read `outer_name.𝑗` becomes the spliced key's component `𝑗`
/// (`src/ccl/design/type-inference.md`, "Flattening").
fn spliced(
    outer_name: Option<&Name>,
    outer: &Type,
    inner_name: Option<Name>,
    mut keys: Type,
    mut elem: Type,
) -> Type {
    let prefix: Vec<(Option<Name>, Type)> = match outer {
        Type::Tuple(ts) => ts.iter().map(|t| (None, t.clone())).collect(),
        Type::DepTuple(cs) => cs.clone(),
        other => unreachable!("the level above was flattened to a tuple, got {other}"),
    };
    let names = crate::ccl::subst::tuple_component_names(&prefix);
    let opened = crate::ccl::subst::open_tuple_components(&prefix, |j, _| {
        crate::ccl::subst::Mapping::Rename(names[j].clone())
    });
    if let Some(outer_name) = outer_name {
        let components: Vec<Expr> = names
            .iter()
            .zip(&opened)
            .map(|(name, ty)| Expr::var(name).with_ty(ty.clone()))
            .collect();
        let memo = PredMemo::new();
        crate::ccl::subst::rewrite_pairing_projections_memo(
            outer_name,
            &components,
            &mut keys,
            &memo,
        );
        crate::ccl::subst::rewrite_pairing_projections_memo(
            outer_name,
            &components,
            &mut elem,
            &memo,
        );
        assert!(
            !crate::ccl::subst::type_free_vars(&keys).contains(outer_name)
                && !crate::ccl::subst::type_free_vars(&elem).contains(outer_name),
            "a nested feed's keys and rows read an earlier level's key only through its \
             components"
        );
    }
    let components = names
        .into_iter()
        .map(Some)
        .zip(opened)
        .chain([(inner_name, keys)])
        .collect();
    keyed_by(components, elem)
}

/// A feed's contribution from under nested loops, rebuilt over the product of the loops'
/// positions: `𝐴 ≫ (λ 𝑥 → 𝐵 ≫ (λ 𝑦 → 𝑣))` becomes
/// `λ 𝑝 : (𝐷𝐴, 𝐷𝐵) → (𝑝.0 ▷ 𝐴) ▷ (λ 𝑥 → (𝑝.1 ▷ 𝐵) ▷ (λ 𝑦 → 𝑣))`, at any depth. A feed is keyed
/// by the position of every loop around it, so the channel is one collection over the tuple of
/// positions rather than a collection per outer position. The form is the one a multi-clause
/// comprehension lowers to (`src/ccl/lower/comprehension.rs`), and a `let` around or between
/// the loops stays where it is.
///
/// The tuple's refinement carries the loops' filters, read at their components, which is
/// where planning applies them. A loop's filter is the refinement its source's cast adds
/// ([`refine_source_domain`]); the cast is dropped from the loop's read, as a comprehension's
/// source carries none. No filter reads an enclosing loop's variable: that nest's keys depend
/// on the enclosing position, and [`indexed_nest`] builds it. A source's own domain refinement
/// stays on its component and is lifted as well; a present-key refinement is not a filter and
/// is not lifted.
///
/// [`classify_nest`] decides whether a contribution is that nest.
fn nest_as_product(contribution: Expr, generators: Vec<Generator>) -> Expr {
    let levels = generators.len();
    let domains: Vec<Type> = generators
        .iter()
        .map(|g| source_domain(&g.source().ty).expect("a loop's source is a collection"))
        .collect();
    let bare = Type::Tuple(domains.clone());
    let at = |index: usize| {
        Expr::apply(
            Expr::var(Name::elem()).with_ty(bare.clone()),
            Expr::proj_index(index).with_ty(Type::fun(bare.clone(), domains[index].clone())),
        )
        .with_ty(domains[index].clone())
    };
    let mut lifted: Vec<Refinement> = Vec::new();
    for (index, generator) in generators.iter().enumerate() {
        // The keys this loop ranges over: its source's own refinements and, where it filters,
        // the ones its `cast` states, which the keys satisfy together. A present-key
        // refinement is not a filter and is not lifted.
        let mut refinements: Vec<Refinement> = domains[index].refinements().to_vec();
        if let TypedExprNode::Cast { target, .. } = &generator.iterated.node {
            for r in cast_target_refinement(target)
                .expect("a loop filter's cast states the filter (`make_cast` asserts it)")
                .iter()
            {
                if !refinements.contains(r) {
                    refinements.push(r.clone());
                }
            }
        }
        for r in refinements.iter().filter(|r| !r.is_collection_membership()) {
            let predicate = crate::ccl::subst::Subst::discharge(Name::elem(), at(index))
                .apply_expr(&r.predicate);
            debug_assert!(
                generators[..index]
                    .iter()
                    .all(|g| count_free(&g.param.name, &predicate) == 0),
                "a product nest's filter reads no enclosing loop's variable ([`generator_nest`])"
            );
            lifted.push(Refinement::born(Rc::new(predicate)));
        }
    }
    let keys = if lifted.is_empty() {
        bare
    } else {
        let mut set = crate::ccl::ty::RefinementSet::new();
        set.extend(lifted);
        Type::Refinement(Box::new(bare), set)
    };
    let record = Name::fresh("__iter_record");
    let nest_params: Vec<Name> = generators.iter().map(|g| g.param.name.clone()).collect();
    around_lets(contribution, &mut |nest| {
        let body = rebuild_nest(nest, 0, levels, &mut |depth, _, param, inner| {
            let position = Expr::apply(
                Expr::var(&record).with_ty(keys.clone()),
                Expr::proj_index(depth).with_ty(Type::fun(keys.clone(), domains[depth].clone())),
            )
            .with_ty(domains[depth].clone());
            read_level(
                position,
                generators[depth].source().clone(),
                param,
                inner,
                &nest_params,
            )
        });
        collection_over(&record, keys.clone(), body)
    })
}

/// How a feed's contribution from under nested loops is rebuilt to be keyed by the tuple of
/// the loops' positions (`docs/chl-spec.md`, "8.4 Feeds are the second form of mutability").
enum Nest {
    /// No loop's source reads an enclosing loop's binder or a name bound inside one, so the
    /// positions are a product: [`nest_as_product`].
    Product(Vec<Generator>),
    /// Generators, some source reading an enclosing loop, so its positions differ per
    /// enclosing position: [`indexed_nest`], then [`flatten_nested_contribution`].
    Indexed,
    /// One loop, or a level that is not a loop generator but a collection indexed by position
    /// or a gated unit: [`flatten_nested_contribution`] alone.
    Flat,
}

/// Which [`Nest`] `contribution` is, fed under `levels` loops.
fn classify_nest(contribution: &Expr, levels: usize) -> Nest {
    if levels < 2 {
        return Nest::Flat;
    }
    let mut generators = Vec::with_capacity(levels);
    match generator_nest(
        contribution,
        levels,
        &mut NestScope::default(),
        &mut generators,
    ) {
        Some(true) => Nest::Product(generators),
        Some(false) => Nest::Indexed,
        None => Nest::Flat,
    }
}

/// `build` applied beneath the `let`s that open `expr`, which stay around what it builds: a
/// `let` ahead of the outermost loop is bound once, not once per position.
fn around_lets(expr: Expr, build: &mut dyn FnMut(Expr) -> Expr) -> Expr {
    if !matches!(expr.node, TypedExprNode::Let { .. }) {
        return build(expr);
    }
    let TypedExpr {
        node:
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            },
        user_annotation,
        node_id,
        ..
    } = expr
    else {
        unreachable!("matched as a `let`")
    };
    rebuild_let(
        binding,
        bound_expr,
        user_annotation,
        node_id,
        around_lets(*body, build),
    )
}

/// The `let` at `node_id` rebuilt around a new `body`, which gives it its type.
fn rebuild_let(
    binding: TypedBinding,
    bound_expr: Box<Expr>,
    user_annotation: Option<Type>,
    node_id: NodeId,
    body: Expr,
) -> Expr {
    TypedExpr {
        ty: lifted_past(&binding, &bound_expr, &body.ty),
        node: TypedExprNode::Let {
            binding,
            bound_expr,
            body: Box::new(body),
        },
        user_annotation,
        // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
        node_id,
    }
}

/// `ty`, written under the binder `binding` of a `let` defining it as `bound_expr`, as it reads
/// outside it: a transparent binder discharged to its definition, as inference's
/// `close_let_type` lifts a `let`'s type. An opaque binder's name stays.
fn lifted_past(binding: &TypedBinding, bound_expr: &Expr, ty: &Type) -> Type {
    if binding.transparency == BindingTransparency::Opaque
        || !crate::ccl::subst::type_free_vars(ty).contains(&binding.name)
    {
        return ty.clone();
    }
    crate::ccl::subst::Subst::discharge(
        &binding.name,
        crate::ccl::ccl_utils::predicate_term(bound_expr),
    )
    .apply_type(ty)
}

/// One generator of a nest, as [`generator_nest`] reads it: the term the loop iterates and
/// the loop's binder.
struct Generator {
    /// The loop's source, under the `cast` that carries the loop's filter when it has one
    /// ([`refine_source_domain`]).
    iterated: Expr,
    param: TypedBinding,
}

impl Generator {
    /// The collection the loop reads its elements from: the iterated term without its
    /// filter's `cast`.
    fn source(&self) -> &Expr {
        match &self.iterated.node {
            TypedExprNode::Cast { value, .. } => value,
            _ => &self.iterated,
        }
    }
}

/// The names [`generator_nest`] has passed: the binders of enclosing generators and the
/// names bound between them.
#[derive(Default)]
struct NestScope {
    binders: Vec<Name>,
    lets: Vec<Name>,
}

/// Whether `nest` is `levels` generators, each a source composed with a lambda over its
/// elements, and if so whether it is **independent**: no generator's source or filter reads an
/// enclosing generator's binder or a name bound inside one. Collects each generator into
/// `generators`, outermost first. `None` where a level is not a loop generator but a collection indexed by position or
/// a gated unit, which [`flatten_nested_contribution`] takes as it is.
///
/// Decided by the nest's shape and the names its terms read alone: no type is consulted.
fn generator_nest(
    nest: &Expr,
    levels: usize,
    scope: &mut NestScope,
    generators: &mut Vec<Generator>,
) -> Option<bool> {
    if levels == 0 {
        return Some(true);
    }
    match &nest.node {
        TypedExprNode::Let { binding, body, .. } => {
            if !scope.binders.is_empty() {
                scope.lets.push(binding.name.clone());
            }
            generator_nest(body, levels, scope, generators)
        }
        TypedExprNode::Compose(elts) => {
            let [prefix @ .., last] = elts.as_slice() else {
                return None;
            };
            let TypedExprNode::Lambda { param, body } = &last.node else {
                return None;
            };
            let iterated = match prefix {
                [] => return None,
                [one] => one.clone(),
                _ => compose_typed_or_hole(prefix.to_vec()),
            };
            let generator = Generator {
                iterated,
                param: param.clone(),
            };
            // Neither the source nor its filter may read an enclosing binder or a name bound
            // between the loops: the loop's keys would then depend on the enclosing position,
            // and the keys of the nest are a dependent tuple rather than a product.
            let reads = |names: &[Name], e: &Expr| names.iter().any(|n| count_free(n, e) > 0);
            let independent = !reads(&scope.binders, &generator.iterated)
                && !reads(&scope.lets, &generator.iterated);
            generators.push(generator);
            scope.binders.push(param.name.clone());
            Some(generator_nest(body, levels - 1, scope, generators)? && independent)
        }
        _ => None,
    }
}

/// The domain of a loop's source: a collection's, or, for a read of a deferred collection
/// (a generator's channel, typed by its handle until this pass assembles it), the handle's
/// channel domain ([`channel_domain_of`]).
fn source_domain(ty: &Type) -> Option<Type> {
    ty.domain().or_else(|| channel_domain_of(ty))
}

/// The type of one item of a loop's source: a collection's codomain, or a deferred
/// collection's element type, as [`source_domain`] reads its domain.
fn source_item(ty: &Type) -> Type {
    ty.codomain()
        .or_else(|| ty.as_feed().map(|(_, element)| element.clone()))
        .unwrap_or_else(|| panic!("a loop's source is a collection, got {ty}"))
}

/// `nest` with each of its `levels` generators `𝑠 ≫ (λ 𝑥 → body)` rebuilt by `level`, which
/// is handed the generator's depth, its source `𝑠`, its binder `𝑥` and the rebuilt `body`.
/// Every `let` stays in place.
fn rebuild_nest(
    nest: Expr,
    depth: usize,
    levels: usize,
    level: &mut dyn FnMut(usize, Expr, TypedBinding, Expr) -> Expr,
) -> Expr {
    if depth == levels {
        return nest;
    }
    let TypedExpr {
        node,
        user_annotation,
        node_id,
        ..
    } = nest;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => rebuild_let(
            binding,
            bound_expr,
            user_annotation,
            node_id,
            rebuild_nest(*body, depth, levels, level),
        ),
        TypedExprNode::Compose(mut elts) => {
            let lambda = elts
                .pop()
                .expect("a generator has a source before its lambda");
            let TypedExprNode::Lambda { param, body } = lambda.node else {
                panic!("a loop level of a feed contribution is `𝑠 ≫ (λ 𝑥 → body)`")
            };
            let source = match elts.len() {
                1 => elts.pop().expect("one element"),
                _ => compose_typed_or_hole(elts),
            };
            let inner = rebuild_nest(*body, depth + 1, levels, level);
            level(depth, source, param, inner)
        }
        other => panic!(
            "a loop level of a feed contribution is `𝑠 ≫ (λ 𝑥 → body)`, got {}",
            other.kind_name()
        ),
    }
}

/// `(position ▷ source) ▷ (λ param → inner)`: one generator's step at `position`. The lambda's
/// type is dependent: a deeper generator's domain may name `param`, in a filter that reads it.
///
/// Where `inner`'s type reads a variable of the nest's loops (`nest_params`), as a row filtered
/// by one does, the step is `inner` with the read substituted for `param` in terms and types
/// alike, at every level, rather than a redex. The row's filter then reads the position, which
/// lambda elimination lifts onto the key as it lifts any filter reading a lambda's parameter.
/// Behind a redex, the variable the filter reads would be gone from the term by the time the
/// key's lambda is eliminated.
fn read_level(
    position: Expr,
    source: Expr,
    param: TypedBinding,
    inner: Expr,
    nest_params: &[Name],
) -> Expr {
    let item = source_item(&source.ty);
    let read = Expr::apply(position, source).with_ty(item);
    let row_reads = crate::ccl::subst::type_free_vars(&inner.ty);
    if nest_params.iter().any(|p| row_reads.contains(p)) {
        return crate::ccl::subst::Subst::discharge(param.name, read).apply_expr(&inner);
    }
    let ty = inner.ty.clone();
    let lambda = contribution_lambda(&param, inner, None);
    Expr::apply(read, lambda).with_ty(ty)
}

/// `λ position : domain → body`, a collection over `domain`, keyed where `body`'s type reads
/// `position`.
fn collection_over(position: &Name, domain: Type, body: Expr) -> Expr {
    let value = body.ty.clone();
    let ty = if crate::ccl::subst::type_free_vars(&value).contains(position) {
        Type::pi_kinded(position.clone(), domain.clone(), value, FunKind::Data(None))
    } else {
        Type::data_fun(domain.clone(), value)
    };
    Expr::lambda(position, domain, body).with_ty(ty)
}

/// A feed's contribution from under `levels` loops, each level indexed by its own position:
/// `𝐴 ≫ (λ 𝑥 → 𝐵 ≫ (λ 𝑦 → 𝑣))` becomes
/// `λ 𝑟 : 𝐷𝐴 → (𝑟 ▷ 𝐴) ▷ (λ 𝑥 → λ 𝑞 : 𝐷𝐵 → (𝑞 ▷ 𝐵) ▷ (λ 𝑦 → 𝑣))`, the form a nested
/// comprehension lowers to (`src/ccl/lower/comprehension.rs`). A generator composed onto its
/// source is a pipeline, which a recurrence's body cannot hold per position of the recurrence;
/// the indexed form is a collection there like any other.
///
/// A `let` between two levels is bound inside the inner level's position lambda, next to the
/// read of that level's source, as it is in [`nest_as_product`]'s form.
fn indexed_nest(nest: Expr, levels: usize) -> Expr {
    let nest_params = loop_params(&nest, levels);
    rebuild_nest(nest, 0, levels, &mut |_, source, param, inner| {
        let inner = lets_into_position(inner);
        let domain = source_domain(&source.ty).expect("a loop's source is a collection");
        let position = Name::fresh("__iter_record");
        let step = read_level(
            Expr::var(&position).with_ty(domain.clone()),
            source,
            param,
            inner,
            &nest_params,
        );
        collection_over(&position, domain, step)
    })
}

/// The variables of the `levels` loops of `nest`, outermost first: each `𝑠 ≫ (λ 𝑥 → body)`'s
/// `𝑥`, through the `let`s between them.
fn loop_params(nest: &Expr, levels: usize) -> Vec<Name> {
    let mut params = Vec::with_capacity(levels);
    let mut at = nest;
    while params.len() < levels {
        match &at.node {
            TypedExprNode::Let { body, .. } => at = body,
            TypedExprNode::Compose(elts) => match elts.last().map(|e| &e.node) {
                Some(TypedExprNode::Lambda { param, body }) => {
                    params.push(param.name.clone());
                    at = body;
                }
                _ => break,
            },
            _ => break,
        }
    }
    params
}

/// `expr` with the `let`s that open it moved inside the position lambda they open onto, if
/// they open onto one.
fn lets_into_position(expr: Expr) -> Expr {
    let TypedExprNode::Let { .. } = &expr.node else {
        return expr;
    };
    let TypedExpr {
        node:
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            },
        user_annotation,
        node_id,
        ..
    } = expr
    else {
        unreachable!("matched as a `let`")
    };
    let body = lets_into_position(*body);
    // The position lambda moves out from under the `let`, so its type reads the binding as the
    // `let`'s own type would.
    let lambda_ty = lifted_past(&binding, &bound_expr, &body.ty);
    let rebind = |body: Expr| rebuild_let(binding, bound_expr, user_annotation, node_id, body);
    match body.node {
        TypedExprNode::Lambda { param, body: step } => TypedExpr {
            node: TypedExprNode::Lambda {
                param,
                body: Box::new(rebind(*step)),
            },
            ty: lambda_ty,
            ..body
        },
        node => rebind(TypedExpr { node, ..body }),
    }
}

/// The contributions a feed-only loop makes, one per feed in it, each with the deferred
/// collection it feeds: what channelization assembles a loop's channel from, here for a loop
/// that feeds from inside a recurrence. Each is in [`indexed_nest`]'s form, a collection per
/// position of the recurrence, with the number of loops it is keyed by. `mut_elim` takes each as a tap of the recurrence, and
/// channelization flattens the levels when it assembles the outer channel
/// ([`flatten_nested_contribution`]). A feed is a tap of its own rather than combined with the
/// loop's other feeds of the same collection, because feeds at different depths are keyed by
/// different numbers of positions.
///
/// `feed_loop` is `𝑠 ≫ (λ 𝑥 → body)` with no mutable variable written in `body`. A `<<=`
/// inside it is refused, as one inside any loop is.
pub(crate) fn loop_contributions(feed_loop: Expr) -> Vec<(Name, Expr, usize)> {
    let mut contributions = Vec::new();
    let mut rest = feed_loop;
    for defer in collect_feed_target_names(&rest) {
        let mut feeds = Vec::new();
        let mut define = None;
        rest = extract_for_defer(rest, &defer, &mut feeds, &mut define, false)
            .unwrap_or_else(|e| panic!("a feed-only loop inside a recurrence: {}", e.error));
        assert!(
            define.is_none(),
            "a `<<=` inside a loop defines its collection once per iteration"
        );
        for Contribution { value, levels, .. } in feeds {
            contributions.push((defer.clone(), indexed_nest(value, levels), levels));
        }
    }
    contributions
}

/// Return `true` if `expr` contains any `Feed(target, …)` or
/// `Define(target, …)` node where `target == name`, respecting shadowing
/// by `Let`/`Lambda` bindings that rebind `name`.
///
/// Debug-only: the sole caller is the `channelize_expr` invariant assert that a
/// bare-`Var` defer alias never survives `inline` into channelize.
#[cfg(debug_assertions)]
fn contains_feed_or_define_for(expr: &Expr, name: &Name) -> bool {
    match &expr.node {
        // Hit: the Feed/Define's target name matches.  Also recurse into
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
                || (&binding.name != name && contains_feed_or_define_for(body, name))
        }
        TypedExprNode::Lambda { param, body, .. } => {
            &param.name != name && contains_feed_or_define_for(body, name)
        }
        _ => expr.any_child(|c| contains_feed_or_define_for(c, name)),
    }
}

/// Substitute every free `Var(name)` in `expr` with `replacement`.
///
/// Replace every free occurrence of `Var(name)` with `replacement` during
/// channelization, renaming `Feed`/`Define` targets along the way: when
/// `replacement` is a `Var(new_name)`, handle uses of `name` become
/// `new_name` — the α-renaming that makes alias-inlining for defer handles
/// correct.
///
/// A thin wrapper over the uniform engine's in-place mode
/// ([`crate::ccl::subst::Subst::rewrite_expr`]). Unlike the pre-port
/// version, the engine also rewrites type-carried refinement predicates
/// (`Cast` targets, annotations), so a channelize rename now reaches a
/// predicate that closes over the renamed binder instead of leaving a stale
/// reference; and a `Case` pattern binding correctly shadows `name` in its
/// branch.
fn channelize_rename(expr: Expr, from: &Name, to: &Name) -> Expr {
    let mut expr = expr;
    // A **rename**, not a discharge of a bare variable. Both rewrite the same
    // occurrences, but the species is what carries the occurrence's type onto the
    // replacement (`Mapping::as_expr`): α-renaming cannot change a term's type, while a
    // discharge substitutes a term that brings its own — and a hand-built `Expr::var`
    // brings `Type::Hole`, which `subst`'s typedness assertion now rejects. Keeping the
    // species honest also keeps `Subst::invert`/`split_renames` exact here.
    crate::ccl::subst::Subst::rename(from.clone(), to.clone()).rewrite_expr(&mut expr);
    expr
}

/// State threaded through the channelize walk: the channel domains it resolves.
struct ChannelizeCtx {
    /// each channelized defer's concrete channel domain,
    /// keyed by its (nominal) `ChanDom` name — recorded as clusters are
    /// assembled, then closed and substituted over the whole tree by [`run`].
    /// A recorded domain may itself reference another cluster name (an alias
    /// `x <<= y` records `x ↦ ChanDom(y)`); [`close_chan_domains`] resolves
    /// those before the substitution.
    resolved_domains: Vec<(Name, Type)>,
    /// Each channelized defer's **binder slot**, keyed the same way as
    /// [`Self::resolved_domains`]. A channel over a conditional source is a collection over
    /// that source's witness — `Σ (σ : 𝐾). σ ⤇ 𝑉` — and only the assembled channel's own
    /// type says so: a witness reference carries no kind, so the slot cannot be
    /// reconstructed from the substituted domain. An alias records none and erases
    /// unbound, as it did before.
    channel_kinds: Vec<(Name, FunKind)>,
    /// The `let d = Defer` node that declares each deferred binding, which is
    /// where an error about the binding as a whole is raised
    /// ([`Self::at_declaration`]). Recorded as the walk reaches each declaration,
    /// before it processes the cluster the binding opens.
    defer_decls: HashMap<Name, NodeId>,
}

impl ChannelizeCtx {
    fn new() -> Self {
        Self {
            resolved_domains: Vec::new(),
            channel_kinds: Vec::new(),
            defer_decls: HashMap::new(),
        }
    }

    /// `error` at the declaration of the binding it names: an error about the
    /// binding as a whole rather than about one of its feeds or defines.
    ///
    /// # Panics
    ///
    /// If the walk has not reached the binding's declaration. Only a cluster
    /// raises these errors, and the walk records every declaration of a cluster
    /// before processing it.
    fn at_declaration(&self, error: DeferError) -> Located<DeferError> {
        let node = *self.defer_decls.get(error.defer()).unwrap_or_else(|| {
            panic!(
                "`{}` is reported before the walk reached its declaration",
                error.defer()
            )
        });
        Located::new(error, node)
    }
}

/// Eliminate all `Defer`/`Feed`/`Define` nodes from `expr`.
///
/// Walks the expression top-down.  Every `let d = Defer in body` triggers
/// the channelization rewrite described in the module docs.  After this
/// pass returns, no `Defer`, `Feed`, or `Define` nodes remain — any
/// residue is reported as [`DeferError::UnboundDeferHandle`].
///
/// **Runs on an inferred tree.** The pass reads types it cannot re-derive — a
/// feed handle's rigid `ChanDom`, a channel's concrete domain — and closes the
/// tree by substituting each `ChanDom(d)` to its assembled channel's domain. Its
/// unit tests type their fixtures for the same reason.
///
/// As a final step, every `ExprStmt(e, b)` is collapsed to `b`.  The
/// variant only existed as a vehicle for surfacing `Feed`/`Define` sites
/// in statement position; once those have been extracted into source
/// channels, the surrounding `ExprStmt`'s `e` argument is a pure
/// `Unit`-typed value that can be dropped.  Doing this in `channelize`
/// (rather than leaving it for `simplify`) means no later pass needs to
/// pattern-match `ExprStmt`.
pub fn run(expr: Expr) -> Result<Expr, Located<DeferError>> {
    // Keying a contribution builds a function type per level over the same predicates, so one
    // memo serves every binder conversion of a predicate shared across them.
    crate::ccl::subst::with_conversion_memo(|| run_memoized(expr))
}

fn run_memoized(expr: Expr) -> Result<Expr, Located<DeferError>> {
    let mut ctx = ChannelizeCtx::new();
    // Cluster channelization.  Walks the tree, processes `let d = Defer in …`
    // clusters, extracting feeds and building each defer's channel.
    //
    // Defer-mediating UDFs (`def g(out): out << e`, `def f(n): x = defer();
    // …; x`) never reach here: `inline` beta-reduces every such function at its
    // call site *before* this pass (it runs pre-channelize — see the `inline`
    // module docs), leaving only the flattened `let d = Defer in …` chains this
    // walk handles. The former Phase-1 chain rewriter and the call-site smart
    // walker that existed for the un-inlined higher-order case are retired.
    let rewritten = channelize_expr(expr, &mut ctx)?;
    let mut rewritten = drop_expr_stmts(rewritten);
    assert_no_defer_residue(&rewritten)?;
    // With nominal channel domains, every consumer of a defer read typed
    // *concretely* against `ChanDom(d)` at inference — there is no `Infer`
    // channel-domain residue to re-derive. Closing the tree is therefore a pure
    // whole-tree type substitution: map each `ChanDom(d)` to its assembled
    // channel's concrete domain, and erase each `Feed`-kind history to its bare
    // `Fun` — the exact feed-side analog of `mut_elim::erase_mut`. The
    // strict post-channelize `typecheck` in `compile_program` backstops the
    // invariant.
    let mut map = close_chan_domains(std::mem::take(&mut ctx.resolved_domains));
    let kinds: HashMap<Name, FunKind> =
        std::mem::take(&mut ctx.channel_kinds).into_iter().collect();
    // One predicate memo for the whole erasure, so occurrences that shared a predicate
    // term still share one afterwards ([`PredMemo`], "One memo per pass").
    let predicates: PredMemo<()> = PredMemo::default();
    erase_chan_domains(&mut rewritten, &mut map, &kinds, &predicates);
    #[cfg(debug_assertions)]
    assert_no_type_residue(&rewritten);
    Ok(rewritten)
}

/// The channel-domain name (and its inference level) carried by a feed
/// handle's recorded type — `feed(ChanDom(n) ⤇ V)`, through refinements.
/// This is the name consumer types actually reference. For a specialization
/// clone it differs from the term binder name (channel identity is
/// per-instantiation, freshened at `specialize_use`), so channel recording
/// and lift-alias entries key on it, never on the term name.
fn handle_chan_dom(ty: &Type) -> Option<(Name, crate::ccl::ChanLevel)> {
    match ty.as_feed()?.0.peel_refinements() {
        Type::ChanDom(n, l) => Some((n.clone(), *l)),
        _ => None,
    }
}

/// the channel domain carried by an assembled channel's
/// type — the domain of its constructed `Fun`, or, for an alias channel that
/// is itself a defer read (`x <<= y` leaves `Var(y) : feed(…)`), the read's
/// handle domain (a `ChanDom` closed later by [`close_chan_domains`]).
fn channel_domain_of(ty: &Type) -> Option<Type> {
    match ty.peel_refinements() {
        Type::Fun { domain, .. } => Some((**domain).clone()),
        _ => ty.as_feed().map(|(domain, _)| domain.clone()),
    }
}

/// close the recorded name → domain entries over each other
/// (an alias `x <<= y` recorded `x ↦ ChanDom(y)`; resolve it to `y`'s concrete
/// domain). Terminates because cross-references are acyclic (the per-cluster
/// topo sort rejects cycles); a duplicate name with *disagreeing* domains —
/// which specialization of a polymorphic defer-returning UDF would produce —
/// is a structural failure of the nominal scheme, so refuse loudly.
fn close_chan_domains(entries: Vec<(Name, Type)>) -> HashMap<Name, Type> {
    let mut map: HashMap<Name, Type> = HashMap::new();
    for (name, dom) in entries {
        if let Some(prev) = map.get(&name) {
            assert!(
                *prev == dom,
                "channel domain for `{name}` recorded twice with \
                 disagreeing domains ({prev} vs {dom}) — nominal domains cannot \
                 distinguish specialized copies of one defer binder"
            );
            continue;
        }
        map.insert(name, dom);
    }
    // Substitute the map into its own values until no value references a map
    // key. Bounded by the map size (each pass must resolve at least one
    // reference or the reference chain is a cycle).
    for _ in 0..=map.len() {
        let mut changed = false;
        let snapshot = map.clone();
        for dom in map.values_mut() {
            let before = dom.clone();
            subst_chan_domains_in_type(dom, &snapshot);
            changed = changed || *dom != before;
        }
        if !changed {
            return map;
        }
    }
    panic!("cyclic channel-domain references survived topo sort");
}

/// rewrite `ty` in place — every `ChanDom(d)` becomes its
/// concrete channel domain from `map` (unmapped names are left for
/// [`assert_no_type_residue`] / the strict wall to flag).
fn subst_chan_domains_in_type(ty: &mut Type, map: &HashMap<Name, Type>) {
    if let Type::ChanDom(name, _) = ty {
        if let Some(dom) = map.get(name) {
            *ty = dom.clone();
            // The substituted domain is drawn from a *constructed* channel
            // type; it may nest another feed handle only through an unmapped
            // alias, which the residue assert flags. Recurse for totality —
            // the closed map cannot re-introduce a mapped name, so this
            // terminates.
            subst_chan_domains_in_type(ty, map);
        }
        return;
    }
    ty.walk_children_mut(|t| subst_chan_domains_in_type(t, map));
}

/// erase every `Feed`-kind `Type::History` in `ty` to its
/// bare `Fun(domain, value)` and substitute every `ChanDom` via
/// [`subst_chan_domains_in_type`] — the feed-side analog of
/// `mut_elim::erase_mut_in_type`.
fn erase_chan_domains_in_type(
    ty: &mut Type,
    map: &HashMap<Name, Type>,
    kinds: &HashMap<Name, FunKind>,
) -> bool {
    if let Type::History {
        function,
        history_kind: HistoryKind::Append,
    } = ty
    {
        // The handle names its channel, and the channel's assembled type is what says
        // whether the read view binds a witness. Read it before the domain is substituted:
        // afterwards the domain is a bare reference, and a reference carries no kind.
        let Type::Fun {
            name,
            domain,
            codomain: value,
            ..
        } = std::mem::replace(function.as_mut(), Type::Hole)
        else {
            unreachable!("a history's function is an unrefined function")
        };
        let fun_kind = match domain.peel_refinements() {
            Type::ChanDom(n, _) => kinds.get(n).cloned(),
            _ => None,
        };
        // A feed channel reads as a collection: erase History to its function, a data function
        // keeping the function's binder.
        *ty = Type::Fun {
            name,
            fun_kind: fun_kind.unwrap_or(FunKind::Data(None)),
            domain,
            codomain: value,
        };
        erase_chan_domains_in_type(ty, map, kinds);
        return true;
    }
    if let Type::ChanDom(name, _) = ty {
        let Some(dom) = map.get(name) else {
            return false;
        };
        *ty = dom.clone();
        erase_chan_domains_in_type(ty, map, kinds);
        return true;
    }
    let mut changed = false;
    ty.walk_children_mut(|t| changed |= erase_chan_domains_in_type(t, map, kinds));
    changed
}

/// Whether `ty`'s own structure holds a type satisfying `hit`. Refinement predicates are
/// not walked, which is the reach of [`erase_chan_domains_in_type`].
fn structure_holds_type(ty: &Type, hit: &dyn Fn(&Type) -> bool) -> bool {
    if hit(ty) {
        return true;
    }
    let mut found = false;
    ty.walk_children(|c| found |= structure_holds_type(c, hit));
    found
}

/// Whether any refinement predicate reachable from `ty` holds a type satisfying `hit` in
/// one of its own node slots. Such a slot is a slot like any other, so a refinement sitting
/// in one contributes its predicate too, at whatever depth. That re-entry mirrors the one
/// [`erase_chan_domains_in_predicates`] makes through [`erase_chan_domains_in_slot`], and
/// `visited` dedups the predicate DAG across it.
///
/// Read-only, and the two things that ask are the eraser and its checker: the gate on
/// [`erase_chan_domains_in_predicates`] asks for a channel type, and [`has_type_residue`]
/// asks for anything channelization must have removed.
///
/// Gating the eraser on a read-only scan is what keeps node ids stable. Rebuilding a
/// predicate copies it, and the copy draws fresh ids whether or not the rebuild is kept,
/// so a walk that entered unconditionally would renumber every later node in programs
/// with nothing to erase. The scan lives here rather than in
/// [`walk_refined_predicates_mut`] because that helper clones before it can ask; a probe
/// that ran on the shared term first belongs there, and every pass with a conditional
/// predicate rewrite will want it.
fn predicates_hold_type(
    ty: &Type,
    hit: &dyn Fn(&Type) -> bool,
    visited: &mut HashSet<PredicateId>,
) -> bool {
    fn in_expr(e: &Expr, hit: &dyn Fn(&Type) -> bool, visited: &mut HashSet<PredicateId>) -> bool {
        let mut found = false;
        e.walk_type_slots(|t| found |= slot_holds_type(t, hit, visited));
        e.walk_children(|c| found |= in_expr(c, hit, visited));
        found
    }
    let mut found = false;
    walk_refined_predicates(ty, visited, &mut |pred, vis| {
        // A predicate holding its own `defer` is in source form: this pass does not rewrite
        // inside a predicate, and lifting the predicate channelizes it
        // (`planning::predicates::eliminate_lifted`), so its channel types are its own until
        // then.
        if !holds_defer(pred) {
            found |= in_expr(pred, hit, vis);
        }
    });
    found
}

/// Whether `e` binds a `defer` anywhere in its term.
pub(crate) fn holds_defer(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::Defer) || e.fold_children(false, |acc, c| acc || holds_defer(c))
}

/// Whether one type slot holds a type satisfying `hit`, structure and refinement predicates
/// alike. The checker half of [`erase_chan_domains_in_slot`].
fn slot_holds_type(
    ty: &Type,
    hit: &dyn Fn(&Type) -> bool,
    visited: &mut HashSet<PredicateId>,
) -> bool {
    structure_holds_type(ty, hit) || predicates_hold_type(ty, hit, visited)
}

/// Erase channel types inside `ty`'s refinement **predicates**, which
/// [`erase_chan_domains_in_type`] does not reach: `Type::walk_children_mut` visits a
/// `Type::Refinement`'s base and not its predicate.
///
/// A predicate over a channel-domain source carries that domain in its node types.
/// The post-channelization type check visits predicates and rejects residual
/// channel domains. See `src/ccl/design/type-inference.md`,
/// "Feed handles as invariant histories".
///
/// A predicate's own type slots go back through [`erase_chan_domains_in_slot`], so a
/// refinement sitting in one has its predicate erased too. `walk_refined_predicates_mut`
/// hands the callback the memo for exactly that re-entry.
///
/// `predicates` is the pass's one memo, so occurrences that shared a predicate term leave
/// sharing it ([`PredMemo`]).
///
/// Returns whether anything was rewritten.
fn erase_chan_domains_in_predicates(
    ty: &mut Type,
    map: &HashMap<Name, Type>,
    kinds: &HashMap<Name, FunKind>,
    predicates: &PredMemo<()>,
) -> bool {
    if !predicates_hold_type(ty, &is_channel_type, &mut HashSet::new()) {
        return false;
    }
    walk_refined_predicates_mut(ty, predicates, &(), &mut |pred, memo| {
        fn go(
            e: &mut Expr,
            map: &HashMap<Name, Type>,
            kinds: &HashMap<Name, FunKind>,
            memo: &PredMemo<()>,
        ) -> bool {
            let mut changed = false;
            e.walk_type_slots_mut(|t| changed |= erase_chan_domains_in_slot(t, map, kinds, memo));
            e.walk_children_mut(|c| changed |= go(c, map, kinds, memo));
            changed
        }
        go(pred, map, kinds, memo)
    })
}

/// Erase channel types from one type slot: its structure and its refinement predicates
/// alike. [`has_type_residue`] checks the same pair through [`slot_holds_type`], so the
/// eraser and its checker cannot disagree about what a slot holds. Returns whether
/// anything was rewritten.
fn erase_chan_domains_in_slot(
    ty: &mut Type,
    map: &HashMap<Name, Type>,
    kinds: &HashMap<Name, FunKind>,
    predicates: &PredMemo<()>,
) -> bool {
    let mut changed = erase_chan_domains_in_type(ty, map, kinds);
    changed |= erase_chan_domains_in_predicates(ty, map, kinds, predicates);
    changed
}

/// whole-tree erasure — node types, user annotations, and
/// the binder slots `walk_children_mut` does not reach (mirroring
/// `mut_elim::erase_mut`'s coverage of the strict-wall checker).
///
/// The walk is **bottom-up and scope-aware**: a substituted channel domain may
/// carry a refinement predicate that closes over a `let`-bound variable (a
/// filter-feed guard `x > n` referencing `let n = 0`). Inference never saw
/// that predicate above the binder — the rigid `ChanDom` hid it — so its §6.2
/// Let-closing discharge was vacuous there. Replay it here: after a `Let`'s
/// subtree is erased, discharge `[name ↦ bound]` into every map value, so any
/// substitution *above* the binder injects the closed form the strict checker
/// derives. Still derivation-free — a discharge transport, not re-inference.
fn erase_chan_domains(
    expr: &mut Expr,
    map: &mut HashMap<Name, Type>,
    kinds: &HashMap<Name, FunKind>,
    predicates: &PredMemo<()>,
) {
    // Erase this node's binder-declared type slots — both the declared type and
    // the annotation, since a handle can ride either. Deliberately *not*
    // `walk_type_slots_mut` (which `mut_elim::erase_mut` uses): the slots here are
    // visited in three separate phases — binders, then children, then this node's
    // own `ty`/annotation *after* the `Let`-discharge below has updated `map` —
    // and one combined call would collapse that ordering. This is order-invariant
    // w.r.t. the `Let`-discharge below: a binder's type resolves against `map` as
    // it stands, and a child's discharge only closes variables bound *inside*
    // that child — never in scope at this binder — so erasing binders before the
    // child recursion sees the same substitutions the old inline order did.
    expr.walk_binders_mut(|b| {
        erase_chan_domains_in_slot(&mut b.ty, map, kinds, predicates);
        if let Some(ann) = &mut b.user_annotation {
            erase_chan_domains_in_slot(ann, map, kinds, predicates);
        }
    });
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut expr.node
    {
        erase_chan_domains(bound_expr, map, kinds, predicates);
        erase_chan_domains(body, map, kinds, predicates);
        // §6.2 Let-closing on the substitution content (see fn docs).
        // A discharge template is not a tree node: it is cloned again at every
        // read, and that read is where the sibling is minted.
        let discharge =
            crate::ccl::subst::Subst::discharge(&binding.name, bound_expr.clone_preserving_ids());
        // Only a domain naming the binder is rewritten. A `let` under a loop's position
        // lambda can read the position, and a domain built from that loop names a binder
        // after it, which a discharge passing under it would report as a capture.
        for dom in map.values_mut() {
            if crate::ccl::subst::type_free_vars(dom).contains(&binding.name) {
                *dom = discharge.apply_type(dom);
            }
        }
    } else {
        expr.walk_children_mut(|c| erase_chan_domains(c, map, kinds, predicates));
    }
    erase_chan_domains_in_slot(&mut expr.ty, map, kinds, predicates);
    if let Some(ann) = &mut expr.user_annotation {
        erase_chan_domains_in_slot(ann, map, kinds, predicates);
    }
}

/// The codomain of `ty` viewed as a function, peeling outer refinements.
///
/// a `Feed`-kind history is viewed as its `domain ⤇ value` — with rigid
/// nominal domains an unresolved defer read has a usable
/// (concrete-modulo-`ChanDom`) function view, so a channel built on
/// a read prefix (a nested generator's inner channel block) types at
/// construction instead of leaving a `Hole` for a re-derivation pass.
fn fun_codomain(ty: &Type) -> Option<Type> {
    match ty.peel_refinements() {
        Type::Fun { codomain, .. } => Some((**codomain).clone()),
        _ => ty.as_feed().map(|(_, value)| value.clone()),
    }
}

/// The domain of `ty` viewed as a function, peeling outer refinements.
/// See [`fun_codomain`] for the feed-history read view.
fn fun_domain(ty: &Type) -> Option<Type> {
    match ty.peel_refinements() {
        Type::Fun { domain, .. } => Some((**domain).clone()),
        _ => ty.as_feed().map(|(domain, _)| domain.clone()),
    }
}

/// Debug-only invariant: after [`run`] on a typed input, no expression or
/// binder slot may still carry a `Hole`, `Infer`, or `Feed` type — channelize
/// erased the defer constructs, so their transient types must be gone too. A slot's
/// refinement predicates are part of it ([`has_type_residue`]), since
/// [`erase_chan_domains_in_predicates`] is what clears them.
#[cfg(debug_assertions)]
fn assert_no_type_residue(expr: &Expr) {
    assert!(
        !has_type_residue(&expr.ty),
        "type residue survived channelize on `{}` : {}",
        crate::ccl::symbolic::symbolic(expr),
        expr.ty
    );
    match &expr.node {
        TypedExprNode::Lambda { param, .. } => assert!(
            !has_type_residue(&param.ty),
            "type residue survived channelize on lambda param `{}` : {}",
            param.name,
            param.ty
        ),
        TypedExprNode::Let { binding, .. } => assert!(
            !has_type_residue(&binding.ty),
            "type residue survived channelize on let binding `{}` : {}",
            binding.name,
            binding.ty
        ),
        _ => {}
    }
    expr.walk_children(assert_no_type_residue);
}

/// Attach the filter-feed guard refinement to a channel source's *domain*,
/// stamping the refined function type directly on `source.ty`.
///
/// The refinement rides a **`cast`** wrapping the source: inference has already
/// run, so nothing would consume an annotation, and the refinement needs a term
/// to carry it. Planning reifies a domain refinement into the source's
/// `restrict`, but only where it recognizes the site as not-yet-materialized,
/// which is a question about the *term* ([`crate::ccl::planning`]'s
/// `is_iteration_bearing`); refining `source.ty` in place would answer it with
/// whatever node sits underneath, dropping the guard for a source that already
/// reads as iterating.
///
/// A channel source is always a concrete function type by the time this runs, so
/// the non-`Fun` case is a compiler bug rather than a shape to handle: the
/// refinement has nowhere to go and the filter would be **silently dropped**
/// (planning reifies it off `expr.ty.domain()`, and no pass after this one could
/// recover it). Assert rather than drop it quietly.
fn refine_source_domain(source: &mut Expr, refinement: Refinement) {
    if let Type::Fun {
        domain, codomain, ..
    } = &source.ty
    {
        let refined_domain =
            crate::ccl::ccl_utils::refine_with_bare((**domain).clone(), &refinement.predicate);
        let codomain = (**codomain).clone();
        let target = Type::fun_like(&source.ty, refined_domain, codomain);
        // `take` rather than clone: the source subtree can be arbitrarily large and
        // the placeholder is overwritten on the next line.
        let inner = std::mem::replace(source, Expr::lit(Lit::Unit));
        *source = make_cast(inner, target.clone()).with_ty(target);
        return;
    }
    // Not a `debug_assert!`: the failure this guards is a *dropped filter*, which is
    // a wrong answer rather than a crash, so a release build must not sail past it.
    unreachable!(
        "refine_source_domain: channel source is not a function type ({}); \
         its filter refinement would be silently dropped",
        source.ty
    );
}

/// Collapse every `ExprStmt(e, b)` to `b`, recursing structurally.
///
/// Safe to do after the main channelize walk: every remaining `e` is pure
/// (its `Feed`/`Define` sites have been extracted, leaving `Unit`
/// residue), so dropping it is value-preserving.
fn drop_expr_stmts(expr: Expr) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;
    let new_node = match node {
        TypedExprNode::Comprehension { .. } => {
            unreachable!(
                "a Comprehension reached channelize; the comprehension phase eliminates it"
            )
        }
        // `mut_elim::run` (before channelize) eliminates every mutable variable
        // introduction, so this arm is unreachable in the production pipeline.
        TypedExprNode::MutDecl { .. } => {
            unreachable!("a MutDecl reached channelize; mut_elim must have eliminated it")
        }
        // Defensive: a `For`/`MutWrite` marker is load-bearing structure, not
        // extracted-feed residue, so keep the `ExprStmt` rather than dropping
        // its effect. `mut_elim::run` (before channelize) eliminates every
        // marker, so this arm is unreachable in the production pipeline;
        // keeping it means a stray marker is passed through to the
        // strict `typecheck` backstop instead of being silently discarded.
        TypedExprNode::ExprStmt { expr: effect, body } if contains_phase_marker(&effect) => {
            TypedExprNode::ExprStmt {
                expr: Box::new(drop_expr_stmts(*effect)),
                body: Box::new(drop_expr_stmts(*body)),
            }
        }
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
        TypedExprNode::Cast { value, target } => TypedExprNode::Cast {
            value: Box::new(drop_expr_stmts(*value)),
            target,
        },
        TypedExprNode::Realize(value) => TypedExprNode::Realize(Box::new(drop_expr_stmts(*value))),
        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(drop_expr_stmts(*left)),
            op,
            right: Box::new(drop_expr_stmts(*right)),
        },
        TypedExprNode::UnaryOp(op, inner) => {
            TypedExprNode::UnaryOp(op, Box::new(drop_expr_stmts(*inner)))
        }
        TypedExprNode::Lambda { param, body } => TypedExprNode::Lambda {
            param,
            body: Box::new(drop_expr_stmts(*body)),
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
        TypedExprNode::Copair(elts) => {
            TypedExprNode::Copair(elts.into_iter().map(drop_expr_stmts).collect())
        }
        // Kept distinct from the copairing above: this arm *rebuilds* the node, so
        // sharing it would silently turn a disjoint join into a coproduct.
        TypedExprNode::DisjointJoin(elts) => {
            TypedExprNode::DisjointJoin(elts.into_iter().map(drop_expr_stmts).collect())
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
        // `Transact` is born by recognition, which runs *after* channelize
        // (post-`lambda_elim`) — none can reach this pass.
        TypedExprNode::Transact { .. } => {
            unreachable!("channelize: Transact is born by recognition, after this pass")
        }
        // Pure structural recursion: no ExprStmt can hide from the walk
        // inside a binding body.
        TypedExprNode::LetRec { bindings, body } => TypedExprNode::LetRec {
            bindings: bindings
                .into_iter()
                .map(|(b, def)| (b, drop_expr_stmts(def)))
                .collect(),
            body: Box::new(drop_expr_stmts(*body)),
        },
        // Pre-phase markers: `mut_elim::run` eliminates these before
        // channelize, so these arms are defensive (a stray marker recurses
        // structurally and reaches the strict `typecheck` backstop; its interior
        // ExprStmt chain is kept by the marker-bearing arm above).
        TypedExprNode::For { target, iter, body } => TypedExprNode::For {
            target,
            iter: Box::new(drop_expr_stmts(*iter)),
            body: Box::new(drop_expr_stmts(*body)),
        },
        TypedExprNode::MutWrite { name, key, value } => TypedExprNode::MutWrite {
            name,
            key: key.map(|k| Box::new(drop_expr_stmts(*k))),
            value: Box::new(drop_expr_stmts(*value)),
        },
        TypedExprNode::Begin { body } => TypedExprNode::Begin {
            body: Box::new(drop_expr_stmts(*body)),
        },
        // Feed/Define get caught by assert_no_defer_residue downstream.
        node @ (TypedExprNode::Feed { .. }
        | TypedExprNode::Define { .. }
        | TypedExprNode::Defer
        | TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::LoadFrom(_)) => node,
        TypedExprNode::Error => crate::unexpected_error_node!(),
        // A tagged-variant value carries no ExprStmt of its own; recurse into
        // the payload so a nested one is dropped.
        TypedExprNode::VariantCtor { tag, payload } => TypedExprNode::VariantCtor {
            tag,
            payload: Box::new(drop_expr_stmts(*payload)),
        },
    };
    TypedExpr {
        node: new_node,
        ty,
        user_annotation,
        node_id,
    }
}

/// Whether the subtree contains a pre-phase marker node (`For`/`MutWrite`)
/// that the unified letrec phase consumes downstream of channelize. Used to
/// keep marker-bearing `ExprStmt`s alive through [`drop_expr_stmts`].
fn contains_phase_marker(expr: &Expr) -> bool {
    if matches!(
        expr.node,
        TypedExprNode::For { .. } | TypedExprNode::MutWrite { .. }
    ) {
        return true;
    }
    let mut found = false;
    expr.walk_children(|c| found = found || contains_phase_marker(c));
    found
}

/// Confirm that no `Defer`/`Feed`/`Define` nodes remain after channelize, and
/// report the first one left at itself.
fn assert_no_defer_residue(expr: &Expr) -> Result<(), Located<DeferError>> {
    match &expr.node {
        TypedExprNode::Comprehension { .. } => {
            unreachable!(
                "a Comprehension reached channelize; the comprehension phase eliminates it"
            )
        }
        // `mut_elim::run` (before channelize) eliminates every mutable variable
        // introduction, so this arm is unreachable in the production pipeline.
        TypedExprNode::MutDecl { .. } => {
            unreachable!("a MutDecl reached channelize; mut_elim must have eliminated it")
        }
        TypedExprNode::Defer => Err(Located::new(
            DeferError::UnboundDeferHandle(Name::from("<defer>")),
            expr.node_id,
        )),
        TypedExprNode::DisjointJoin(elts) => elts.iter().try_for_each(assert_no_defer_residue),
        TypedExprNode::Feed { name, .. } | TypedExprNode::Define { name, .. } => Err(Located::new(
            DeferError::UnboundDeferHandle(name.clone()),
            expr.node_id,
        )),
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
        TypedExprNode::Cast { value, .. } | TypedExprNode::Realize(value) => {
            assert_no_defer_residue(value)
        }
        TypedExprNode::Begin { body } => assert_no_defer_residue(body),
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
        | TypedExprNode::Copair(elts) => elts.iter().try_for_each(assert_no_defer_residue),
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
        TypedExprNode::Transact { .. } => {
            unreachable!("channelize: Transact is born by recognition, after this pass")
        }
        TypedExprNode::ExprStmt { expr, body } => {
            assert_no_defer_residue(expr)?;
            assert_no_defer_residue(body)
        }
        // Pure structural check over the group's bodies.
        TypedExprNode::LetRec { bindings, body } => {
            bindings
                .iter()
                .try_for_each(|(_, def)| assert_no_defer_residue(def))?;
            assert_no_defer_residue(body)
        }
        // Pre-phase markers are not defer residue (v1 lowering guarantees no
        // defer nodes inside them); check their subtrees structurally.
        TypedExprNode::For { iter, body, .. } => {
            assert_no_defer_residue(iter)?;
            assert_no_defer_residue(body)
        }
        TypedExprNode::MutWrite { key, value, .. } => {
            if let Some(key) = key {
                assert_no_defer_residue(key)?;
            }
            assert_no_defer_residue(value)
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::LoadFrom(_) => Ok(()),
        TypedExprNode::Error => crate::unexpected_error_node!(),
        TypedExprNode::VariantCtor { payload, .. } => assert_no_defer_residue(payload),
    }
}

/// Recursively walk `expr`, looking for `let d = Defer in body` bindings.
///
/// When found, processes the binding via [`channelize_defer`] (feed path) or
/// inlines the define value directly (define path).  All other nodes are
/// recursed into structurally.
fn channelize_expr(expr: Expr, ctx: &mut ChannelizeCtx) -> Result<Expr, Located<DeferError>> {
    // One stack frame per node over the whole tree; grow on demand, as the other
    // pass-level walks do.
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || channelize_inner(expr, ctx))
}

fn channelize_inner(expr: Expr, ctx: &mut ChannelizeCtx) -> Result<Expr, Located<DeferError>> {
    if matches!(expr.node, TypedExprNode::Error) {
        crate::unexpected_error_node!();
    }
    let TypedExpr {
        node,
        ty,
        user_annotation,
        node_id,
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
            // Alongside the term names, capture each defer's *channel-domain
            // name* off its recorded handle type — the name consumer types
            // carry, which the cluster's domain recording keys on (it differs
            // from the term name for a specialization clone).
            let mut chan_names: HashMap<Name, Name> = HashMap::new();
            if let Some((n, _)) =
                handle_chan_dom(&binding.ty).or_else(|| handle_chan_dom(&bound_expr.ty))
            {
                chan_names.insert(binding.name.clone(), n);
            }
            ctx.defer_decls.insert(binding.name.clone(), node_id);
            // And each defer's element type, which types the union of its feeds.
            let mut elements: HashMap<Name, Type> = HashMap::new();
            if let Some(element) =
                handle_element(&binding.ty).or_else(|| handle_element(&bound_expr.ty))
            {
                elements.insert(binding.name.clone(), element);
            }
            let mut defer_names = vec![binding.name];
            let mut current_body = *body;
            loop {
                let cur_let_id = current_body.node_id;
                match current_body.node {
                    TypedExprNode::Let {
                        binding: b,
                        bound_expr: be,
                        body: inner,
                    } if matches!(be.node, TypedExprNode::Defer) => {
                        if let Some((n, _)) =
                            handle_chan_dom(&b.ty).or_else(|| handle_chan_dom(&be.ty))
                        {
                            chan_names.insert(b.name.clone(), n);
                        }
                        ctx.defer_decls.insert(b.name.clone(), cur_let_id);
                        if let Some(element) =
                            handle_element(&b.ty).or_else(|| handle_element(&be.ty))
                        {
                            elements.insert(b.name.clone(), element);
                        }
                        defer_names.push(b.name);
                        current_body = *inner;
                    }
                    other => {
                        current_body = TypedExpr {
                            node: other,
                            ty: current_body.ty,
                            user_annotation: current_body.user_annotation,
                            // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                            node_id: cur_let_id,
                        };
                        break;
                    }
                }
            }
            // Recurse into the body first to handle any nested
            // non-clustered defers (inner `let d = Defer in ...`
            // separated from this cluster by other lets).
            let body_rewritten = channelize_expr(current_body, ctx)?;
            // The recording names the **outermost** `let d = Defer`: the cluster's
            // whole product replaces it. A cluster's inner defers are consumed too but
            // are not named, because naming them would assert they die, and a
            // defer whose handle survives in a type does not.
            let _g =
                provenance::enter(node_id, "channelize.cluster", provenance::Nature::Expansion);
            channelize_cluster(&defer_names, &chan_names, &elements, body_rewritten, ctx)
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
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
            if is_lift_shape(&bound_expr) {
                // Read before the lift consumes the binding.
                let (outer, lvl) = handle_chan_dom(&binding.ty)
                    .unwrap_or_else(|| (binding.name.clone(), crate::ccl::ChanLevel(0)));
                // The lift *mints*: `channelize_substitute` replaces the inner
                // scope's trailing `Var` with the outer body, and any `ExprStmt`
                // prefix is rebuilt onto the lifted spine. Those products stand in
                // for this `let`, which the lift consumes, so the recording names it.
                // `Machinery` — merging two defer scopes is plumbing that undoes an
                // inlining artifact, not anything the user wrote.
                //
                // The recursion below runs outside the recording, so a nested lift
                // attributes to its own `let`.
                let lift = {
                    let _g = provenance::enter(
                        node_id,
                        "channelize.defer_lift",
                        provenance::Nature::Machinery,
                    );
                    lift_defer(&binding.name, *bound_expr, &body)
                };
                // The lift renames the inner defer binder to the outer name,
                // but *consumer types outside the lifted subtree* may carry
                // the inner handle's rigid `ChanDom`. Record the alias so the
                // final substitution closes `chan(inner) ↦ chan(outer) ↦
                // concrete`. Both sides key on the *channel-domain names the
                // recorded handle types carry* — for a specialization clone
                // these differ from the term binder names (channel identity
                // is per-instantiation, freshened at `specialize_use`), and
                // post-freshening the two scopes usually already share one
                // name, in which case no entry is needed. Term names are the
                // fallback for handles whose type records no domain.
                let inner_key = lift
                    .inner_chan_dom
                    .map(|(n, _)| n)
                    .unwrap_or(lift.inner_name);
                if inner_key != outer {
                    ctx.resolved_domains
                        .push((inner_key, Type::ChanDom(outer, lvl)));
                }
                return channelize_expr(lift.expr, ctx);
            }
            // Let-of-defer-returning-let collapse: `let y = (let z =
            // E in Var(z)) in body_y` is equivalent to `let z = E in
            // body_y[y → z]`.  Surfaces a deeper `Defer` (inside E)
            // so the outer defer lift can fire on a subsequent
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
                // This arm rebuilds: it copies the inner scope out of the
                // borrowed tree and splices the outer body into its tail, so the
                // collapsed `let` and both copies are new nodes standing in for
                // this `let`. Same parent and same reason as the lift above.
                let _g = provenance::enter(
                    node_id,
                    "channelize.defer_collapse",
                    provenance::Nature::Machinery,
                );
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
                let renamed = channelize_rename(spliced, &inner_name, &binding.name);
                // Same alias recording as the lift above — types outside this
                // subtree may carry the inner handle's rigid name.
                let inner_key = handle_chan_dom(&inner_binding.ty)
                    .map(|(n, _)| n)
                    .unwrap_or_else(|| inner_name.clone());
                let (outer, lvl) = handle_chan_dom(&binding.ty)
                    .unwrap_or_else(|| (binding.name.clone(), crate::ccl::ChanLevel(0)));
                if inner_key != outer {
                    ctx.resolved_domains
                        .push((inner_key, Type::ChanDom(outer, lvl)));
                }
                let collapsed = Expr::let_bind(binding.name.clone(), inner_be, renamed);
                drop(_g);
                return channelize_expr(collapsed, ctx);
            }
            // Recurse first so any inner aliases / UDF-inlines get
            // resolved before we check this outer binding.
            let bound_expr = channelize_expr(*bound_expr, ctx)?;
            let body = channelize_expr(*body, ctx)?;
            // Alias inlining (`let y = Var(x) in body` → `body[y → x]`) is
            // `inline`'s job, not channelize's: `inline` unconditionally collapses
            // a bare-`Var` alias before this pass runs — post-uniquify its
            // `!is_let_bound(x)` guard always holds, since a unique `x` is never
            // re-bound in the body. So a bare-`Var` alias whose body feeds the
            // alias handle must never reach here; a survivor would silently
            // mis-route `Feed(y, …)` to the wrong handle. Assert that loudly in
            // debug rather than re-implementing the collapse. (The defer-*returning*
            // lifts above — `lift_defer` / the collapse — survive `inline`
            // because their bound-expr is a `let`, not a bare `Var`.)
            #[cfg(debug_assertions)]
            {
                if matches!(&bound_expr.node, TypedExprNode::Var(_)) {
                    debug_assert!(
                        !contains_feed_or_define_for(&body, &binding.name),
                        "channelize: a defer alias `let {} = <var>` with a feed for \
                         it survived inline — expected `inline` to collapse it (see \
                         module docs)",
                        binding.name
                    );
                }
            }
            Ok(TypedExpr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr: Box::new(bound_expr),
                    body: Box::new(body),
                },
                ty,
                user_annotation,
                node_id,
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
                node_id,
            };
            expr.try_map_children(|c| channelize_expr(c, ctx))?;
            Ok(expr)
        }
    }
}

/// The element type of a feed handle: what one `<<` appends. It types a channel's union
/// ([`copair_type`]), and decides nothing about the channel's shape.
fn handle_element(ty: &Type) -> Option<Type> {
    ty.as_feed().map(|(_, element)| element.clone())
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
/// union via [`TypedExprNode::Copair`], a `Define` value is
/// used directly, and top-level scalar feeds are lifted to `Fun(Unit,
/// T)` via the `λ __unused → V` wrap inside `extract_for_defer`.
fn channelize_cluster(
    defer_names: &[Name],
    chan_names: &HashMap<Name, Name>,
    elements: &HashMap<Name, Type>,
    body: Expr,
    ctx: &mut ChannelizeCtx,
) -> Result<Expr, Located<DeferError>> {
    // Extract feeds/defines for each defer.  `rewritten` accumulates the
    // body's Feed/Define replacements as we process each defer in turn.
    let mut channels: HashMap<Name, Expr> = HashMap::new();
    let mut rewritten = body;
    for name in defer_names.iter().rev() {
        // Process innermost defer first so its feeds are picked up before
        // the outer defer's walk; the outer walk wouldn't see them anyway
        // since extract_for_defer matches by name.  Processing order is
        // not load-bearing here because each defer extracts only its own
        // feeds.
        let mut feeds = Vec::new();
        let mut define: Option<(NodeId, Expr)> = None;
        rewritten = extract_for_defer(rewritten, name, &mut feeds, &mut define, false)?;
        let feeds: Vec<Expr> = feeds
            .into_iter()
            .map(
                |Contribution {
                     value,
                     levels,
                     feed,
                 }| {
                    // Keying the contribution by the tuple of its positions is still building
                    // what its `Feed` became.
                    let _g =
                        provenance::enter(feed, "channelize.feed", provenance::Nature::Expansion);
                    match classify_nest(&value, levels) {
                        Nest::Product(generators) => nest_as_product(value, generators),
                        Nest::Indexed => {
                            flatten_nested_contribution(indexed_nest(value, levels), levels)
                        }
                        Nest::Flat => flatten_nested_contribution(value, levels),
                    }
                },
            )
            .collect();
        let channel = match (feeds.is_empty(), define) {
            (true, None) => {
                return Err(ctx.at_declaration(DeferError::NoFeedOrDefine(name.clone())));
            }
            (true, Some((_, d))) => d,
            (false, None) => combine_feed_values(feeds, elements.get(name)),
            (false, Some((define_id, _))) => {
                return Err(Located::new(
                    DeferError::FeedsAndDefinesMixed(name.clone()),
                    define_id,
                ));
            }
        };
        channels.insert(name.clone(), channel);
    }
    // Record each channel's concrete domain under its nominal name — the
    // *channel-domain name off the defer's handle type* (`chan_names`), not
    // the term binder name: a specialization clone's binder is uid-shared
    // across specializations while its handle carries the per-instantiation
    // freshened name consumer types reference. The domain comes off the
    // assembled channel's constructed type (`Fun`), or — for an alias channel
    // that is itself a defer read (`x <<= y` leaves `Var(y) : feed(…)`) — off
    // the read's handle type, whose domain is the referenced channel's own
    // `ChanDom` (closed later).
    for name in defer_names {
        if let Some(ch) = channels.get(name) {
            let key = chan_names
                .get(name)
                .cloned()
                .unwrap_or_else(|| name.clone());
            // A non-function channel type records no domain; any consumer
            // still holding its `ChanDom` surfaces at the debug residue
            // assert / strict wall.
            if let Some(dom) = channel_domain_of(&ch.ty) {
                if let Some(k) = ch.ty.fun_kind() {
                    ctx.channel_kinds.push((key.clone(), k.clone()));
                }
                ctx.resolved_domains.push((key, dom));
            }
        }
    }
    // Uniquification runs before channelization, so a channel's captured free
    // variable is never shadowed by a `Let` on the wrap-to-feed spine (a body
    // binder and a captured outer variable never share a `uid`). Enforce that
    // invariant in debug.
    #[cfg(debug_assertions)]
    assert_no_shadowed_captures(&rewritten, &channels);
    // The cluster becomes a **mutually-scoped `Feed`-kind letrec group** —
    // the model's "feeds are the letrec's outputs" — so binding order inside
    // the group is immaterial and no topological sort is needed at emission.
    // What a sort used to reject, the letrec causality rule now rejects:
    // channels carry no guard, so a reference cycle among them
    // (`x <<= y; y <<= x`) has no well-founded solution — the same law that
    // governs overwrite recursion, applied by the same checker.
    let mut group: Vec<(TypedBinding, Expr)> = Vec::with_capacity(defer_names.len());
    for name in defer_names {
        if let Some(channel) = channels.remove(name) {
            group.push((
                TypedBinding {
                    name: name.clone(),
                    ty: channel.ty.clone(),
                    user_annotation: None,
                    transparency: BindingTransparency::Transparent,
                },
                channel,
            ));
        }
    }
    if let Err(errs) = check_letrec_causal(&group) {
        let name = errs[0]
            .cycle
            .first()
            .expect("cycle names a binding")
            .clone();
        return Err(ctx.at_declaration(DeferError::MutuallyRecursiveCycle(name)));
    }
    Ok(bind_cluster_at_scope(rewritten, group))
}

/// Debug invariant: channelization relies on **Barendregt uniqueness**
/// (`uniquify` runs before it), so a channel's captured free variable is never
/// rebound by a `Let` on the wrap-to-feed spine — a body binder and a captured
/// outer variable never share a `uid`, so the emitted `let d = channel` can't
/// be shadow-captured. (A channel legitimately referencing a body-*internal*
/// binding — e.g. an accumulator — is excluded: such a name is bound in
/// `body`, hence not free in it, so it never lands in the checked set.) A
/// violation would mean a duplicate binder `uid` reached channelization (e.g. an
/// un-freshened `inline` duplication); catch it loudly here rather than silently
/// mis-scoping a channel.
#[cfg(debug_assertions)]
fn assert_no_shadowed_captures(body: &Expr, channels: &HashMap<Name, Expr>) {
    // Scope-aware in types too: a node's type stands where the node does, so a dependent
    // type under a `let` names the `let`'s binder without capturing it.
    let channel_fvs: HashSet<Name> = channels
        .values()
        .flat_map(crate::ccl::ccl_utils::free_names)
        .collect();
    let body_fvs = crate::ccl::ccl_utils::free_names(body);
    let protected: HashSet<Name> = channel_fvs.intersection(&body_fvs).cloned().collect();
    fn walk(e: &Expr, protected: &HashSet<Name>) {
        if let TypedExprNode::Let { binding, .. } = &e.node {
            debug_assert!(
                !protected.contains(&binding.name),
                "channelize: body binding `{}` shadows a channel-captured free \
                 variable — uniquification invariant violated (see module docs)",
                binding.name
            );
        }
        e.walk_children(|c| walk(c, protected));
    }
    walk(body, &protected);
}

/// Walk `expr` through `Let` / `ExprStmt` bodies to the scope where the
/// cluster's `let d_i = channel_i` bindings belong, then emit them there in
/// topological order ([`emit_cluster_then`]). The bindings land at the body's
/// terminal, *or* earlier — just above the first `Let` whose bound expression
/// references a cluster name — so a cross-referencing defer is always bound
/// before its use (the cross-cluster case in the module docs).
///
/// There is no shadow α-renaming: uniquification guarantees a channel's captured
/// free variable is never rebound on this spine
/// ([`assert_no_shadowed_captures`] checks it in debug).
fn bind_cluster_at_scope(expr: Expr, group: Vec<(TypedBinding, Expr)>) -> Expr {
    let TypedExpr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // If this Let's `bound_expr` references any of the cluster's binding
            // names, emit the cluster's bindings *here* (before this Let) rather
            // than continuing to the body's terminal — otherwise the cluster
            // binding would be lexically after the reference and unbound at its
            // use site.
            //
            // Triggered most commonly when an *inner* cluster's processing left a
            // `let y = Var(x)` in the chain (`y`'s channel was `Var(x)` of an
            // outer defer) and the outer cluster's wrap now needs to put
            // `let x = …` before that `let y`. See `test_feed_and_define_operators`
            // cases 10–11 for the cross-cluster-references-through-intervening-let
            // pattern this targets.
            let references_cluster = group
                .iter()
                .any(|(b, _)| count_free(&b.name, &bound_expr) > 0);
            if references_cluster {
                let original_let = TypedExpr {
                    node: TypedExprNode::Let {
                        binding,
                        bound_expr,
                        body,
                    },
                    ty,
                    user_annotation,
                    node_id,
                };
                return emit_cluster_letrec(original_let, group);
            }
            TypedExpr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(bind_cluster_at_scope(*body, group)),
                },
                ty,
                user_annotation,
                node_id,
            }
        }
        TypedExprNode::ExprStmt { expr: e, body } => TypedExpr {
            node: TypedExprNode::ExprStmt {
                expr: e,
                body: Box::new(bind_cluster_at_scope(*body, group)),
            },
            ty,
            user_annotation,
            node_id,
        },
        // A letrec's continuation is the scope its trailing reads live in, and
        // a channel assembled from the group's taps (`__hist ≫ .__to_<feed>`)
        // *captures a group binder* — so the cluster must bind BELOW the
        // group, inside its body, or the capture dangles. (Emitting above is
        // required only in the inverse case — a group binding referencing a
        // channel name — mirroring the `Let` bound-expression guard.)
        TypedExprNode::LetRec { bindings, body } => {
            let group_references_cluster = group
                .iter()
                .any(|(b, _)| bindings.iter().any(|(_, def)| count_free(&b.name, def) > 0));
            if group_references_cluster {
                let original = TypedExpr {
                    node: TypedExprNode::LetRec { bindings, body },
                    ty,
                    user_annotation,
                    node_id,
                };
                return emit_cluster_letrec(original, group);
            }
            TypedExpr {
                node: TypedExprNode::LetRec {
                    bindings,
                    body: Box::new(bind_cluster_at_scope(*body, group)),
                },
                ty,
                user_annotation,
                node_id,
            }
        }
        other => {
            let terminal = TypedExpr {
                node: other,
                ty,
                user_annotation,
                node_id,
            };
            emit_cluster_letrec(terminal, group)
        }
    }
}

/// Wrap `inner` in the cluster's **`Feed`-kind letrec group** — every channel
/// mutually in scope, so cross-channel references (`x <<= y`, in either
/// direction) need no ordering. Recognition flattens the (causality-checked,
/// therefore acyclic) group back to plain `let`s in dependency order for
/// planning. An alias channel (`x <<= y`) leaves its binding typed by the
/// read's handle, whose rigid `ChanDom` the final [`erase_chan_domains`]
/// substitution closes.
fn emit_cluster_letrec(inner: Expr, group: Vec<(TypedBinding, Expr)>) -> Expr {
    if group.is_empty() {
        return inner;
    }
    let ty = inner.ty.clone();
    // A freshly-minted cluster `LetRec` — not a rebuild of an input node, so it
    // draws a fresh `NodeId` through the canonical `Expr::new` constructor.
    let mut cluster = Expr::new(TypedExprNode::LetRec {
        bindings: group,
        body: Box::new(inner),
    });
    cluster.ty = ty;
    cluster
}

/// Collect every free `Var` name in `expr` into `out`, respecting
/// shadowing by enclosing `Let`/`Lambda` bindings on the term spine.
///
/// Also walks references hidden in **type positions**:
/// - `expr.ty` refinement predicates (including a lambda's refined domain)
/// - `expr.user_annotation` refinement predicates (set by
///   [`extract_for_defer`]'s filter-feed rewrite)
///
/// Without these, a channel that references an outer let-binding only
/// through a refinement predicate would be missed by
/// [`assert_no_shadowed_captures`], leaving a downstream `Let` shadow
/// undetected and the channel silently reading the wrong value at the
/// cluster bind site.
///
/// Shadowing inside type-position predicates is intentionally not
/// tracked — the goal here is "does the channel reference this name
/// anywhere," not "does the name occur free per lexical-scope
/// rules."  This matches [`crate::ccl::ccl_utils::count_free`]'s
/// behaviour on type refinements.
fn collect_free_vars(expr: &Expr, out: &mut HashSet<Name>) {
    fn rec(expr: &Expr, bound: &mut Vec<Name>, out: &mut HashSet<Name>) {
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
            TypedExprNode::Lambda { param, body } => {
                // Domain refinements ride the param's *type*, visited
                // unconditionally by the `collect_free_vars_in_type(&expr.ty)`
                // call at the top of `rec` (they belong to the outer scope).
                bound.push(param.name.clone());
                rec(body, bound, out);
                bound.pop();
            }
            _ => expr.walk_children(|c| rec(c, bound, out)),
        }
    }
    let mut bound = Vec::new();
    rec(expr, &mut bound, out);
}

/// Walk `ty` for any [`Refinement`](crate::ccl::Refinement) predicate expressions and
/// collect their free variables into `out`.  Structural recursion via
/// [`Type::walk_children`] so every compound type variant (`Fun`,
/// `Tuple`, `Record`, `Variant`) is covered uniformly.
///
/// `try_borrow().ok()` silently treats an actively-mutated predicate
/// as "no references"; callers run between passes when no predicate
/// is being walked elsewhere, so the under-count is safe in practice.
fn collect_free_vars_in_type(ty: &Type, out: &mut HashSet<Name>) {
    // Refinement predicates are themselves CCL expressions; recurse into them
    // through `collect_free_vars` so their own type-position predicates and
    // shadowing are handled consistently.
    for refinement in ty.refinements() {
        collect_free_vars(&refinement.predicate, out);
    }
    ty.walk_children(|child| collect_free_vars_in_type(child, out));
}

/// Collect every defer-target name referenced by a `Feed`/`Define`
/// node in `expr`, respecting `Let`/`Lambda` shadowing on the term
/// spine, returned in deterministic (sorted) order.
///
/// Used only by [`extract_for_defer`]'s debug assertion that a
/// pre-phase `For`/`MutWrite` marker carries no feeds.
fn collect_feed_target_names(expr: &Expr) -> Vec<Name> {
    fn rec(expr: &Expr, bound: &mut Vec<Name>, out: &mut HashSet<Name>) {
        match &expr.node {
            TypedExprNode::Comprehension { .. } => unreachable!(
                "a Comprehension reached channelize; the comprehension phase eliminates it"
            ),
            TypedExprNode::MutDecl { .. } => {
                unreachable!("a MutDecl reached channelize; mut_elim must have eliminated it")
            }
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
            TypedExprNode::Cast { value, .. } | TypedExprNode::Realize(value) => {
                rec(value, bound, out)
            }
            TypedExprNode::Begin { body } => rec(body, bound, out),
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
            | TypedExprNode::Copair(elts)
            | TypedExprNode::DisjointJoin(elts) => {
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
            TypedExprNode::Transact { .. } => {
                unreachable!("channelize: Transact is born by recognition, after this pass")
            }
            TypedExprNode::ExprStmt { expr: e, body } => {
                rec(e, bound, out);
                rec(body, bound, out);
            }
            // Every group binder shadows across all binding bodies and the
            // letrec body (mutual recursion).
            TypedExprNode::LetRec { bindings, body } => {
                for (b, _) in bindings {
                    bound.push(b.name.clone());
                }
                for (_, def) in bindings {
                    rec(def, bound, out);
                }
                rec(body, bound, out);
                for _ in bindings {
                    bound.pop();
                }
            }
            // Pre-phase markers: the target binder scopes the loop body; a
            // `MutWrite` names a mutable variable, not a feed target.
            TypedExprNode::For { target, iter, body } => {
                rec(iter, bound, out);
                bound.push(target.name.clone());
                rec(body, bound, out);
                bound.pop();
            }
            TypedExprNode::MutWrite { key, value, .. } => {
                if let Some(key) = key {
                    rec(key, bound, out);
                }
                rec(value, bound, out);
            }
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::LoadFrom(_)
            | TypedExprNode::Defer => {}
            TypedExprNode::Error => crate::unexpected_error_node!(),
            TypedExprNode::VariantCtor { payload, .. } => rec(payload, bound, out),
        }
    }
    let mut targets: HashSet<Name> = HashSet::new();
    rec(expr, &mut Vec::new(), &mut targets);
    let mut sorted: Vec<Name> = targets.into_iter().collect();
    // Deterministic order so generated field names compare reliably.
    sorted.sort();
    sorted
}

/// A single feed value passes through unchanged.  Multiple feed values
/// are merged via [`TypedExprNode::Copair`] — the dedicated
/// N-ary collection-union node — which compiles to a `UnionOperator`
/// downstream.
///
/// The union is stamped with its type at construction (mirroring
/// `emit_copair`): one `FieldKey::Index(i)` domain tag per operand
/// `i`, over the shared element codomain, `element` where the handle states it. A
/// defer-read operand contributes its handle's rigid `ChanDom` domain, closed by the final
/// [`erase_chan_domains`] substitution.
fn combine_feed_values(mut feeds: Vec<Expr>, element: Option<&Type>) -> Expr {
    debug_assert!(!feeds.is_empty());
    if feeds.len() == 1 {
        return feeds.pop().unwrap();
    }
    // `copair_type` stamps one `Index(i)` tag per operand, while `Expr::copair`
    // *splices* an operand that is itself a copairing — so a `Copair` feed value would
    // leave the node with more operands than its type has tags. It cannot arise here: a
    // feed value is a lambda, a compose or an apply, because a feed outside any iteration
    // is lifted into a lambda however its value is built. The splice is silent, so state
    // the precondition rather than leaving a future feed path to discover it.
    debug_assert!(
        !feeds
            .iter()
            .any(|f| matches!(f.node, TypedExprNode::Copair(_))),
        "combine_feed_values: a feed value is itself a copairing, so `Expr::copair` \
         splices it and the stamped type's {} tags no longer describe the node's operands",
        feeds.len()
    );
    let ty = copair_type(&feeds, element);
    Expr::copair(feeds).with_ty(ty)
}

/// The type of an N-ary channel union: `Variant[Index(i) ↦ domainᵢ] ⤇ cod`,
/// where each operand contributes its domain as tag `i` and they share a
/// common element codomain. Returns [`Type::Hole`] when an operand is not a
/// function-shaped type at all (the untyped-mode pipeline); a defer-read
/// operand is function-shaped via its handle's read view, so typed-mode
/// unions are concrete-modulo-`ChanDom` at construction.
///
/// `cod` is `element`, the channel's element type off its handle, where the handle states
/// one: inference constrains every contribution into it, so it is their join. Two jagged rows
/// `box([1])` and `box([2, 3])` differ in their witness kinds, which the join below, over
/// refinements only, does not reach.
fn copair_type(feeds: &[Expr], element: Option<&Type>) -> Type {
    let mut tags: Vec<(crate::ccl::FieldKey, Type)> = Vec::with_capacity(feeds.len());
    let mut cod: Option<Type> = None;
    for (i, f) in feeds.iter().enumerate() {
        match f.ty.peel_refinements() {
            Type::Fun {
                domain, codomain, ..
            } => {
                tags.push((crate::ccl::FieldKey::Index(i), (**domain).clone()));
                match &cod {
                    None => cod = Some((**codomain).clone()),
                    // The channel's element type is the **join** of its
                    // contributions, so a refinement only survives if every one of them
                    // establishes it: `c << 1` and `c << 2` contribute
                    // `{Int | __elem == 1}` and `{Int | __elem == 2}` and the channel
                    // is a plain `Int`. This is the mutable variable law (`emit`'s `MutWrite`
                    // rule) for the append-kind history: a channel is not one value
                    // but the sequence its contributions produce.
                    Some(c) if c != &**codomain => {
                        cod = Some(join_refinements(c, codomain));
                    }
                    // Every `<<` contribution to one channel is constrained into
                    // the channel's shared `value` var at inference, so the
                    // operand element types must already agree — taking operand
                    // 0's codomain is only sound under that invariant. Name it:
                    // a future feed path bypassing the shared-channel constraint
                    // would otherwise mis-type the union to operand 0 silently.
                    //
                    // Compared modulo **refinements**: the invariant is that the
                    // operands share an element *type*, and contributions
                    // legitimately differ in what each one additionally knows about
                    // its own value (`c << 1` and `c << 2` contribute
                    // `{Int | __elem == 1}` and `{Int | __elem == 2}`). The channel's
                    // element type is what they have in common, which is what
                    // operand 0's codomain stands in for.
                    Some(c) => debug_assert_eq!(
                        crate::ccl::ccl_utils::strip_refinements(&c.without_pi_names()),
                        crate::ccl::ccl_utils::strip_refinements(&codomain.without_pi_names()),
                        "copair_type: feed operands disagree on element \
                         type ({c} vs {codomain}); inference should have unified \
                         them into the channel's shared value var"
                    ),
                }
            }
            _ => return Type::Hole,
        }
    }
    match element.cloned().or(cod) {
        Some(c) => Type::data_fun(Type::variant(tags), c),
        None => Type::Hole,
    }
}

/// The join of two types that agree modulo refinements: their shared skeleton
/// carrying only the refinements **both** sides establish.
///
/// Refinements are compared structurally, as everywhere else (`Refinement`'s
/// `PartialEq`), and the skeletons must already agree — the caller's
/// `debug_assert` states that invariant.
fn join_refinements(a: &Type, b: &Type) -> Type {
    Type::refined(
        a.peel_refinements().clone(),
        a.refinements()
            .iter()
            .filter(|r| b.refinements().contains(r))
            .cloned()
            .collect(),
    )
}

/// Build a [`TypedExprNode::Compose`] typed `Fun(first-domain, last-codomain)`.
/// With nominal channel domains every element is concrete-modulo-`ChanDom` at
/// construction (the feed-history read view of [`fun_domain`] /
/// [`fun_codomain`]), so a `Hole` here means a genuinely untyped input (the
/// untyped-mode pipeline); the debug residue assert and the strict wall
/// backstop the typed mode.
fn compose_typed_or_hole(elts: Vec<Expr>) -> Expr {
    let d = elts.first().and_then(|e| fun_domain(&e.ty));
    let c = elts.last().and_then(|e| fun_codomain(&e.ty));
    // `fun_like`, not `Type::fun`: the chain is the head read through the rest, so it is a
    // collection exactly when the head is. The head here is routinely a feed handle that
    // `erase_chan_domains` has not yet turned into a `Type::Fun`, which `fun_like` reads as
    // the read view it states.
    match (d, c) {
        (Some(d), Some(c)) => {
            let stated = Type::fun_like(&elts[0].ty, d, c);
            crate::ccl::ccl_utils::chain_typed(elts, stated)
        }
        _ => Expr::compose(elts).with_ty(Type::Hole),
    }
}

/// `λ param → body`, a channel contribution built around a fed value, with the kind of
/// `exemplar`'s function (`Compute` where there is none) and dependent where `body`'s type
/// reads `param`: a row fed in a loop may read the loop's variable
/// (`src/ccl/design/type-inference.md`, "A history's value may depend on its position").
fn contribution_lambda(param: &TypedBinding, body: Expr, exemplar: Option<&Type>) -> Expr {
    let codomain = body.ty.clone();
    let fun_kind = exemplar
        .and_then(
            |t| match Type::fun_like(t, param.ty.clone(), codomain.clone()) {
                Type::Fun { fun_kind, .. } => Some(fun_kind),
                _ => None,
            },
        )
        .unwrap_or(FunKind::Compute);
    let ty = if crate::ccl::subst::type_free_vars(&codomain).contains(&param.name) {
        Type::pi_kinded(param.name.clone(), param.ty.clone(), codomain, fun_kind)
    } else {
        Type::Fun {
            name: None,
            fun_kind,
            domain: Box::new(param.ty.clone()),
            codomain: Box::new(codomain),
        }
    };
    Expr::lambda(&param.name, param.ty.clone(), body).with_ty(ty)
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
/// `in_inner_scope` is `true` when the walk has crossed a [`TypedExprNode::Lambda`]
/// or [`TypedExprNode::Case`] branch boundary — `Define` is disallowed in those
/// contexts since the channelized binding would need to escape the inner scope.
fn extract_for_defer(
    expr: Expr,
    defer_name: &Name,
    feeds: &mut Vec<Contribution>,
    define: &mut Option<(NodeId, Expr)>,
    in_inner_scope: bool,
) -> Result<Expr, Located<DeferError>> {
    // Grow the stack on demand, as `lambda_elim`'s two recursion entries do. This
    // walk descends the whole tree in one stack frame per node, and the frame is large
    // (one `match` over every node kind, so it is sized for the union of all arms)
    // — deep enough trees overflow a test thread's default stack. Every level goes
    // through this wrapper, so each one checks the remaining headroom.
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || {
        extract_for_defer_impl(expr, defer_name, feeds, define, in_inner_scope)
    })
}

/// Check that a walk with `in_inner_scope` set collected no define.
///
/// Such a walk raises [`DeferError::NestedDefinition`] at the `Define` itself,
/// where its node is in hand, so it never fills the slot it is passed.
fn no_inner_define(define: Option<(NodeId, Expr)>) {
    assert!(
        define.is_none(),
        "an inner-scope walk raises NestedDefinition at the Define rather than collecting it"
    );
}

fn extract_for_defer_impl(
    expr: Expr,
    defer_name: &Name,
    feeds: &mut Vec<Contribution>,
    define: &mut Option<(NodeId, Expr)>,
    in_inner_scope: bool,
) -> Result<Expr, Located<DeferError>> {
    let TypedExpr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;
    let node = match node {
        TypedExprNode::Comprehension { .. } => {
            unreachable!(
                "a Comprehension reached channelize; the comprehension phase eliminates it"
            )
        }
        // `mut_elim::run` (before channelize) eliminates every mutable variable
        // introduction, so this arm is unreachable in the production pipeline.
        TypedExprNode::MutDecl { .. } => {
            unreachable!("a MutDecl reached channelize; mut_elim must have eliminated it")
        }
        TypedExprNode::Feed { name, value } if &name == defer_name => {
            // A feed outside any iteration contributes one element, keyed by the unit: its
            // value is lifted to `Unit ⤇ 𝑉`, whatever 𝑉 is, a collection included
            // (`docs/chl-spec.md`, "3.7 Feed operator `<<`": the stream's element type is the
            // type of the value). Inside an iteration scope (a lambda or loop body) the
            // surrounding generator supplies the keys, so the value stays an element: the
            // Compose-with-Lambda case above wraps it with its own `λ x → V` companion.
            let value = *value;
            let feed = node_id;
            let _g = provenance::enter(feed, "channelize.feed", provenance::Nature::Expansion);
            let contribution = if in_inner_scope {
                Contribution {
                    value,
                    levels: 0,
                    feed,
                }
            } else {
                // The channel is a collection — inference says so on the handle, and every
                // read of it is `⤇`. `Expr::lambda` declares `Compute`, so the wrap has to
                // restate what the thing being wrapped is.
                let vty = value.ty.clone();
                Contribution {
                    value: Expr::lambda("__unused", Type::Base(BaseType::Unit), value)
                        .with_ty(Type::data_fun(Type::Base(BaseType::Unit), vty)),
                    levels: 1,
                    feed,
                }
            };
            feeds.push(contribution);
            // The `Feed` wrapper's id is reused onto this `Lit(Unit)` replacement
            // (the enclosing rebuild carries `node_id`) — a preserve, not a
            // discard.
            TypedExprNode::Lit(Lit::Unit)
        }
        TypedExprNode::Define { name, value } if &name == defer_name => {
            if in_inner_scope {
                return Err(Located::new(
                    DeferError::NestedDefinition(defer_name.clone()),
                    node_id,
                ));
            }
            if define.is_some() {
                return Err(Located::new(
                    DeferError::MultipleDefinitions(defer_name.clone()),
                    node_id,
                ));
            }
            *define = Some((node_id, *value));
            TypedExprNode::Lit(Lit::Unit)
        }
        // Pass through Feed/Define for *other* defers — they'll be processed
        // by a different `channelize_defer` call.
        node @ (TypedExprNode::Feed { .. } | TypedExprNode::Define { .. }) => node,
        // Channelization runs *before* lambda elimination (see
        // `design/lowering.md`, "The `channelize` step (feed channelization)"), and
        // a disjoint join is born there — by the `Case` fan-outs — so one cannot
        // reach this walk. Spelled out rather than folded into a child-walk arm
        // because this match *rebuilds* nodes, and quietly rebuilding a disjoint
        // join as something else is the failure worth preventing.
        TypedExprNode::DisjointJoin(_) => {
            unreachable!("DisjointJoin is born by lambda_elim, which runs after channelize")
        }
        // Defensive: `transact_phase` strips every `Begin` before channelize, so
        // this is unreachable in the pipeline; recurse structurally if a stray
        // one survives (reaching the strict typecheck backstop).
        TypedExprNode::Begin { body } => TypedExprNode::Begin {
            body: Box::new(extract_for_defer(
                *body,
                defer_name,
                feeds,
                define,
                in_inner_scope,
            )?),
        },
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_expr =
                extract_for_defer(*bound_expr, defer_name, feeds, define, in_inner_scope)?;
            let body = if &binding.name == defer_name {
                // Inner let shadows the defer name; do not descend.
                *body
            } else {
                // Track which feeds get added during the body walk so we can
                // wrap them with this let's binding if their free vars
                // reference it. Without this, an extracted channel like
                // `Apply(src, λx → V_with_n)` (from a generator function body
                // with `let n = … in for-loop`) would float out to the
                // cluster's bind site with `n` unbound.
                let prev_len = feeds.len();
                let new_body = extract_for_defer(*body, defer_name, feeds, define, in_inner_scope)?;
                // Wrap each feed extracted during the body walk with this
                // let-binding — but only when the feed actually references the
                // binding. A channel that escapes the scope where the binding
                // is bound (a generator body inlined out) needs it carried
                // along; a channel that doesn't mention it must *not* be
                // wrapped, or every channel drags in an unused binding — a whole
                // history record, in the worst case (each `http_serve` reply re-emitting
                // a mutable variable it never reads). The reference test is
                // `collect_free_vars` rather than `count_free` because the
                // binding may be referenced only through a `user_annotation` /
                // refinement predicate (a filter-feed guard); `collect_free_vars`
                // traverses those, so guard-referenced bindings are kept while
                // dead ones are dropped. Inner lets wrap first as the walk
                // unwinds, so a transitively-referenced binding is exposed as
                // free here by the time this (outer) let checks.
                for Contribution {
                    value: feed,
                    feed: feed_id,
                    ..
                } in feeds.iter_mut().skip(prev_len)
                {
                    let mut fvs = HashSet::new();
                    collect_free_vars(feed, &mut fvs);
                    if fvs.contains(&binding.name) {
                        let _g = provenance::enter(
                            *feed_id,
                            "channelize.feed",
                            provenance::Nature::Expansion,
                        );
                        // A `mem::take` slot, overwritten below: minting for it
                        // would log a birth for a node no tree ever holds.
                        let placeholder = Expr::throwaway(TypedExprNode::Lit(Lit::Unit));
                        let original = std::mem::replace(feed, placeholder);
                        // stamp the wrap at construction —
                        // the let's type is its body's, closed over the binder
                        // (the design §6.2 discharge) — there is no
                        // re-derivation pass to fill a `Hole` in. The discharge
                        // payload only feeds `apply_type`, so it is a *template*
                        // rather than a tree node — it keeps its ids, and the
                        // sibling is minted at the read inside `apply_type`.
                        let let_ty = crate::ccl::subst::Subst::discharge(
                            &binding.name,
                            bound_expr.clone_preserving_ids(),
                        )
                        .apply_type(&original.ty);
                        // The `Let` this walk is rebuilding keeps the original
                        // `bound_expr` in the body, and each extracted feed that
                        // captures the binder gets its own re-binding of the same
                        // definition, so every wrap is a copy.
                        *feed = Expr::let_bind(binding.name.clone(), bound_expr.clone(), original)
                            .with_ty(let_ty);
                    }
                }
                new_body
            };
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(bound_expr),
                body: Box::new(body),
            }
        }
        TypedExprNode::ExprStmt { expr: e, body } => TypedExprNode::ExprStmt {
            expr: Box::new(extract_for_defer(
                *e,
                defer_name,
                feeds,
                define,
                in_inner_scope,
            )?),
            body: Box::new(extract_for_defer(
                *body,
                defer_name,
                feeds,
                define,
                in_inner_scope,
            )?),
        },
        TypedExprNode::Apply { function, argument } => {
            // A comprehension's per-element step is `(𝑖 ▷ xs) ▷ (λ x → body)`:
            // the inner apply looks the element up, the outer one runs the
            // per-element lambda on it. So the argument here is an **element**,
            // not the iteration source. When the body feeds, the per-iteration
            // channel is exposed as a companion `argument ▷ (λ x → V)` — the same
            // shape, yielding the feed value instead of `Unit`.
            //
            // Without this special case the inner Lambda would be handled by the
            // generic Lambda arm, which wraps each feed in `λ x → V` — losing the
            // surrounding apply that binds the lambda to its element.
            if matches!(
                &function.node,
                TypedExprNode::Lambda { param, .. } if &param.name != defer_name
            ) {
                // Peeked above by reference; take ownership without cloning the
                // whole function subtree (this runs on every `Apply` walked).
                let TypedExpr {
                    node:
                        TypedExprNode::Lambda {
                            param,
                            body: lambda_body,
                        },
                    ty: function_ty,
                    user_annotation: function_user_annotation,
                    // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                    node_id: function_node_id,
                } = *function
                else {
                    unreachable!("peeked above as a lambda whose param is not the defer binder")
                };
                let mut lambda_feeds: Vec<Contribution> = Vec::new();
                let mut lambda_define: Option<(NodeId, Expr)> = None;
                let new_lambda_body = extract_for_defer(
                    *lambda_body,
                    defer_name,
                    &mut lambda_feeds,
                    &mut lambda_define,
                    true,
                )?;
                no_inner_define(lambda_define);
                let new_argument = extract_for_defer(
                    *argument.clone(),
                    defer_name,
                    feeds,
                    define,
                    in_inner_scope,
                )?;
                for Contribution {
                    value: v,
                    levels,
                    feed,
                } in lambda_feeds
                {
                    let _g =
                        provenance::enter(feed, "channelize.feed", provenance::Nature::Expansion);
                    // `Apply { argument: source-element, function: λ p → v }`
                    // applies the value lambda to the per-element source, so the
                    // companion channel's type is the lambda's codomain `v.ty`
                    // (the argument matches `param.ty`). Typed at construction.
                    // It binds one element, so it adds no position.
                    // A value reading the element reads the argument.
                    let v_ty =
                        crate::ccl::subst::discharge_codomain(&param.name, &new_argument, &v.ty);
                    let channel_lambda = contribution_lambda(&param, v, None);
                    let channel = Expr::apply(new_argument.clone(), channel_lambda).with_ty(v_ty);
                    feeds.push(Contribution {
                        value: channel,
                        levels,
                        feed,
                    });
                }
                let new_function = TypedExpr {
                    node: TypedExprNode::Lambda {
                        param,
                        body: Box::new(new_lambda_body),
                    },
                    ty: function_ty,
                    user_annotation: function_user_annotation,
                    // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                    node_id: function_node_id,
                };
                TypedExprNode::Apply {
                    function: Box::new(new_function),
                    argument: Box::new(new_argument),
                }
            } else {
                let new_function =
                    extract_for_defer(*function, defer_name, feeds, define, in_inner_scope)?;
                let new_argument =
                    extract_for_defer(*argument, defer_name, feeds, define, in_inner_scope)?;
                TypedExprNode::Apply {
                    function: Box::new(new_function),
                    argument: Box::new(new_argument),
                }
            }
        }
        // `realize` wraps a pure value exactly as `cast` does; recurse and keep `target`.
        TypedExprNode::Realize(value) => TypedExprNode::Realize(Box::new(extract_for_defer(
            *value,
            defer_name,
            feeds,
            define,
            in_inner_scope,
        )?)),
        // `cast` wraps a pure value; recurse into it and keep `target`.
        TypedExprNode::Cast { value, target } => TypedExprNode::Cast {
            value: Box::new(extract_for_defer(
                *value,
                defer_name,
                feeds,
                define,
                in_inner_scope,
            )?),
            target,
        },
        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(extract_for_defer(
                *left,
                defer_name,
                feeds,
                define,
                in_inner_scope,
            )?),
            op,
            right: Box::new(extract_for_defer(
                *right,
                defer_name,
                feeds,
                define,
                in_inner_scope,
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
            )?),
        ),
        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(extract_for_defer(
                *input,
                defer_name,
                feeds,
                define,
                in_inner_scope,
            )?),
            kind,
        },
        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(
            elts.into_iter()
                .map(|e| extract_for_defer(e, defer_name, feeds, define, in_inner_scope))
                .collect::<Result<_, _>>()?,
        ),
        TypedExprNode::List(elts) => TypedExprNode::List(
            elts.into_iter()
                .map(|e| extract_for_defer(e, defer_name, feeds, define, in_inner_scope))
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
                let elt_node_id = elt.node_id;
                match elt.node {
                    TypedExprNode::Lambda { param, body } if &param.name != defer_name => {
                        // Feeding `λ p → Case({g₀ → Feed(d, v₀); …; true → Unit})`
                        // becomes one refined-source channel per feeding arm
                        // plus a Lambda whose body collapses to `Unit`.  See
                        // [`try_extract_fanout_feed`].
                        if let Some(fanout_arms) = try_extract_fanout_feed(&body, defer_name) {
                            // Fan the feeding arms out into one refined-source
                            // channel each (unioned via `++` at the cluster bind
                            // site), encoding the `Case`'s first-match order:
                            // arm `i`'s source is restricted to `gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`
                            // ([`synthesize_arm_predicate`]). The two-arm
                            // `if g: d << v` shape is the degenerate
                            // one-feeding-arm case.
                            //
                            // Each channel's restriction is the *bare* element
                            // predicate `__elem ▷ source ▷ (λ p → predᵢ)`
                            // referencing the domain element `__elem` (the same
                            // form a filtered comprehension builds — see
                            // `crate::ccl::comprehension`), then wraps the source's
                            // *domain* in `Refinement(_, pred)` so planning
                            // restricts the iteration to passing indices. The
                            // predicate MUST reference `__elem` in this element
                            // form: planning's `compile_refinement_predicates`
                            // η-expands `λ __elem → pred` and lambda-eliminates
                            // it, so a predicate constant in `__elem` (e.g. a
                            // point-free `source ≫ guard`) collapses to
                            // `const(_)` and drops the per-element test. It is
                            // also fully typed here — a `Refinement` predicate is
                            // immutable, so no later pass re-derives it (channel
                            // reads type concretely at inference against their
                            // rigid `ChanDom`; there is no re-typing pass).
                            // Two traversals decide which arms are this defer's. The
                            // fan-out decided on the guard form
                            // `tag_case_to_guard_case` produces, where a pattern
                            // payload is already substituted; the residual decides on
                            // the original, by matching a `Feed`'s name. An arm counted
                            // by one and not the other is either left standing with its
                            // value already taken into the channel, or erased with its
                            // value lost, and nothing downstream reports either.
                            let TypedExprNode::Case {
                                branches: original_branches,
                                ..
                            } = &body.node
                            else {
                                unreachable!(
                                    "`try_extract_fanout_feed` returned `Some`, which \
                                     destructures a `Case`"
                                )
                            };
                            assert_eq!(
                                fanout_arms
                                    .iter()
                                    .filter(|(_, value)| value.is_some())
                                    .count(),
                                original_branches
                                    .iter()
                                    .filter(|b| matches!(
                                        &b.body.node,
                                        TypedExprNode::Feed { name, .. } if name == defer_name
                                    ))
                                    .count(),
                                "the fan-out extracts and the residual erases the same arms"
                            );
                            // Every feeding arm composes its own restriction onto a
                            // clone of this prefix, so N defers off one conditional
                            // compile to N restricted scans of the same source and N
                            // evaluations of the guard — with a data source and a UDF
                            // condition, one UDF call per defer per element. No
                            // downstream pass collapses the shared prefix. That is the
                            // accepted cost of giving each defer a channel whose domain
                            // is its own arms' restriction: the restrictions are
                            // disjoint by first-match, so there is no one domain the
                            // arms could share a scan over.
                            let source_prefix = if new_elts.len() == 1 {
                                new_elts[0].clone()
                            } else {
                                typed_compose(new_elts.clone())
                            };
                            let src_domain = source_prefix.ty.domain().unwrap_or(Type::Hole);
                            let src_item = source_prefix.ty.codomain().unwrap_or(Type::Hole);
                            // The `Feed` each feeding arm is, in arm order: the guard form a
                            // `match` converts to is a copy, so the originals name them.
                            let mut arm_feeds = original_branches
                                .iter()
                                .filter(|b| {
                                    matches!(
                                        &b.body.node,
                                        TypedExprNode::Feed { name, .. } if name == defer_name
                                    )
                                })
                                .map(|b| b.body.node_id())
                                .collect::<Vec<_>>()
                                .into_iter();
                            let mut prior: Vec<Expr> = Vec::new();
                            for (guard, feed_value) in fanout_arms {
                                if let Some(value) = feed_value {
                                    let feed = arm_feeds.next().expect(
                                        "one original `Feed` per feeding arm, asserted above",
                                    );
                                    let _g = provenance::enter(
                                        feed,
                                        "channelize.feed",
                                        provenance::Nature::Expansion,
                                    );
                                    let pred = synthesize_arm_predicate(&guard, &prior);
                                    let elem = Expr::var(Name::elem()).with_ty(src_domain.clone());
                                    let source_at_elem = Expr::apply(elem, source_prefix.clone())
                                        .with_ty(src_item.clone());
                                    let pred_lambda =
                                        Expr::lambda(&param.name, param.ty.clone(), pred);
                                    let pred_on_source = Expr::apply(source_at_elem, pred_lambda)
                                        .with_ty(Type::Base(BaseType::Bool));
                                    let refinement_struct =
                                        Refinement::born(Rc::new(pred_on_source));
                                    let mut refined_prefix = source_prefix.clone();
                                    refine_source_domain(&mut refined_prefix, refinement_struct);
                                    let channel_lambda = contribution_lambda(&param, value, None);
                                    // stamp the channel at
                                    // construction — `Fun(refined-domain,
                                    // value)` off the two elements' concrete
                                    // types; there is no re-derivation pass
                                    // to fill a `Hole` in.
                                    let channel_expr =
                                        compose_typed_or_hole(vec![refined_prefix, channel_lambda]);
                                    feeds.push(Contribution {
                                        value: channel_expr,
                                        levels: 1,
                                        feed,
                                    });
                                }
                                prior.push(guard);
                            }
                            // Every feed for this defer is extracted, so its arms
                            // are what the residual drops. A `Case` feeding another
                            // defer keeps that arm for the pass that extracts it;
                            // one feeding only this defer residues to arms that are
                            // all `Unit`, which after lambda elim composes with the
                            // unrefined source to a no-op iteration.
                            let new_lambda = TypedExpr {
                                node: TypedExprNode::Lambda {
                                    param,
                                    body: Box::new(residual_after_fanout(*body, defer_name)),
                                },
                                ty: elt_ty,
                                user_annotation: elt_user_ann,
                                // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                                node_id: elt_node_id,
                            };
                            new_elts.push(new_lambda);
                            continue;
                        }
                        let mut lambda_feeds: Vec<Contribution> = Vec::new();
                        let mut lambda_define: Option<(NodeId, Expr)> = None;
                        let new_body = extract_for_defer(
                            *body,
                            defer_name,
                            &mut lambda_feeds,
                            &mut lambda_define,
                            true,
                        )?;
                        no_inner_define(lambda_define);
                        // Emit per-feed companion composes BEFORE pushing
                        // the rewritten lambda — `new_elts` is the prefix
                        // up to (but not including) this element, which is
                        // exactly the surrounding context the feed value
                        // needs.
                        for Contribution {
                            value: v,
                            levels,
                            feed,
                        } in lambda_feeds
                        {
                            let _g = provenance::enter(
                                feed,
                                "channelize.feed",
                                provenance::Nature::Expansion,
                            );
                            // `Expr::lambda` stamps `Fun(param.ty, v.ty)`; the
                            // param carries the matched lambda's own (concrete)
                            // type, so the companion value lambda is fully typed.
                            // The compose type is `Fun(prefix-domain, v.ty)`;
                            // a prefix that is itself a defer read carries its
                            // handle's rigid `ChanDom` domain, closed by the
                            // final `erase_chan_domains` substitution.
                            let channel_lambda = contribution_lambda(&param, v, None);
                            let mut channel_elts = new_elts.clone();
                            channel_elts.push(channel_lambda);
                            // A single-element "compose" is just that
                            // element; otherwise build a Compose.
                            let channel_expr = if channel_elts.len() == 1 {
                                channel_elts.into_iter().next().unwrap()
                            } else {
                                compose_typed_or_hole(channel_elts)
                            };
                            // The loop keys the feed by its positions: one more level.
                            feeds.push(Contribution {
                                value: channel_expr,
                                levels: levels + 1,
                                feed,
                            });
                        }
                        new_elts.push(TypedExpr {
                            node: TypedExprNode::Lambda {
                                param,
                                body: Box::new(new_body),
                            },
                            ty: elt_ty,
                            user_annotation: elt_user_ann,
                            // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                            node_id: elt_node_id,
                        });
                    }
                    other => {
                        let elt = TypedExpr {
                            node: other,
                            ty: elt_ty,
                            user_annotation: elt_user_ann,
                            // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                            node_id: elt_node_id,
                        };
                        new_elts.push(extract_for_defer(
                            elt,
                            defer_name,
                            feeds,
                            define,
                            in_inner_scope,
                        )?);
                    }
                }
            }
            TypedExprNode::Compose(new_elts)
        }
        TypedExprNode::Copair(elts) => TypedExprNode::Copair(
            elts.into_iter()
                .map(|e| extract_for_defer(e, defer_name, feeds, define, in_inner_scope))
                .collect::<Result<_, _>>()?,
        ),
        TypedExprNode::Record(fields) => {
            let mut new_fields = Vec::with_capacity(fields.len());
            for (n, e) in fields {
                new_fields.push((
                    n,
                    extract_for_defer(e, defer_name, feeds, define, in_inner_scope)?,
                ));
            }
            TypedExprNode::Record(new_fields)
        }
        TypedExprNode::Lambda { param, body } => {
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
            let mut local_feeds: Vec<Contribution> = Vec::new();
            let mut local_define: Option<(NodeId, Expr)> = None;
            let body = if &param.name == defer_name {
                *body
            } else {
                extract_for_defer(*body, defer_name, &mut local_feeds, &mut local_define, true)?
            };
            no_inner_define(local_define);
            for Contribution {
                value: v,
                levels,
                feed,
            } in local_feeds
            {
                let _g = provenance::enter(feed, "channelize.feed", provenance::Nature::Expansion);
                // The channel contribution is this lambda with the fed value for its body, so
                // it is the same collection-or-capability the lambda was — `Expr::lambda`
                // stamps `Compute`, so the incoming kind is carried back on. Its binder is
                // one more position the contribution is keyed by.
                let wrapped = contribution_lambda(&param, v, Some(&ty));
                feeds.push(Contribution {
                    value: wrapped,
                    levels: levels + 1,
                    feed,
                });
            }
            TypedExprNode::Lambda {
                param,
                body: Box::new(body),
            }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            // Case branches: each branch is an inner scope.  When *some*
            // arm contains a feed for `defer_name`, we wrap each arm's
            // terminal in `Record({result, __to_<d>})` with an Empty channel
            // for arms that don't feed (so all arms share the same Record
            // shape), and the Case's outer value becomes that Record.  The
            // surrounding scope's channel contribution is `case ▷
            // Proj("__to_<d>")` and the surrounding `result` is `case ▷
            // Proj("result")`.
            //
            // For arms with feeds where the feed value references arm-local
            // bindings, the Record wrap inside the arm keeps those bindings
            // in scope at the publication site.
            let mut per_branch: Vec<(Option<Pattern>, Expr, Vec<Contribution>, Expr)> =
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
                )?;
                no_inner_define(branch_define);
                if !branch_feeds.is_empty() {
                    any_feed = true;
                }
                per_branch.push((pattern, guard, branch_feeds, body));
            }
            if any_feed {
                // A feeding `Case` that reached the generic structural recursion
                // — i.e. one *not* wrapped in the iteration `Compose`/`Apply`
                // that the fan-out sites above intercept, so there is no
                // iteration source to restrict per arm. The loop-sourced
                // multi-arm fan-out (`if g: d << v` and `if/elif` in a for-loop
                // body) is handled at those sites via `try_extract_fanout_feed`.
                //
                // A *source-less* conditional feed (`if c: d << 1 else: d << 2`,
                // outside any loop) has no iteration source, so each feeding arm
                // becomes a **gated one-shot lift** over the `Unit` driver:
                // `λ __unused : {Unit | π̂ᵢ} → vᵢ`, first-match `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`
                // (a source-less feed; see `design/mutability.md`). Lambda elimination const-lifts
                // each to the value-`Case` C-form arm, planning materializes the
                // gate, and the channel union publishes exactly the selected arm's
                // value — empty (a naturally-partial feed) when no arm fires. A
                // *scrutinee / pattern* feed cannot be gated by a boolean
                // predicate, so it stays rejected.
                let guard_only =
                    scrutinee.is_none() && per_branch.iter().all(|(p, ..)| p.is_none());
                if !guard_only {
                    return Err(Located::new(
                        DeferError::PartialFeedCaseUnsupported(defer_name.clone()),
                        node_id,
                    ));
                }
                let unit_ty = Type::Base(BaseType::Unit);
                let mut prior_guards: Vec<Expr> = Vec::new();
                for (_, guard, branch_feeds, _) in &per_branch {
                    let pred = synthesize_arm_predicate(guard, &prior_guards);
                    prior_guards.push(guard.clone());
                    // `{Unit | π̂ᵢ}` — the gate is constant in the driver element.
                    // Store `π̂ᵢ` *directly* as the refinement's bare predicate (it
                    // does not mention `__elem`): planning's `fn_of_bare_predicate`
                    // slow-paths that through lambda elimination, desugaring the
                    // `and`/`not` into point-free form — the same path the
                    // loop-sourced fan-out relies on. A degenerate literal-`true`
                    // gate leaves the driver unrefined (an unconditional feed).
                    let refined = if matches!(&pred.node, TypedExprNode::Lit(Lit::Bool(true))) {
                        unit_ty.clone()
                    } else {
                        Type::refined_one(unit_ty.clone(), Refinement::born(Rc::new(pred)))
                    };
                    for Contribution {
                        value: v,
                        levels,
                        feed,
                    } in branch_feeds
                    {
                        let _g = provenance::enter(
                            *feed,
                            "channelize.feed",
                            provenance::Nature::Expansion,
                        );
                        // The channel is a collection, exactly as at the unconditional
                        // const-wrap above; `Expr::lambda` stamps `Compute`, so restate it.
                        // The gated unit is one more level, as the unconditional lift's is.
                        let vty = v.ty.clone();
                        feeds.push(Contribution {
                            value: Expr::lambda("__unused", refined.clone(), v.clone())
                                .with_ty(Type::data_fun(refined.clone(), vty)),
                            levels: levels + 1,
                            feed: *feed,
                        });
                    }
                }
                // Fall through: the residual value in every arm is now feed-free
                // (`Unit` for a bare `d << v` arm), so the `Case` below denotes the
                // statement's (discarded) value.
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
        // `Transact` is born by recognition, which runs *after* channelize
        // (post-`lambda_elim`) — none can reach feed extraction.
        TypedExprNode::Transact { .. } => {
            unreachable!("channelize: Transact is born by recognition, after this pass")
        }
        // Leaf nodes — no feeds possible.
        node @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::LoadFrom(_)
        | TypedExprNode::Defer) => node,
        TypedExprNode::Error => crate::unexpected_error_node!(),
        TypedExprNode::VariantCtor { tag, payload } => TypedExprNode::VariantCtor {
            tag,
            payload: Box::new(extract_for_defer(
                *payload,
                defer_name,
                feeds,
                define,
                in_inner_scope,
            )?),
        },
        // Recognition runs after lambda_elim, so a
        // causal `LetRec` reaches feed extraction. Walk its binding bodies
        // and continuation generically — the phase hoists every in-loop /
        // in-block feed to the letrec *body* (`for x in tap: defer << x` ExprStmts),
        // so extraction finds them there; binding bodies carry no feeds but
        // are walked for totality. Binder shadowing of `defer_name` is
        // impossible post-uniquify.
        TypedExprNode::LetRec { mut bindings, body } => {
            for (_, def) in bindings.iter_mut() {
                let taken = std::mem::take(def);
                *def = extract_for_defer(taken, defer_name, feeds, define, in_inner_scope)?;
            }
            let body = extract_for_defer(*body, defer_name, feeds, define, in_inner_scope)?;
            TypedExprNode::LetRec {
                bindings,
                body: Box::new(body),
            }
        }
        // Pre-phase markers: v1 lowering guarantees no feeds inside a
        // `For` body or `MutWrite` value, so there is nothing to extract —
        // pass them through untouched (debug-checked).
        node @ (TypedExprNode::For { .. } | TypedExprNode::MutWrite { .. }) => {
            debug_assert!(
                {
                    // `collect_feed_target_names` walks node structure only, so the
                    // probe needs no type or annotation slots.
                    let probe = Expr::throwaway(node.clone());
                    collect_feed_target_names(&probe).is_empty()
                },
                "feed inside a For/MutWrite marker — v1 lowering must route \
                 feed-bearing loops through the Loop path"
            );
            node
        }
    };
    Ok(TypedExpr {
        node,
        ty,
        user_annotation,
        node_id,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{Lit, symbolic::symbolic};

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }
    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    /// Type a hand-built fixture, so the test drives this pass at the position
    /// the pipeline runs it: after inference.
    ///
    /// The pass reads types it cannot re-derive — a feed handle's rigid
    /// `ChanDom`, a channel's concrete domain — so an untyped fixture would
    /// exercise fallback paths that no real program reaches.
    fn typed(expr: Expr) -> Expr {
        let mut expr = crate::ccl::uniquify::run(expr);
        crate::ccl::infer::infer(
            &mut expr,
            &mut crate::ccl::infer::TypeInferenceContext::new(),
        )
        .expect("fixture should type-check");
        expr
    }

    /// The lifted-prefix spine is typed, not `Hole`.
    ///
    /// [`lift_defer`] rebuilds the prefix onto the lifted body with
    /// `Expr::expr_stmt`, which carries the body's type — an `ExprStmt`'s type
    /// *is* its body's. That constructor used to leave `Type::Hole` here, and
    /// `Hole` is [`has_type_residue`], so an escaping one is exactly what
    /// [`assert_no_type_residue`] exists to catch. Pinned because the spine is
    /// built by a shared constructor: a future change there would otherwise
    /// reintroduce the residue silently on a path no other test types.
    ///
    /// Asserts on `Type::Hole` directly rather than calling `has_type_residue`,
    /// which is `#[cfg(debug_assertions)]` — reaching for it here would make the
    /// test exist only in debug, and `Hole` is the residue this path can produce.
    #[test]
    fn lifted_prefix_spine_carries_the_body_type() {
        let int = Type::Base(BaseType::Int);
        // `bound_expr` = `feed(x, 1); let x = Defer in (feed(x, 2); x)`, i.e. a
        // one-statement prefix ahead of the inner defer. Typed throughout, as a
        // post-inference tree is — the retype only matters in typed mode, and an
        // under-typed fixture would report its own `Hole`s as the failure.
        let inner_body = Expr::expr_stmt(Expr::feed("x", lit(2)), var("x").with_ty(int.clone()));
        let inner =
            Expr::let_bind("x", Expr::new(TypedExprNode::Defer), inner_body).with_ty(int.clone());
        let bound_expr = Expr::expr_stmt(Expr::feed("x", lit(1)), inner);
        let body = var("y").with_ty(int.clone());

        assert!(is_lift_shape(&bound_expr), "the fixture has the lift shape");
        let lift = lift_defer(&Name::raw("y"), bound_expr, &body);
        assert_eq!(lift.inner_name, Name::raw("x"));

        // Every `ExprStmt` on the spine carries a type. Checking for the absence
        // of `Hole` rather than for equality with `int` keeps this honest if the
        // lift ever wraps the body in something typed differently.
        fn assert_spine_typed(e: &Expr) {
            if matches!(e.node, TypedExprNode::ExprStmt { .. }) {
                assert!(
                    !matches!(e.ty, Type::Hole),
                    "lifted spine ExprStmt left a `Hole`: {}",
                    symbolic(e)
                );
            }
            e.walk_children(assert_spine_typed);
        }
        assert_spine_typed(&lift.expr);
    }

    #[test]
    fn run_single_feed() {
        let body = Expr::expr_stmt(Expr::feed("d", lit(1)), var("d"));
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(typed(expr)).unwrap();
        // After channelize: let __scope_out_d_0 = (Unit; Record({result: d, to_d: 1})) in
        //                let d = __scope_out_d_0.to_d in
        //                __scope_out_d_0.result
        let s = symbolic(&result);
        // After channelize: `unit; let d = (λ __unused → 1) in d` — the
        // scalar feed value is lifted to `Fun(Unit, T)` via the
        // `λ __unused → V` wrap, then bound to the defer name.
        assert!(s.contains("__unused"), "expected const-wrap in output: {s}");
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
        assert!(!s.contains("feed"), "no Feed should remain: {s}");
    }

    /// `let d = Defer in define(d, 42); d` — Define path: bind d to V directly.
    #[test]
    fn run_define_replaces_directly() {
        let body = Expr::expr_stmt(Expr::define("d", Expr::list(vec![lit(42)])), var("d"));
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(typed(expr)).unwrap();
        let s = symbolic(&result);
        assert!(
            s.contains("42"),
            "expected 42 to appear in result, got: {s}"
        );
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
        assert!(!s.contains("define"), "no Define should remain: {s}");
    }

    /// `let d = Defer in <body without feeds>` — error, raised at the `let`.
    #[test]
    fn run_no_feed_is_error() {
        let body = var("d");
        let expr = typed(Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body));
        let decl = expr.node_id();
        let err = run(expr).unwrap_err();
        assert!(
            matches!(&err.error, DeferError::NoFeedOrDefine(d) if d.base() == "d"),
            "expected NoFeedOrDefine(d), got {err:?}"
        );
        assert_eq!(err.node_id, decl);
    }

    /// Multiple feeds: copaired (distinct index sets, tagged apart).
    #[test]
    fn run_multiple_feeds_use_copair() {
        let body = Expr::expr_stmt(
            Expr::feed("d", lit(1)),
            Expr::expr_stmt(Expr::feed("d", lit(2)), var("d")),
        );
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(typed(expr)).unwrap();
        let s = symbolic(&result);
        assert!(
            s.contains("⊎") || s.contains("Union"),
            "should use union: {s}"
        );
    }

    // -----------------------------------------------------------------
    // `run`-boundary tests for the cluster algorithm and filter-feed Case
    // shapes.  These exercise the bulk of `extract_for_defer` /
    // `channelize_cluster` / `bind_cluster_at_scope` without going
    // through the full pipeline.
    // -----------------------------------------------------------------

    /// Cluster of three defers where channels reference each other in a
    /// chain (`a` depends on `b` depends on `c`). The cluster is emitted as
    /// one mutually-scoped `Feed`-kind letrec group — all three channels
    /// bound together, order immaterial (recognition later flattens the
    /// acyclic group to dependency-ordered lets).
    #[test]
    fn run_three_defer_cluster_becomes_letrec_group() {
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
            Expr::define("a", var("b")),
            Expr::expr_stmt(
                Expr::define("b", var("c")),
                Expr::expr_stmt(
                    Expr::define("c", Expr::list(vec![lit(0), lit(1)])),
                    var("a"),
                ),
            ),
        );
        let with_c = Expr::let_bind("c", Expr::new(TypedExprNode::Defer), inner);
        let with_b = Expr::let_bind("b", Expr::new(TypedExprNode::Defer), with_c);
        let with_a = Expr::let_bind("a", Expr::new(TypedExprNode::Defer), with_b);
        let result = run(typed(with_a)).expect("cluster resolution should succeed");
        let s = symbolic(&result);
        assert!(
            s.contains("letrec"),
            "cluster should be a letrec group: {s}"
        );
        let TypedExprNode::LetRec { bindings, .. } = &result.node else {
            panic!("cluster should be emitted as a letrec group: {s}");
        };
        let names: Vec<&str> = bindings.iter().map(|(b, _)| b.name.base()).collect();
        assert_eq!(
            names,
            ["a", "b", "c"],
            "all three channels bound in one group: {s}"
        );
        assert!(!s.contains("defer"), "no Defer should remain: {s}");
    }

    /// Mutually recursive defer cluster: `a <<= b; b <<= a` — an
    /// unsupported letrec.  Surfaces as `MutuallyRecursiveCycle`.
    #[test]
    fn run_mutual_cycle_is_error() {
        let inner = Expr::expr_stmt(
            Expr::define("a", var("b")),
            Expr::expr_stmt(Expr::define("b", var("a")), var("a")),
        );
        let with_b = Expr::let_bind("b", Expr::new(TypedExprNode::Defer), inner);
        let with_a = Expr::let_bind("a", Expr::new(TypedExprNode::Defer), with_b);
        let err = run(typed(with_a)).unwrap_err();
        assert!(
            matches!(err.error, DeferError::MutuallyRecursiveCycle(_)),
            "expected MutuallyRecursiveCycle, got {err:?}"
        );
    }

    // -----------------------------------------------------------------
    // `collect_free_vars` — type-position refinement traversal
    // -----------------------------------------------------------------

    /// `collect_free_vars` must descend into `user_annotation`
    /// refinement predicates.  Otherwise filter-feed channels (which
    /// stash a `Refinement(_, pred)` in `user_annotation`) hide their
    /// outer-let references from [`assert_no_shadowed_captures`], and a
    /// downstream shadow goes undetected.
    #[test]
    fn collect_free_vars_descends_into_user_annotation_predicates() {
        // Build a trivial channel whose `user_annotation` carries a
        // predicate referencing `outer_n`:
        //   `Var("__chan")` with user_annotation = Fun(Refinement(Hole, pred(outer_n)), Hole)
        let pred = var("outer_n");
        let refinement = Refinement::born(Rc::new(pred));
        let annotated = Expr::var(Name::raw("__chan")).with_user_annotation(Type::fun(
            Type::refined_one(Type::Hole, refinement),
            Type::Hole,
        ));

        let mut free: HashSet<Name> = HashSet::new();
        collect_free_vars(&annotated, &mut free);
        assert!(
            free.contains(&Name::raw("outer_n")),
            "user_annotation predicate reference should be collected: got {free:?}"
        );
        // The expression node itself names `__chan` — also collected.
        assert!(
            free.contains(&Name::raw("__chan")),
            "expr node Var was missed: {free:?}"
        );
    }

    /// `collect_free_vars` must descend into `expr.ty` refinement
    /// predicates (the type slot, not just `user_annotation`).
    #[test]
    fn collect_free_vars_descends_into_ty_refinement_predicates() {
        let pred = var("inner_k");
        let refinement = Refinement::born(Rc::new(pred));
        let typed = Expr::lit(Lit::Unit).with_ty(Type::Fun {
            name: None,
            fun_kind: FunKind::Compute,
            domain: Box::new(Type::refined_one(Type::Hole, refinement)),
            codomain: Box::new(Type::Hole),
        });
        let mut free: HashSet<Name> = HashSet::new();
        collect_free_vars(&typed, &mut free);
        assert!(
            free.contains(&Name::raw("inner_k")),
            "expr.ty predicate reference should be collected: got {free:?}"
        );
    }
}

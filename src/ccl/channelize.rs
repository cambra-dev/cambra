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
//! already hoisted every in-loop feed to an ordinary `Feed(defer, view)` of the
//! loop's history ([`crate::ccl::mut_elim::hoist_feeds`]), so channelization
//! is **origin-agnostic**: it never distinguishes an accumulator-loop feed from
//! a feed-only-loop or scalar feed.
//!
//! Type errors report against the user-shaped tree (inference types the defer
//! constructs directly: see `design/type-inference.md` §"Feed handles as an invariant `History` constructor (`Type::History { kind: Feed }`)"), so this
//! step never fails on a user error — it only rejects internally-inconsistent
//! shapes.
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
//! concrete domain and erase each `Feed`-kind history to its stream `Fun` — the
//! exact feed-side analog of `mut_elim::erase_mut`. There is no re-typing
//! pass; the strict post-channelization `typecheck` in `compile_program`
//! backstops the invariant.
//!
//! After this step, no [`TypedExprNode::Defer`], [`TypedExprNode::Feed`],
//! [`TypedExprNode::Define`], or [`TypedExprNode::ExprStmt`] nodes — and no
//! `Feed`/`Hole`/`Infer` types — remain in the tree; every downstream pass treats
//! those variants as `unreachable!`.
//!
//! A loop-sourced multi-arm (`if`/`elif`) feed `Case` fans out into one
//! refined-source channel per feeding arm ([`try_extract_fanout_feed`]); only a
//! *source-less* conditional feed (a feeding `Case` outside any iteration) is
//! rejected, with `DeferError::PartialFeedCaseUnsupported` (see the `Case` arm of
//! [`extract_for_defer`]).
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
//! `desugar` performs three steps:
//!
//! 1. **Feed extraction.**  Walk the cluster body and collect every
//!    `Feed(d_i, V)` / `Define(d_i, V)` plus the iteration context
//!    they sit in (Compose/Apply/Loop/Case), producing a channel
//!    expression for each `d_i`.
//! 2. **Channel assembly.**  Combine multiple feeds per defer via
//!    `++` ([`TypedExprNode::CollectionUnion`]); lift scalar feeds
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

use crate::ccl::{
    BaseType, BinOpKind, Branch, Expr, HistoryKind, Lit, LogicKind, Name, Pattern, Refinement,
    Type, TypedBinding, TypedExpr, TypedExprNode, UnaryOpKind,
    ccl_utils::{count_free, typed_compose},
    letrec::check_letrec_causal,
};

/// `true` when `ty` carries channelization-erasable residue — a `Hole` stamped
/// on a node this pass constructed or invalidated, an unresolved `Infer` channel
/// domain, or a `Feed` history the defer elimination dissolves. Walks type
/// structure only; refinement *predicates* carry no such residue (their terms are
/// immutable and kept type-consistent by the substitution engine), so they are
/// not inspected.
///
/// Debug-only: its sole consumer is the `assert_no_type_residue` invariant
/// walk (the strict `typecheck` wall is the release-visible enforcement).
#[cfg(debug_assertions)]
fn has_type_residue(ty: &Type) -> bool {
    match ty {
        Type::Hole
        | Type::Infer(_)
        | Type::ChanDom(..)
        | Type::History {
            kind: HistoryKind::Append,
            ..
        } => true,
        _ => {
            let mut found = false;
            ty.walk_children(|t| found = found || has_type_residue(t));
            found
        }
    }
}

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
    /// cyclically (e.g. `x ≪= y; y ≪= x`). Channels are `Feed`-kind letrec
    /// bindings and carry no `get_prev_*` guard, so a cycle has no
    /// well-founded solution — rejected by the letrec causality rule
    /// ([`crate::ccl::letrec::check_letrec_causal`]), the same law that
    /// governs overwrite recursion. The payload names one of the defers on the
    /// cycle.
    MutuallyRecursiveCycle(String),
    /// A feeding `Case` reached the generic structural recursion — a
    /// conditional feed with no enclosing iteration source to restrict per arm
    /// (the loop-sourced multi-arm case is fanned out at the `Compose`/`Apply`
    /// sites via [`try_extract_fanout_feed`]). A source-less conditional feed
    /// has no refinement to hang the guard on, so it is rejected rather than
    /// miscompiled. The payload names the defer.
    PartialFeedCaseUnsupported(String),
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
            DeferError::PartialFeedCaseUnsupported(name) => {
                write!(
                    f,
                    "deferred binding '{name}' is fed from some but not all branches of a \
                     multi-way conditional; this shape is not supported yet"
                )
            }
        }
    }
}

/// Recognize a guard-only `Case` that feeds `defer_name` in one or more arms —
/// the desugar-stage counterpart of `lambda_elim`'s `is_filter_case_body`.
///
/// Shape (as lowered from `if g₀: d << v₀ elif g₁: d << v₁ …` in a for-loop
/// body): `Case { None, [g₀ → body₀; …; gₙ₋₁ → bodyₙ₋₁; true → unit] }`, where
/// each non-trailing `bodyᵢ` is either `Feed(defer_name, vᵢ)` (a feeding arm)
/// or `Unit` (a non-feeding arm), and the trailing arm is the implicit
/// `true → unit` fallthrough.
///
/// Returns each non-trailing arm's `(guard, feed_value?)` in source order —
/// `feed_value` is `None` for a non-feeding arm, whose guard still participates
/// in later arms' predicate synthesis ([`synthesize_arm_predicate`]). Returns
/// `None` (not fannable) if there is a scrutinee, no `true → unit` fallthrough,
/// an arm binds a pattern, or an arm body is neither this defer's feed nor
/// `Unit` — so a `Case` mixing this defer's feeds with other effects falls
/// through to the generic handling rather than being silently collapsed.
fn try_extract_fanout_feed(body: &Expr, defer_name: &Name) -> Option<Vec<(Expr, Option<Expr>)>> {
    let TypedExprNode::Case {
        scrutinee: None,
        branches,
    } = &body.node
    else {
        return None;
    };
    if branches.len() < 2 {
        return None;
    }
    let (last, rest) = branches.split_last().expect("len >= 2");
    // The trailing arm must be the implicit `true → unit` fallthrough.
    if !matches!(&last.guard.node, TypedExprNode::Lit(Lit::Bool(true)))
        || !matches!(&last.body.node, TypedExprNode::Lit(Lit::Unit))
    {
        return None;
    }
    let mut arms = Vec::with_capacity(rest.len());
    let mut any_feed = false;
    for b in rest {
        // A guard-only arm never binds a pattern.
        if b.pattern.is_some() {
            return None;
        }
        match &b.body.node {
            TypedExprNode::Feed { name, value } if name == defer_name => {
                any_feed = true;
                arms.push((b.guard.clone(), Some((**value).clone())));
            }
            TypedExprNode::Lit(Lit::Unit) => arms.push((b.guard.clone(), None)),
            _ => return None,
        }
    }
    any_feed.then_some(arms)
}

/// Build arm `i`'s effective predicate `gᵢ ∧ ¬g₀ ∧ … ∧ ¬gᵢ₋₁`, encoding a
/// `Case`'s "first matching guard wins" semantics: arm `i` fires only where its
/// own guard holds and no earlier arm's did. `prior` holds `g₀ … gᵢ₋₁` in
/// order; `guard` is `gᵢ`. Every guard is a `Bool`-typed expression over the
/// same loop element, so the synthesized conjunction is `Bool` too — typed here
/// (desugar runs post-inference and must be type-preserving).
fn synthesize_arm_predicate(guard: &Expr, prior: &[Expr]) -> Expr {
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

/// Attempt to apply the defer-returning lift to a `Let` binding.
///
/// Pattern: `let y = (let x = Defer in body_x) in body_y` where
/// `body_x` is *defer-returning* (ends in `Var(x)` after walking
/// through any `ExprStmt`/`Let` chains).
///
/// Rewrites to: `let y = Defer in body_x[x → y] with Var(y) replaced
/// by body_y`.  The substitution `x → Var(y)` is done via
/// [`desugar_substitute`], which also renames the *target* name of
/// `Feed`/`Define` nodes when the replacement is a `Var` — so
/// `Feed("x", …)` becomes `Feed("y", …)` automatically.
///
/// Also handles an optional `ExprStmt` prefix on `bound_expr`: the
/// heads of any leading ExprStmts become a prefix that's prepended to
/// the lifted body, with stale Feed/Define target names renamed to `y`.
fn try_lift_defer(binding_name: &Name, bound_expr: &Expr, body: &Expr) -> Option<(Expr, Name)> {
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
    let (inner_name, inner_handle_ty, inner_body_x) = match current.node {
        TypedExprNode::Let {
            binding: inner_binding,
            bound_expr: inner_be,
            body: inner_body,
        } if matches!(inner_be.node, TypedExprNode::Defer)
            && is_defer_returning(&inner_body, &inner_binding.name) =>
        {
            // Keep the inner defer's recorded handle type (`feed(ChanDom(F) ⇒
            // V)`) — the lifted binding must carry it so cluster discovery
            // keys the channel by the domain name consumer types reference,
            // not by the term name. (`Hole` on an untyped tree, harmlessly.)
            (inner_binding.name, inner_be.ty, *inner_body)
        }
        _ => return None,
    };

    // `body_x[x → y]` — also renames Feed/Define targets named `x` to `y`.
    let y_var = Expr::var(binding_name);
    let inner_subst = desugar_substitute(inner_body_x, &inner_name, &y_var);

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
            },
            TypedExprNode::Define { name: _, value } => TypedExpr {
                ty: head.ty,
                node: TypedExprNode::Define {
                    name: binding_name.clone(),
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

    // Rebuild the lifted let type-preservingly: the `Defer` node (and, via
    // `let_bind`, the binding slot) carries the inner handle type, and the
    // `Let` node itself the body's type.
    let out_ty = spliced.ty.clone();
    let mut defer_node = Expr::new(TypedExprNode::Defer);
    defer_node.ty = inner_handle_ty;
    let mut lifted = Expr::let_bind(binding_name, defer_node, spliced);
    lifted.ty = out_ty;
    Some((lifted, inner_name))
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

/// Return `true` if `expr` contains a `Defer` node anywhere
/// (transitively).
fn contains_defer(expr: &Expr) -> bool {
    matches!(expr.node, TypedExprNode::Defer) || expr.any_child(contains_defer)
}

/// Return `true` if `expr` contains any `Feed(target, …)` or
/// `Define(target, …)` node where `target == name`, respecting shadowing
/// by `Let`/`Lambda` bindings that rebind `name`.
///
/// Debug-only: the sole caller is the `desugar` invariant assert that a
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
/// desugaring, renaming `Feed`/`Define` targets along the way: when
/// `replacement` is a `Var(new_name)`, handle uses of `name` become
/// `new_name` — the α-renaming that makes alias-inlining for defer handles
/// correct.
///
/// A thin wrapper over the uniform engine's in-place mode
/// ([`crate::ccl::subst::Subst::rewrite_expr`]). Unlike the pre-port
/// version, the engine also rewrites type-carried refinement predicates
/// (`Cast` targets, annotations), so a desugar rename now reaches a
/// predicate that closes over the renamed binder instead of leaving a stale
/// reference; and a `Case` pattern binding correctly shadows `name` in its
/// branch.
fn desugar_substitute(expr: Expr, name: &Name, replacement: &Expr) -> Expr {
    let mut expr = expr;
    crate::ccl::subst::Subst::discharge_in_place(&mut expr, name, replacement);
    expr
}

/// State threaded through the desugar walk.
///
/// Carries whether the input tree was type-inferred before this pass
/// (the desugar-after-inference order — see [`run`]), which gates the
/// type-stamp steps.
struct DesugarCtx {
    /// Whether the input tree was type-inferred before this pass (the
    /// desugar-after-inference order — see [`run`]). Gates the type
    /// stamps: under the legacy untyped order they would change what
    /// inference later sees.
    input_typed: bool,
    /// each channelized defer's concrete channel domain,
    /// keyed by its (nominal) `ChanDom` name — recorded as clusters are
    /// assembled, then closed and substituted over the whole tree by [`run`].
    /// A recorded domain may itself reference another cluster name (an alias
    /// `x <<= y` records `x ↦ ChanDom(y)`); [`close_chan_domains`] resolves
    /// those before the substitution.
    resolved_domains: Vec<(Name, Type)>,
}

impl DesugarCtx {
    fn new() -> Self {
        Self {
            input_typed: false,
            resolved_domains: Vec::new(),
        }
    }
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
/// `Unit`-typed value that can be dropped.  Doing this in `channelize`
/// (rather than leaving it for `simplify`) means no later pass needs to
/// pattern-match `ExprStmt`.
pub fn run(expr: Expr, input_typed: bool) -> Result<Expr, DeferError> {
    // `input_typed` says whether the tree was already type-inferred (the
    // desugar-after-inference pipeline order). It cannot be sniffed from the
    // tree — lowering stamps concrete types on some nodes (lambdas,
    // comprehension domains) — so the caller states it. In the legacy
    // pre-inference order the pass is purely structural and the
    // type-synthesis step below is skipped.
    let mut ctx = DesugarCtx::new();
    ctx.input_typed = input_typed;
    // Cluster channelization.  Walks the tree, processes `let d = Defer in …`
    // clusters, extracting feeds and building each defer's channel.
    //
    // Defer-mediating UDFs (`def g(out): out << e`, `def f(n): x = defer();
    // …; x`) never reach here: `inline` beta-reduces every such function at its
    // call site *before* this pass (it runs pre-desugar — see the `inline`
    // module docs), leaving only the flattened `let d = Defer in …` chains this
    // walk handles. The former Phase-1 chain rewriter and the call-site smart
    // walker that existed for the un-inlined higher-order case are retired.
    let rewritten = desugar(expr, &mut ctx)?;
    let mut rewritten = drop_expr_stmts(rewritten);
    assert_no_defer_residue(&rewritten)?;
    if input_typed {
        // with nominal channel domains, every consumer of a
        // defer read typed *concretely* against `ChanDom(d)` at inference —
        // there is no `Infer` channel-domain residue to re-derive. Closing the
        // tree is therefore a pure whole-tree type substitution: map each
        // `ChanDom(d)` to its assembled channel's concrete domain, and erase
        // each `Feed`-kind history to its bare stream `Fun` — the exact
        // feed-side analog of `mut_elim::erase_mut`. The strict
        // post-desugar `typecheck` in `compile_program` backstops the invariant.
        let mut map = close_chan_domains(std::mem::take(&mut ctx.resolved_domains));
        erase_chan_domains(&mut rewritten, &mut map);
        #[cfg(debug_assertions)]
        assert_no_type_residue(&rewritten);
    }
    Ok(rewritten)
}

/// The channel-domain name (and its inference level) carried by a feed
/// handle's recorded type — `feed(ChanDom(n) ⇒ V)`, through refinements.
/// This is the name consumer types actually reference. For a specialization
/// clone it differs from the term binder name (channel identity is
/// per-instantiation, freshened at `specialize_use`), so channel recording
/// and lift-alias entries key on it, never on the term name.
fn handle_chan_dom(ty: &Type) -> Option<(Name, crate::ccl::ChanLevel)> {
    match peel_refinements(ty) {
        Type::History {
            domain,
            kind: HistoryKind::Append,
            ..
        } => match peel_refinements(domain) {
            Type::ChanDom(n, l) => Some((n.clone(), *l)),
            _ => None,
        },
        _ => None,
    }
}

/// Locate the `let <term> = Defer` binding inside `expr` and read its handle's
/// channel-domain name ([`handle_chan_dom`], off the binding slot or the
/// `Defer` node itself). Used by the defer-returning lift to key its alias
/// entry by the name consumer types carry.
fn find_defer_chan_dom(expr: &Expr, term: &Name) -> Option<(Name, crate::ccl::ChanLevel)> {
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        ..
    } = &expr.node
        && binding.name == *term
        && matches!(bound_expr.node, TypedExprNode::Defer)
    {
        return handle_chan_dom(&binding.ty).or_else(|| handle_chan_dom(&bound_expr.ty));
    }
    let mut found = None;
    expr.walk_children(|c| {
        if found.is_none() {
            found = find_defer_chan_dom(c, term);
        }
    });
    found
}

/// the channel domain carried by an assembled channel's
/// type — the domain of its constructed `Fun`, or, for an alias channel that
/// is itself a defer read (`x <<= y` leaves `Var(y) : feed(…)`), the read's
/// handle domain (a `ChanDom` closed later by [`close_chan_domains`]).
fn channel_domain_of(ty: &Type) -> Option<Type> {
    match peel_refinements(ty) {
        Type::Fun { domain, .. } => Some((**domain).clone()),
        Type::History {
            domain,
            kind: HistoryKind::Append,
            ..
        } => Some((**domain).clone()),
        _ => None,
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
/// bare stream `Fun(domain, value)` and substitute every `ChanDom` via
/// [`subst_chan_domains_in_type`] — the feed-side analog of
/// `mut_elim::erase_mut_in_type`.
fn erase_chan_domains_in_type(ty: &mut Type, map: &HashMap<Name, Type>) {
    if let Type::History {
        value,
        domain,
        kind: HistoryKind::Append,
    } = ty
    {
        let domain = std::mem::replace(domain.as_mut(), Type::Hole);
        let value = std::mem::replace(value.as_mut(), Type::Hole);
        *ty = Type::Fun {
            name: None,
            domain: Box::new(domain),
            codomain: Box::new(value),
        };
        return erase_chan_domains_in_type(ty, map);
    }
    if let Type::ChanDom(name, _) = ty {
        if let Some(dom) = map.get(name) {
            *ty = dom.clone();
            erase_chan_domains_in_type(ty, map);
        }
        return;
    }
    ty.walk_children_mut(|t| erase_chan_domains_in_type(t, map));
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
fn erase_chan_domains(expr: &mut Expr, map: &mut HashMap<Name, Type>) {
    // Erase this node's binder-declared type slots (shared coverage with
    // `mut_elim::erase_mut` via `walk_binders_mut`). This is order-invariant
    // w.r.t. the `Let`-discharge below: a binder's type resolves against `map` as
    // it stands, and a child's discharge only closes variables bound *inside*
    // that child — never in scope at this binder — so erasing binders before the
    // child recursion sees the same substitutions the old inline order did.
    expr.walk_binders_mut(|b| {
        erase_chan_domains_in_type(&mut b.ty, map);
        if let Some(ann) = &mut b.user_annotation {
            erase_chan_domains_in_type(ann, map);
        }
    });
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut expr.node
    {
        erase_chan_domains(bound_expr, map);
        erase_chan_domains(body, map);
        // §6.2 Let-closing on the substitution content (see fn docs).
        let discharge = crate::ccl::subst::Subst::discharge(&binding.name, (**bound_expr).clone());
        for dom in map.values_mut() {
            *dom = discharge.apply_type(dom);
        }
    } else {
        expr.walk_children_mut(|c| erase_chan_domains(c, map));
    }
    erase_chan_domains_in_type(&mut expr.ty, map);
    if let Some(ann) = &mut expr.user_annotation {
        erase_chan_domains_in_type(ann, map);
    }
}

/// The codomain of `ty` viewed as a function, peeling outer refinements.
///
/// a `Feed`-kind history is viewed as its stream
/// `domain ⇒ value` — with rigid nominal domains an unresolved defer read has
/// a usable (concrete-modulo-`ChanDom`) function view, so a channel built on
/// a read prefix (a nested generator's inner channel block) types at
/// construction instead of leaving a `Hole` for a re-derivation pass.
fn fun_codomain(ty: &Type) -> Option<Type> {
    match peel_refinements(ty) {
        Type::Fun { codomain, .. } => Some((**codomain).clone()),
        Type::History {
            value,
            kind: HistoryKind::Append,
            ..
        } => Some((**value).clone()),
        _ => None,
    }
}

/// The domain of `ty` viewed as a function, peeling outer refinements.
/// See [`fun_codomain`] for the feed-history stream view.
fn fun_domain(ty: &Type) -> Option<Type> {
    match peel_refinements(ty) {
        Type::Fun { domain, .. } => Some((**domain).clone()),
        Type::History {
            domain,
            kind: HistoryKind::Append,
            ..
        } => Some((**domain).clone()),
        _ => None,
    }
}

/// Debug-only invariant: after [`run`] on a typed input, no expression or
/// binder slot may still carry a `Hole`, `Infer`, or `Feed` type — desugar
/// erased the defer constructs, so their transient types must be gone too.
/// (Refinement predicates are checked by the strict `typecheck` instead;
/// walking them here would need the cycle guards it already has.)
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

/// Attach the filter-feed guard refinement to a channel source's *domain*.
///
/// Under the typed order the refined function type is stamped directly on
/// `source.ty` — inference has already run, so nothing would consume an
/// annotation. Under the legacy order it rides `user_annotation` for the
/// upcoming inference pass to unify and carry.
fn refine_source_domain(source: &mut Expr, refinement: Refinement, ctx: &DesugarCtx) {
    if ctx.input_typed
        && let Type::Fun {
            name,
            domain,
            codomain,
        } = &source.ty
    {
        source.ty = Type::Fun {
            name: name.clone(),
            domain: Box::new(Type::Refinement(domain.clone(), refinement)),
            codomain: codomain.clone(),
        };
        return;
    }
    // A typed-order channel source is always a concrete function type, stamped
    // above. Reaching here under the typed order means a residue-typed source
    // whose filter would be *silently dropped*: planning reifies the refinement
    // off `expr.ty.domain()`, never `user_annotation`, and no inference runs
    // after channelize to consume one. Assert rather than drop it; the
    // `user_annotation` write below is the legacy (pre-inference) path only.
    debug_assert!(
        !ctx.input_typed,
        "refine_source_domain: typed-order channel source is not a function type \
         ({}); its filter refinement would be silently dropped",
        source.ty
    );
    source.user_annotation = Some(Type::fun(
        Type::Refinement(Box::new(Type::Hole), refinement),
        Type::Hole,
    ));
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
        TypedExprNode::MutWrite { name, value } => TypedExprNode::MutWrite {
            name,
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
        | TypedExprNode::Source(_)) => node,
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
    }
}

/// Whether the subtree contains a pre-phase marker node (`For`/`MutWrite`)
/// that the unified letrec phase consumes downstream of desugar. Used to
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

/// Confirm that no `Defer`/`Feed`/`Define` nodes remain after desugar.
fn assert_no_defer_residue(expr: &Expr) -> Result<(), DeferError> {
    match &expr.node {
        TypedExprNode::Defer => Err(DeferError::UnboundDeferHandle("<defer>".into())),
        TypedExprNode::Feed { name, .. } | TypedExprNode::Define { name, .. } => {
            Err(DeferError::UnboundDeferHandle(name.base().to_string()))
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
        TypedExprNode::Cast { value, .. } => assert_no_defer_residue(value),
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
        TypedExprNode::MutWrite { value, .. } => assert_no_defer_residue(value),
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_) => Ok(()),
        TypedExprNode::Error => crate::unexpected_error_node!(),
        TypedExprNode::VariantCtor { payload, .. } => assert_no_defer_residue(payload),
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
            let mut defer_names = vec![binding.name];
            let mut current_body = *body;
            loop {
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
            channelize_cluster(&defer_names, &chan_names, body_rewritten, ctx)
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
            if let Some((lifted, inner_name)) = try_lift_defer(&binding.name, &bound_expr, &body) {
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
                // fallback for handles the walk cannot locate.
                if ctx.input_typed {
                    let inner_key = find_defer_chan_dom(&bound_expr, &inner_name)
                        .map(|(n, _)| n)
                        .unwrap_or_else(|| inner_name.clone());
                    let (outer, lvl) = handle_chan_dom(&binding.ty)
                        .unwrap_or_else(|| (binding.name.clone(), crate::ccl::ChanLevel(0)));
                    if inner_key != outer {
                        ctx.resolved_domains
                            .push((inner_key, Type::ChanDom(outer, lvl)));
                    }
                }
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
                let renamed = desugar_substitute(spliced, &inner_name, &Expr::var(&binding.name));
                // Same alias recording as the lift above — types outside this
                // subtree may carry the inner handle's rigid name.
                if ctx.input_typed {
                    let inner_key = handle_chan_dom(&inner_binding.ty)
                        .map(|(n, _)| n)
                        .unwrap_or_else(|| inner_name.clone());
                    let (outer, lvl) = handle_chan_dom(&binding.ty)
                        .unwrap_or_else(|| (binding.name.clone(), crate::ccl::ChanLevel(0)));
                    if inner_key != outer {
                        ctx.resolved_domains
                            .push((inner_key, Type::ChanDom(outer, lvl)));
                    }
                }
                let collapsed = Expr::let_bind(binding.name.clone(), inner_be, renamed);
                return desugar(collapsed, ctx);
            }
            // Recurse first so any inner aliases / UDF-inlines get
            // resolved before we check this outer binding.
            let bound_expr = desugar(*bound_expr, ctx)?;
            let body = desugar(*body, ctx)?;
            // Alias inlining (`let y = Var(x) in body` → `body[y → x]`) is
            // `inline`'s job, not channelize's: `inline` unconditionally collapses
            // a bare-`Var` alias before this pass runs — post-uniquify its
            // `!is_let_bound(x)` guard always holds, since a unique `x` is never
            // re-bound in the body. So a bare-`Var` alias whose body feeds the
            // alias handle must never reach here; a survivor would silently
            // mis-route `Feed(y, …)` to the wrong handle. Assert that loudly in
            // debug rather than re-implementing the collapse. (The defer-*returning*
            // lifts above — `try_lift_defer` / the collapse — survive `inline`
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
    defer_names: &[Name],
    chan_names: &HashMap<Name, Name>,
    body: Expr,
    ctx: &mut DesugarCtx,
) -> Result<Expr, DeferError> {
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
        let mut define: Option<Expr> = None;
        rewritten = extract_for_defer(rewritten, name, &mut feeds, &mut define, false, ctx)?;
        let channel = match (feeds.is_empty(), define) {
            (true, None) => return Err(DeferError::NoFeedOrDefine(name.base().to_string())),
            (true, Some(d)) => d,
            (false, None) => combine_feed_values(feeds),
            (false, Some(_)) => {
                return Err(DeferError::FeedsAndDefinesMixed(name.base().to_string()));
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
    if ctx.input_typed {
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
                    ctx.resolved_domains.push((key, dom));
                }
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
        return Err(DeferError::MutuallyRecursiveCycle(name.base().to_string()));
    }
    Ok(bind_cluster_at_scope(rewritten, group))
}

/// Debug invariant: channelization relies on **Barendregt uniqueness**
/// (`uniquify` runs before it), so a channel's captured free variable is never
/// rebound by a `Let` on the wrap-to-feed spine — a body binder and a captured
/// outer variable never share a `uid`, so the emitted `let d = channel` can't
/// be shadow-captured. (A channel legitimately referencing a body-*internal*
/// binding — e.g. an accumulator stream — is excluded: such a name is bound in
/// `body`, hence not free in it, so it never lands in the checked set.) A
/// violation would mean a duplicate binder `uid` reached channelization (e.g. an
/// un-freshened `inline` duplication); catch it loudly here rather than silently
/// mis-scoping a channel.
#[cfg(debug_assertions)]
fn assert_no_shadowed_captures(body: &Expr, channels: &HashMap<Name, Expr>) {
    let mut channel_fvs: HashSet<Name> = HashSet::new();
    for c in channels.values() {
        collect_free_vars(c, &mut channel_fvs);
    }
    let mut body_fvs: HashSet<Name> = HashSet::new();
    collect_free_vars(body, &mut body_fvs);
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
            }
        }
        TypedExprNode::ExprStmt { expr: e, body } => TypedExpr {
            node: TypedExprNode::ExprStmt {
                expr: e,
                body: Box::new(bind_cluster_at_scope(*body, group)),
            },
            ty,
            user_annotation,
        },
        // A letrec's continuation is the scope its trailing reads live in, and
        // a channel assembled from the group's taps (`__hist ≫ .to_<feed>`)
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
            }
        }
        other => {
            let terminal = TypedExpr {
                node: other,
                ty,
                user_annotation,
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
    TypedExpr {
        node: TypedExprNode::LetRec {
            bindings: group,
            body: Box::new(inner),
        },
        ty,
        user_annotation: None,
    }
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
    if let Type::Refinement(_, refinement) = ty {
        // Refinement predicates are themselves CCL expressions; recurse into
        // them through `collect_free_vars` so their own type-position
        // predicates and shadowing are handled consistently.
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
            TypedExprNode::Cast { value, .. } => rec(value, bound, out),
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
            TypedExprNode::MutWrite { value, .. } => rec(value, bound, out),
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
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
/// are merged via [`TypedExprNode::CollectionUnion`] — the dedicated
/// N-ary collection-union node — which compiles to a `UnionOperator`
/// downstream.
///
/// The union is stamped with its type at construction (mirroring
/// `emit_collection_union`): one `FieldKey::Index(i)` domain tag per operand
/// `i`, over the shared element codomain. A defer-read operand contributes
/// its handle's rigid `ChanDom` domain, closed by the final
/// [`erase_chan_domains`] substitution.
fn combine_feed_values(mut feeds: Vec<Expr>) -> Expr {
    debug_assert!(!feeds.is_empty());
    if feeds.len() == 1 {
        return feeds.pop().unwrap();
    }
    let ty = collection_union_type(&feeds);
    Expr::collection_union(feeds).with_ty(ty)
}

/// The type of an N-ary channel union: `Variant[Index(i) ↦ domainᵢ] ⇒ cod`,
/// where each operand contributes its domain as tag `i` and they share a
/// common element codomain. Returns [`Type::Hole`] when an operand is not a
/// function-shaped type at all (the untyped-mode pipeline); a defer-read
/// operand is function-shaped via its handle's stream view, so typed-mode
/// unions are concrete-modulo-`ChanDom` at construction.
fn collection_union_type(feeds: &[Expr]) -> Type {
    let mut tags: Vec<(crate::ccl::FieldKey, Type)> = Vec::with_capacity(feeds.len());
    let mut cod: Option<Type> = None;
    for (i, f) in feeds.iter().enumerate() {
        match peel_refinements(&f.ty) {
            Type::Fun {
                domain, codomain, ..
            } => {
                tags.push((crate::ccl::FieldKey::Index(i), (**domain).clone()));
                match &cod {
                    None => cod = Some((**codomain).clone()),
                    // Every `<<` contribution to one channel is constrained into
                    // the channel's shared `value` var at inference, so the
                    // operand element types must already agree — taking operand
                    // 0's codomain is only sound under that invariant. Name it:
                    // a future feed path bypassing the shared-channel constraint
                    // would otherwise mis-type the union to operand 0 silently.
                    Some(c) => debug_assert_eq!(
                        c.without_pi_names(),
                        codomain.without_pi_names(),
                        "collection_union_type: feed operands disagree on element \
                         type ({c} vs {codomain}); inference should have unified \
                         them into the channel's shared value var"
                    ),
                }
            }
            _ => return Type::Hole,
        }
    }
    match cod {
        Some(c) => Type::fun(Type::Variant(tags), c),
        None => Type::Hole,
    }
}

/// Peel outer `Refinement` wrappers off a type, returning the underlying type.
fn peel_refinements(ty: &Type) -> &Type {
    let mut t = ty;
    while let Type::Refinement(inner, _) = t {
        t = inner;
    }
    t
}

/// Build a [`TypedExprNode::Compose`] typed `Fun(first-domain, last-codomain)`.
/// With nominal channel domains every element is concrete-modulo-`ChanDom` at
/// construction (the feed-history stream view of [`fun_domain`] /
/// [`fun_codomain`]), so a `Hole` here means a genuinely untyped input (the
/// untyped-mode pipeline); the debug residue assert and the strict wall
/// backstop the typed mode.
fn compose_typed_or_hole(elts: Vec<Expr>) -> Expr {
    let d = elts.first().and_then(|e| fun_domain(&e.ty));
    let c = elts.last().and_then(|e| fun_codomain(&e.ty));
    let ty = match (d, c) {
        (Some(d), Some(c)) => Type::fun(d, c),
        _ => Type::Hole,
    };
    Expr::compose(elts).with_ty(ty)
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
/// contexts since the desugared binding would need to escape the inner scope.
fn extract_for_defer(
    expr: Expr,
    defer_name: &Name,
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
        TypedExprNode::Feed { name, value } if &name == defer_name => {
            // Top-level (non-iteration) Feeds carry scalar values that need
            // lifting to `Fun(Unit, T)` to match the defer-handle's
            // expected function shape (the consumer compiles to a
            // SealedFunction operator with Unit domain).  Inside an
            // iteration scope (Lambda body / Loop body), the surrounding
            // Compose/Loop machinery already provides the function shape,
            // so we leave the value scalar — the Compose-with-Lambda case
            // above wraps it with its own `λ x → V` companion.
            //
            // A feed whose value is *already* a collection (`Fun(D, T)`)
            // contributes its whole extent — a top-level `o << (h ≫ .to_o)`
            // hoisted out of a loop by the letrec phase, or any collection
            // feed. It is not lifted (that would double-wrap it as
            // `Fun(Unit, Fun(D, T))`); it joins the channel union directly.
            let value = *value;
            let mut vty = &value.ty;
            while let Type::Refinement(inner, _) = vty {
                vty = inner;
            }
            let is_collection = matches!(vty, Type::Fun { .. });
            let lifted = if in_inner_scope || is_collection {
                value
            } else {
                Expr::lambda("__unused", Type::Base(BaseType::Unit), value)
            };
            feeds.push(lifted);
            TypedExprNode::Lit(Lit::Unit)
        }
        TypedExprNode::Define { name, value } if &name == defer_name => {
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
                ctx,
            )?),
        },
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_expr =
                extract_for_defer(*bound_expr, defer_name, feeds, define, in_inner_scope, ctx)?;
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
                let new_body =
                    extract_for_defer(*body, defer_name, feeds, define, in_inner_scope, ctx)?;
                // Wrap each feed extracted during the body walk with this
                // let-binding — but only when the feed actually references the
                // binding. A channel that escapes the scope where the binding
                // is bound (a generator body inlined out) needs it carried
                // along; a channel that doesn't mention it must *not* be
                // wrapped, or every channel drags in an unused binding — a whole
                // register record, in the worst case (each `http_serve` reply re-emitting
                // a register it never reads). The reference test is
                // `collect_free_vars` rather than `count_free` because the
                // binding may be referenced only through a `user_annotation` /
                // refinement predicate (a filter-feed guard); `collect_free_vars`
                // traverses those, so guard-referenced bindings are kept while
                // dead ones are dropped. Inner lets wrap first as the walk
                // unwinds, so a transitively-referenced binding is exposed as
                // free here by the time this (outer) let checks.
                for feed in feeds.iter_mut().skip(prev_len) {
                    let mut fvs = HashSet::new();
                    collect_free_vars(feed, &mut fvs);
                    if fvs.contains(&binding.name) {
                        let placeholder = Expr::new(TypedExprNode::Lit(Lit::Unit));
                        let original = std::mem::replace(feed, placeholder);
                        // stamp the wrap at construction —
                        // the let's type is its body's, closed over the binder
                        // (the design §6.2 discharge) — there is no
                        // re-derivation pass to fill a `Hole` in.
                        let let_ty =
                            crate::ccl::subst::Subst::discharge(&binding.name, bound_expr.clone())
                                .apply_type(&original.ty);
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
                } = *function
                else {
                    unreachable!("peeked above as a lambda whose param is not the defer binder")
                };
                // Filter-feed pattern: `λ p → Case({g → Feed(d, V); true →
                // Unit})`.  Recognized so we can emit the channel as a source
                // whose *domain type* carries the guard refinement (via the
                // `user_annotation` below) and collapse the original Lambda's
                // body to Unit.  Without this, the generic Case handler wraps
                // both arms in mismatched Records (`to_d: V` vs `to_d: unit`)
                // which
                // fails inference.
                if let Some(fanout_arms) = try_extract_fanout_feed(&lambda_body, defer_name) {
                    let new_argument = extract_for_defer(
                        *argument.clone(),
                        defer_name,
                        feeds,
                        define,
                        in_inner_scope,
                        ctx,
                    )?;
                    // Same fan-out as the Compose case above (differing only in
                    // that the channel applies the value lambda to the refined
                    // source, `refined_source ▷ (λ p → vᵢ)`, rather than
                    // composing): one refined-source channel per feeding arm
                    // (predicate `gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`, the bare element form
                    // `__elem ▷ source ▷ (λ p → predᵢ)`), unioned via `++`. The
                    // two-arm `if g: d << v` shape is the one-feeding-arm case.
                    //
                    // Both sites require the source to be a loop iteration
                    // (function-typed): the per-arm guard rides the source's
                    // *domain* refinement, which `refine_source_domain` stamps
                    // and which planning reifies off `expr.ty.domain()`. That
                    // "source is a `Fun`" precondition is enforced by
                    // `refine_source_domain`'s assert (shared by both fan-out
                    // sites) — a `Case`-feeding `Apply` whose argument is not a
                    // loop source would trip it rather than silently drop the
                    // guard. `unwrap_or(Hole)` here only feeds the pre-refinement
                    // element-var typing; the guard itself lives on the domain.
                    let src_domain = new_argument.ty.domain().unwrap_or(Type::Hole);
                    let src_item = new_argument.ty.codomain().unwrap_or(Type::Hole);
                    let mut prior: Vec<Expr> = Vec::new();
                    for (guard, feed_value) in fanout_arms {
                        if let Some(value) = feed_value {
                            let pred = synthesize_arm_predicate(&guard, &prior);
                            let elem = Expr::var(Name::elem()).with_ty(src_domain.clone());
                            let source_at_elem =
                                Expr::apply(elem, new_argument.clone()).with_ty(src_item.clone());
                            let pred_lambda = Expr::lambda(&param.name, param.ty.clone(), pred);
                            let pred_on_source = Expr::apply(source_at_elem, pred_lambda)
                                .with_ty(Type::Base(BaseType::Bool));
                            let refinement_struct = Refinement {
                                predicate: Rc::new(pred_on_source),
                            };
                            let mut refined_argument = new_argument.clone();
                            refine_source_domain(&mut refined_argument, refinement_struct, ctx);
                            // stamp the channel at
                            // construction (the value lambda's codomain,
                            // matching the non-fanout Apply path) — there is
                            // no re-derivation pass to fill a `Hole` in.
                            let v_ty = value.ty.clone();
                            let channel_lambda = Expr::lambda(&param.name, param.ty.clone(), value);
                            let channel =
                                Expr::apply(refined_argument, channel_lambda).with_ty(v_ty);
                            feeds.push(channel);
                        }
                        prior.push(guard);
                    }
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
                    // `Apply { argument: source-element, function: λ p → v }`
                    // applies the value lambda to the per-element source, so the
                    // companion channel's type is the lambda's codomain `v.ty`
                    // (the argument matches `param.ty`). Typed at construction.
                    let v_ty = v.ty.clone();
                    let channel_lambda = Expr::lambda(&param.name, param.ty.clone(), v);
                    let channel = Expr::apply(new_argument.clone(), channel_lambda).with_ty(v_ty);
                    feeds.push(channel);
                }
                let new_function = TypedExpr {
                    node: TypedExprNode::Lambda {
                        param,
                        body: Box::new(new_lambda_body),
                    },
                    ty: function_ty,
                    user_annotation: function_user_annotation,
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
                TypedExprNode::Apply {
                    function: Box::new(new_function),
                    argument: Box::new(new_argument),
                }
            }
        }
        // `cast` wraps a pure value; recurse into it and keep `target`.
        TypedExprNode::Cast { value, target } => TypedExprNode::Cast {
            value: Box::new(extract_for_defer(
                *value,
                defer_name,
                feeds,
                define,
                in_inner_scope,
                ctx,
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
                            // `lower::comprehension`), then wraps the source's
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
                            let source_prefix = if new_elts.len() == 1 {
                                new_elts[0].clone()
                            } else {
                                typed_compose(new_elts.clone())
                            };
                            let src_domain = source_prefix.ty.domain().unwrap_or(Type::Hole);
                            let src_item = source_prefix.ty.codomain().unwrap_or(Type::Hole);
                            let mut prior: Vec<Expr> = Vec::new();
                            for (guard, feed_value) in fanout_arms {
                                if let Some(value) = feed_value {
                                    let pred = synthesize_arm_predicate(&guard, &prior);
                                    let elem = Expr::var(Name::elem()).with_ty(src_domain.clone());
                                    let source_at_elem = Expr::apply(elem, source_prefix.clone())
                                        .with_ty(src_item.clone());
                                    let pred_lambda =
                                        Expr::lambda(&param.name, param.ty.clone(), pred);
                                    let pred_on_source = Expr::apply(source_at_elem, pred_lambda)
                                        .with_ty(Type::Base(BaseType::Bool));
                                    let refinement_struct = Refinement {
                                        predicate: Rc::new(pred_on_source),
                                    };
                                    let mut refined_prefix = source_prefix.clone();
                                    refine_source_domain(
                                        &mut refined_prefix,
                                        refinement_struct,
                                        ctx,
                                    );
                                    let channel_lambda =
                                        Expr::lambda(&param.name, param.ty.clone(), value);
                                    // stamp the channel at
                                    // construction — `Fun(refined-domain,
                                    // value)` off the two elements' concrete
                                    // types; there is no re-derivation pass
                                    // to fill a `Hole` in.
                                    let channel_expr =
                                        compose_typed_or_hole(vec![refined_prefix, channel_lambda]);
                                    feeds.push(channel_expr);
                                }
                                prior.push(guard);
                            }
                            // Every feed for this defer is extracted; the
                            // original lambda body collapses to `Unit` (after
                            // lambda elim it composes with the unrefined source
                            // to a no-op iteration).
                            let new_lambda = TypedExpr {
                                node: TypedExprNode::Lambda {
                                    param,
                                    body: Box::new(Expr::lit(Lit::Unit)),
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
                            // `Expr::lambda` stamps `Fun(param.ty, v.ty)`; the
                            // param carries the matched lambda's own (concrete)
                            // type, so the companion value lambda is fully typed.
                            // The compose type is `Fun(prefix-domain, v.ty)`;
                            // a prefix that is itself a defer read carries its
                            // handle's rigid `ChanDom` domain, closed by the
                            // final `erase_chan_domains` substitution.
                            let channel_lambda = Expr::lambda(&param.name, param.ty.clone(), v);
                            let mut channel_elts = new_elts.clone();
                            channel_elts.push(channel_lambda);
                            // A single-element "compose" is just that
                            // element; otherwise build a Compose.
                            let channel_expr = if channel_elts.len() == 1 {
                                channel_elts.into_iter().next().unwrap()
                            } else {
                                compose_typed_or_hole(channel_elts)
                            };
                            feeds.push(channel_expr);
                        }
                        new_elts.push(TypedExpr {
                            node: TypedExprNode::Lambda {
                                param,
                                body: Box::new(new_body),
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
            let mut local_feeds: Vec<Expr> = Vec::new();
            let mut local_define: Option<Expr> = None;
            let body = if &param.name == defer_name {
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
                // A feeding `Case` that reached the generic structural recursion
                // — i.e. one *not* wrapped in the iteration `Compose`/`Apply`
                // that the fan-out sites above intercept, so there is no
                // iteration source to restrict per arm. The loop-sourced
                // multi-arm fan-out (`if g: d << v` and `if/elif` in a for-loop
                // body) is handled at those sites via `try_extract_fanout_feed`,
                // one refined-source channel per arm `i` predicated on
                // `gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`. A *source-less* conditional feed has no
                // refinement to hang the guard on, so reject it rather than
                // mishandle. (The former Record-based fan-out is retired — it
                // published an ill-typed `Unit` empty-channel for no-feed arms,
                // a silent miscompile.)
                return Err(DeferError::PartialFeedCaseUnsupported(
                    defer_name.to_string(),
                ));
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
                ctx,
            )?),
        },
        // Recognition runs after lambda_elim, so a
        // causal `LetRec` reaches feed extraction. Walk its binding bodies
        // and continuation generically — the phase hoists every in-loop /
        // in-block feed to the letrec *body* (`Feed(defer, tap)` ExprStmts),
        // so extraction finds them there; binding bodies carry no feeds but
        // are walked for totality. Binder shadowing of `defer_name` is
        // impossible post-uniquify.
        TypedExprNode::LetRec { mut bindings, body } => {
            for (_, def) in bindings.iter_mut() {
                let taken = std::mem::take(def);
                *def = extract_for_defer(taken, defer_name, feeds, define, in_inner_scope, ctx)?;
            }
            let body = extract_for_defer(*body, defer_name, feeds, define, in_inner_scope, ctx)?;
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
                    let probe = TypedExpr {
                        node: node.clone(),
                        ty: ty.clone(),
                        user_annotation: user_annotation.clone(),
                    };
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
    })
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

    #[test]
    fn run_single_feed() {
        let body = Expr::expr_stmt(Expr::feed("d", lit(1)), var("d"));
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(expr, false).unwrap();
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
        let body = Expr::expr_stmt(Expr::define("d", lit(42)), var("d"));
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(expr, false).unwrap();
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
        let err = run(expr, false).unwrap_err();
        assert_eq!(err, DeferError::NoFeedOrDefine("d".into()));
    }

    /// Multiple feeds: union'd via collection_union.
    #[test]
    fn run_multiple_feeds_use_collection_union() {
        let body = Expr::expr_stmt(
            Expr::feed("d", lit(1)),
            Expr::expr_stmt(Expr::feed("d", lit(2)), var("d")),
        );
        let expr = Expr::let_bind("d", Expr::new(TypedExprNode::Defer), body);
        let result = run(expr, false).unwrap();
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
        let result = run(with_a, false).expect("cluster resolution should succeed");
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
        let err = run(with_a, false).unwrap_err();
        assert!(
            matches!(err, DeferError::MutuallyRecursiveCycle(_)),
            "expected MutuallyRecursiveCycle, got {err:?}"
        );
    }

    /// A multi-arm `Case` feeding the defer in some arm, wrapped in an
    /// `Apply(source, λ …)` iteration, fans out into one refined-source channel
    /// per feeding arm (`try_extract_fanout_feed`) — the former
    /// `PartialFeedCaseUnsupported` rejection is retired. Here the sole feeding
    /// arm (`x > 0`) yields a refined channel; the `false` arm contributes
    /// nothing. (Exercises the `Apply`-site fan-out; the `Compose`-site path has
    /// end-to-end coverage in `tests/compilation_pipeline/feeds_cases.rs`.)
    #[test]
    fn run_multi_arm_case_feed_fans_out() {
        let guard = Expr::new(TypedExprNode::BinOp {
            left: Box::new(var("x")),
            op: BinOpKind::Compare(crate::ccl::CompareKind::Greater),
            right: Box::new(lit(0)),
        });
        let feeding_arm = Branch {
            pattern: None,
            guard,
            body: Expr::feed("d", var("x")),
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
        assert!(
            run(with_d, false).is_ok(),
            "a multi-arm Case feeding the defer must fan out, not be rejected"
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
        let refinement = Refinement {
            predicate: Rc::new(pred),
        };
        let annotated = TypedExpr {
            node: TypedExprNode::Var(Name::raw("__chan")),
            ty: Type::Hole,
            user_annotation: Some(Type::fun(
                Type::Refinement(Box::new(Type::Hole), refinement),
                Type::Hole,
            )),
        };

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
        let refinement = Refinement {
            predicate: Rc::new(pred),
        };
        let typed = TypedExpr {
            node: TypedExprNode::Lit(Lit::Unit),
            ty: Type::Fun {
                name: None,
                domain: Box::new(Type::Refinement(Box::new(Type::Hole), refinement)),
                codomain: Box::new(Type::Hole),
            },
            user_annotation: None,
        };
        let mut free: HashSet<Name> = HashSet::new();
        collect_free_vars(&typed, &mut free);
        assert!(
            free.contains(&Name::raw("inner_k")),
            "expr.ty predicate reference should be collected: got {free:?}"
        );
    }
}

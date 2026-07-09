//! Desugar `Defer`/`Feed`/`Define`/`ExprStmt` nodes into structural
//! let-chain bindings, per-scope `to_<defer>` Record fields, and
//! refined-source channels.
//!
//! Runs **after** [`crate::ccl::infer`] — type errors report against the
//! user-shaped tree (inference types the defer constructs directly: see
//! `design/type-inference.md` §"Feed handles") — and the pass is
//! **type-preserving**: it ends with a retype synthesis
//! ([`crate::ccl::infer::retype`]) that erases the transient
//! `Feed` / `Infer`-channel-domain types along with the nodes.  After
//! this pass, no [`TypedExprNode::Defer`], [`TypedExprNode::Feed`],
//! [`TypedExprNode::Define`], or [`TypedExprNode::ExprStmt`] nodes — and
//! no `Feed`/`Hole`/`Infer` types — remain in the tree; every downstream
//! pass treats those variants as `unreachable!`.
//!
//! # Prototype status
//!
//! **This pass is a prototype.**  The shapes it handles cover the
//! current end-to-end test corpus, but an open design question
//! remains — the N-arm (`if`/`elif`) Case-with-feeds fan-out (rejected
//! today with `DeferError::PartialFeedCaseUnsupported`; see the Case arm
//! of [`extract_for_defer`]).  Expect the algorithm to be reworked
//! rather than incrementally patched.  The umbrella tracking entry lives
//! in `docs/plan.md` under "Tech Debt — `desugar_defers` prototype".
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
//! The full design — the cluster channelization algorithm, per-shape
//! extraction paths (Compose/Apply iteration lambdas, Loop body
//! absorption, filter-feed Case, Case-arm fan-out, defer-returning
//! lift, alias inlining), error modes, known gaps, and a navigation
//! map for the source — lives in `src/ccl/design/desugar-defers.md`.
//! (That doc still describes the retired defer-mediating-UDF chain
//! rewriter / smart walker; `inline` now beta-reduces those UDFs
//! before this pass, so that machinery no longer exists here.)
//!
//! The function-level docs in this file explain individual moving
//! parts; this module comment is the entry point.

use std::collections::{HashMap, HashSet};
use std::fmt;

use std::rc::Rc;

use crate::ccl::{
    BaseType, Branch, Expr, Lit, Name, Pattern, Refinement, Type, TypedBinding, TypedExpr,
    TypedExprNode,
    ccl_utils::{count_free, typed_compose},
    try_walk_transact, walk_transact,
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
    /// A multi-arm `Case` feeds a defer in some arms but not others.
    /// The fan-out rewrite would need a *typed* empty channel for the
    /// non-feeding arms (the planned refinement-based N-arm fan-out;
    /// see the design doc's known-gaps section); until then the shape
    /// is rejected rather than miscompiled. Unreachable from CHL today
    /// — lowering rejects `elif` inside generator bodies first.
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

/// Recognise the filter-feed pattern: a two-branch `Case` matching
/// `{guard → Feed(defer_name, V); true → Unit}`.  Returns
/// `Some((guard, V))` on a match, `None` otherwise.
///
/// This is the desugar-stage counterpart of `lambda_elim`'s
/// `is_filter_case_body`: pre-elim Lambdas wrapping such a Case need
/// their channel emitted as a refined Lambda rather than a Record-
/// over-Cases (which would produce a `to_d: V` vs `to_d: Unit` arm
/// shape mismatch).
///
/// FIXME(desugar_defers-prototype): only the 2-arm shape is recognised;
/// 3+-arm Cases with feeds in some-but-not-all arms are rejected with
/// `DeferError::PartialFeedCaseUnsupported`.  See the umbrella entry in
/// `docs/plan.md` ("Tech Debt — `desugar_defers` prototype") for the planned
/// N-arm refinement-based fan-out (an extension of this two-arm path).
fn try_extract_filter_feed(body: &Expr, defer_name: &Name) -> Option<(Expr, Expr)> {
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
/// [`desugar_substitute`], which also renames the *target* name of
/// `Feed`/`Define` nodes when the replacement is a `Var` — so
/// `Feed("x", …)` becomes `Feed("y", …)` automatically.
///
/// Also handles an optional `ExprStmt` prefix on `bound_expr`: the
/// heads of any leading ExprStmts become a prefix that's prepended to
/// the lifted body, with stale Feed/Define target names renamed to `y`.
fn try_lift_defer(binding_name: &Name, bound_expr: &Expr, body: &Expr) -> Option<Expr> {
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

    Some(Expr::let_bind(
        binding_name,
        Expr::new(TypedExprNode::Defer),
        spliced,
    ))
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

/// Return `true` if any nested `Let` or `Lambda` inside `expr` rebinds
/// `name` (shadowing it).  Used by the alias-inline check to avoid
/// substituting an alias name with a source name that would be captured
/// by a shadowing rebind inside the body.
fn rebinds(expr: &Expr, name: &Name) -> bool {
    // Recognise binder variants that introduce `name` directly.  Lambda's
    // refinement and Let's bound_expr live in the outer scope (not bound
    // by the param/binding), but if they themselves contain a rebind of
    // `name` further down, `any_child` finds it via structural recursion
    // below — no need to short-circuit on the binder structure here.
    let here = match &expr.node {
        TypedExprNode::Let { binding, .. } => &binding.name == name,
        TypedExprNode::Lambda { param, .. } => &param.name == name,
        TypedExprNode::Case { branches, .. } => branches
            .iter()
            .any(|b| b.pattern.as_ref().is_some_and(|p| &p.binding.name == name)),
        _ => false,
    };
    here || expr.any_child(|c| rebinds(c, name))
}

/// Return `true` if `expr` contains any `Feed(target, …)` or
/// `Define(target, …)` node where `target == name`, respecting shadowing
/// by `Let`/`Lambda` bindings that rebind `name`.
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
}

impl DesugarCtx {
    fn new() -> Self {
        Self { input_typed: false }
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
/// `Unit`-typed value that can be dropped.  Doing this in `desugar_defers`
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
        // Synthesize the types this pass left as residue — `Hole` on
        // constructed/invalidated nodes, the erased `Feed` / channel-domain
        // `Infer` types on defer reads — from the surviving inferred types.
        // A failure here is a compiler bug (desugar produced a shape the
        // synthesizer can't type), not a user error; the strict post-desugar
        // `typecheck` in `compile_program` backstops the same invariant.
        if let Err(errs) = crate::ccl::infer::retype(&mut rewritten) {
            panic!("desugar_defers: retype failed on the desugared tree: {errs:#?}");
        }
        #[cfg(debug_assertions)]
        assert_no_type_residue(&rewritten);
    }
    Ok(rewritten)
}

/// Debug-only invariant: after [`run`] on a typed input, no expression or
/// binder slot may still carry a `Hole`, `Infer`, or `Feed` type — desugar
/// erased the defer constructs, so their transient types must be gone too.
/// (Refinement predicates are checked by the strict `typecheck` instead;
/// walking them here would need the cycle guards it already has.)
#[cfg(debug_assertions)]
fn assert_no_type_residue(expr: &Expr) {
    use crate::ccl::infer::has_type_residue;
    assert!(
        !has_type_residue(&expr.ty),
        "type residue survived desugar_defers on `{}` : {}",
        crate::ccl::symbolic::symbolic(expr),
        expr.ty
    );
    match &expr.node {
        TypedExprNode::Lambda { param, .. } => assert!(
            !has_type_residue(&param.ty),
            "type residue survived desugar_defers on lambda param `{}` : {}",
            param.name,
            param.ty
        ),
        TypedExprNode::Let { binding, .. } => assert!(
            !has_type_residue(&binding.ty),
            "type residue survived desugar_defers on let binding `{}` : {}",
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
        // An effect subtree carrying a `For`/`MutWrite` is a pre-phase
        // marker the unified letrec phase consumes (design/mutability.md)
        // — the statement is load-bearing, not extracted-feed residue.
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
        TypedExprNode::Transact {
            keys,
            writers,
            domain,
        } => walk_transact(keys, writers, domain, drop_expr_stmts),
        // Pure structural recursion: no ExprStmt can hide from the walk
        // inside a binding body.
        TypedExprNode::LetRec { bindings, body } => TypedExprNode::LetRec {
            bindings: bindings
                .into_iter()
                .map(|(b, def)| (b, drop_expr_stmts(def)))
                .collect(),
            body: Box::new(drop_expr_stmts(*body)),
        },
        // Pre-phase markers: preserved for the unified letrec phase (their
        // interior ExprStmt chains are kept by the marker-bearing arm above).
        TypedExprNode::For { target, iter, body } => TypedExprNode::For {
            target,
            iter: Box::new(drop_expr_stmts(*iter)),
            body: Box::new(drop_expr_stmts(*body)),
        },
        TypedExprNode::MutWrite { name, value } => TypedExprNode::MutWrite {
            name,
            value: Box::new(drop_expr_stmts(*value)),
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
        TypedExprNode::Transact { keys, writers, .. } => {
            keys.iter()
                .try_for_each(|k| assert_no_defer_residue(&k.init))?;
            writers.iter().try_for_each(|w| {
                assert_no_defer_residue(&w.source)?;
                assert_no_defer_residue(&w.body)
            })
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
                let renamed = desugar_substitute(spliced, &inner_name, &Expr::var(&binding.name));
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
            // [`desugar_substitute`] renames the *target* name of
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
                let substituted = desugar_substitute(body, &binding.name, &bound_expr);
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
    defer_names: &[Name],
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
    // Topologically order the bindings: a defer whose channel references
    // another cluster defer is bound after that defer.
    let order = topo_sort_cluster(defer_names, &channels)?;
    // Wrap the body's terminal with the cluster's let-chain in order —
    // first α-renaming any downstream Let-shadows of channel free
    // variables so the channels keep referring to the values they
    // captured at their original feed positions.
    let protected: HashSet<Name> = compute_protected_set(&rewritten, &channels);
    Ok(rename_shadows_then_bind(
        rewritten, &order, channels, &protected,
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
fn compute_protected_set(body: &Expr, channels: &HashMap<Name, Expr>) -> HashSet<Name> {
    let mut channel_fvs: HashSet<Name> = HashSet::new();
    for c in channels.values() {
        collect_free_vars(c, &mut channel_fvs);
    }
    let mut body_fvs: HashSet<Name> = HashSet::new();
    collect_free_vars(body, &mut body_fvs);
    channel_fvs.intersection(&body_fvs).cloned().collect()
}

/// Walk `expr` through `Let`/`ExprStmt` bodies to its terminal,
/// α-renaming any `Let n = E in inner` where `n ∈ protected_set` so
/// the inner shadowing is broken.  At the terminal, emit the cluster's
/// let-chain in topological order.
fn rename_shadows_then_bind(
    expr: Expr,
    order: &[Name],
    channels: HashMap<Name, Expr>,
    protected: &HashSet<Name>,
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
            let fresh = Name::shadow_rename();
            let new_body = desugar_substitute(*body, &binding.name, &Expr::var(&fresh));
            let new_binding = TypedBinding {
                name: fresh,
                ty: binding.ty,
                user_annotation: binding.user_annotation,
            };
            TypedExpr {
                node: TypedExprNode::Let {
                    binding: new_binding,
                    bound_expr,
                    body: Box::new(rename_shadows_then_bind(
                        new_body, order, channels, protected,
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
                    body: Box::new(rename_shadows_then_bind(*body, order, channels, protected)),
                },
                ty,
                user_annotation,
            }
        }
        TypedExprNode::ExprStmt { expr: e, body } => TypedExpr {
            node: TypedExprNode::ExprStmt {
                expr: e,
                body: Box::new(rename_shadows_then_bind(*body, order, channels, protected)),
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

/// Wrap `inner` with the cluster's `let n_i = channel_i in …` bindings
/// in topological order (so dependencies are bound before dependents).
fn emit_cluster_then(inner: Expr, order: &[Name], mut channels: HashMap<Name, Expr>) -> Expr {
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
/// - `expr.ty` refinement predicates (including a lambda's refined domain)
/// - `expr.user_annotation` refinement predicates (set by
///   [`extract_for_defer`]'s filter-feed rewrite)
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
    defer_names: &[Name],
    channels: &HashMap<Name, Expr>,
) -> Result<Vec<Name>, DeferError> {
    let names: Vec<Name> = defer_names.to_vec();
    // Build dependency edges: d_i depends on d_j if d_i's channel references Var(d_j).
    let mut deps: HashMap<&Name, Vec<&Name>> = HashMap::new();
    for d in &names {
        let mut d_deps = Vec::new();
        if let Some(channel) = channels.get(d) {
            for other in &names {
                if other != d && count_free(other, channel) > 0 {
                    d_deps.push(other);
                }
            }
        }
        deps.insert(d, d_deps);
    }
    let mut sorted: Vec<Name> = Vec::with_capacity(names.len());
    let mut visited: HashSet<Name> = HashSet::new();
    let mut visiting: HashSet<Name> = HashSet::new();
    fn visit(
        name: &Name,
        deps: &HashMap<&Name, Vec<&Name>>,
        visited: &mut HashSet<Name>,
        visiting: &mut HashSet<Name>,
        sorted: &mut Vec<Name>,
    ) -> Result<(), DeferError> {
        if visited.contains(name) {
            return Ok(());
        }
        if visiting.contains(name) {
            // Cycle — currently unsupported.
            return Err(DeferError::MutuallyRecursiveCycle(name.base().to_string()));
        }
        visiting.insert(name.clone());
        if let Some(dep_list) = deps.get(name) {
            for dep in dep_list {
                visit(dep, deps, visited, visiting, sorted)?;
            }
        }
        visiting.remove(name);
        visited.insert(name.clone());
        sorted.push(name.clone());
        Ok(())
    }
    for d in &names {
        visit(d, &deps, &mut visited, &mut visiting, &mut sorted)?;
    }
    Ok(sorted)
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
            // Store keys are labels, not feed targets; each writer body is a
            // lambda that shadows its own binders via the `Lambda`/`Let` arms.
            TypedExprNode::Transact { keys, writers, .. } => {
                for k in keys {
                    rec(&k.init, bound, out);
                }
                for w in writers {
                    rec(&w.source, bound, out);
                    rec(&w.body, bound, out);
                }
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
            TypedExprNode::VariantCtor { .. } => {
                unreachable!("desugar_defers: VariantCtor not yet emitted by lowering")
            }
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
fn combine_feed_values(mut feeds: Vec<Expr>) -> Expr {
    debug_assert!(!feeds.is_empty());
    if feeds.len() == 1 {
        return feeds.pop().unwrap();
    }
    Expr::collection_union(feeds)
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
                // store, in the worst case (each `http_serve` reply re-emitting
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
                        *feed = Expr::let_bind(binding.name.clone(), bound_expr.clone(), original);
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
                    // Same refinement strategy as the Compose case above: the
                    // bare predicate `__elem ▷ source ▷ (λ p → guard)` (the
                    // element form planning expects — see that case and
                    // `lower::comprehension`), fully typed, then wrap the
                    // source's *domain* in `Refinement(_, pred)`. The channel is
                    // `refined_source ▷ (λ p → V)`.
                    let src_domain = new_argument.ty.domain().unwrap_or(Type::Hole);
                    let src_item = new_argument.ty.codomain().unwrap_or(Type::Hole);
                    let elem = Expr::var(Name::elem()).with_ty(src_domain);
                    let source_at_elem = Expr::apply(elem, new_argument.clone()).with_ty(src_item);
                    let pred_lambda = Expr::lambda(&param.name, param.ty.clone(), guard);
                    let pred_on_source = Expr::apply(source_at_elem, pred_lambda)
                        .with_ty(Type::Base(BaseType::Bool));
                    let refinement_struct = Refinement {
                        predicate: Rc::new(pred_on_source),
                    };
                    let mut refined_argument = new_argument.clone();
                    refine_source_domain(&mut refined_argument, refinement_struct, ctx);
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
                        // Filter-feed: `λ p → Case({g → Feed(d, V); true →
                        // Unit})` becomes a refined-Lambda channel
                        // (`λ p with {g} → V`) plus a Lambda whose body
                        // is `Unit`.  See [`try_extract_filter_feed`].
                        if let Some((guard, feed_value)) =
                            try_extract_filter_feed(&body, defer_name)
                        {
                            // Construct the refined source exactly as a
                            // filtered comprehension does (`lower::comprehension`
                            // / `lower::exprs`): a *bare* predicate
                            // `__elem ▷ source ▷ (λ p → guard)` referencing the
                            // domain element `__elem`, then wrap the source's
                            // *domain* in `Refinement(_, pred)` so planning
                            // restricts the iteration to guard-passing indices.
                            //
                            // The predicate MUST reference `__elem` in this
                            // element form: planning's
                            // `compile_refinement_predicates` η-expands
                            // `λ __elem → pred` and lambda-eliminates it, so a
                            // predicate constant in `__elem` (e.g. the point-free
                            // `source ≫ guard`) collapses to `const(_)` and drops
                            // the per-element test. It is also fully typed here —
                            // a `Refinement` predicate is immutable, so `retype`
                            // never re-derives it.
                            let source_prefix = if new_elts.len() == 1 {
                                new_elts[0].clone()
                            } else {
                                typed_compose(new_elts.clone())
                            };
                            let src_domain = source_prefix.ty.domain().unwrap_or(Type::Hole);
                            let src_item = source_prefix.ty.codomain().unwrap_or(Type::Hole);
                            let elem = Expr::var(Name::elem()).with_ty(src_domain);
                            let source_at_elem =
                                Expr::apply(elem, source_prefix.clone()).with_ty(src_item);
                            let pred_lambda = Expr::lambda(&param.name, param.ty.clone(), guard);
                            let pred_on_source = Expr::apply(source_at_elem, pred_lambda)
                                .with_ty(Type::Base(BaseType::Bool));
                            let refinement_struct = Refinement {
                                predicate: Rc::new(pred_on_source),
                            };
                            let mut refined_prefix = source_prefix.clone();
                            refine_source_domain(&mut refined_prefix, refinement_struct, ctx);
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
                // A multi-arm `Case` that feeds the defer in one or more arms.
                // The two-arm filter shape `{guard → d << v; true → unit}` is
                // handled earlier as a refined-source channel
                // (`try_extract_filter_feed`); anything else is the N-arm fan-out
                // — not yet supported. The proper lowering is to extend that
                // refinement fan-out to N arms (a refined source per arm `i`
                // predicated on `¬g₀ ∧ … ∧ ¬g_{i-1} ∧ gᵢ`); the former
                // Record-based fan-out is retired (it published an ill-typed
                // `Unit` empty-channel for no-feed arms — a silent miscompile).
                // Reject up front rather than mishandle. Unreachable from CHL
                // today: lowering rejects `elif` inside a generator for-loop
                // body, so a multi-arm feed `Case` never reaches here.
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
        // Feeds are hoisted out of writer bodies before recognition, so a
        // `Transact` carries no `Feed`/`Define` for any defer (a per-iteration
        // feed rides the store body as `Feed(defer, __store.to_<defer>)`,
        // handled by the top-level `Feed` arm). Recurse structurally; each
        // writer body is a `Lambda`, so its own arm supplies the inner scope.
        TypedExprNode::Transact {
            keys,
            writers,
            domain,
        } => try_walk_transact(keys, writers, domain, |c| {
            extract_for_defer(c, defer_name, feeds, define, in_inner_scope, ctx)
        })?,
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
        // Feed extraction has load-bearing per-variant scope rules
        // (`in_inner_scope`, the Loop `to_<defer>` machinery); how a
        // recursive group would participate is exactly what the unified
        // phase defines — reject rather than guess.
        TypedExprNode::LetRec { .. } => {
            unreachable!(
                "LetRec is not emitted before desugar_defers yet — the unified phase \
                 (src/ccl/design/mutability.md) lands it and replaces this pass"
            )
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
    // `channelize_cluster` / `rename_shadows_then_bind` without going
    // through the full pipeline.
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
        let result = run(with_a, false).expect("topological resolution should succeed");
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

    /// A multi-arm `Case` that feeds the defer in some arm is rejected with
    /// `PartialFeedCaseUnsupported` (the former Record-based fan-out, which
    /// published an ill-typed empty channel for no-feed arms, is retired — the
    /// N-arm refinement fan-out that will replace it is not built yet).
    #[test]
    fn run_multi_arm_case_feed_is_rejected() {
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
            matches!(
                run(with_d, false),
                Err(DeferError::PartialFeedCaseUnsupported(_))
            ),
            "a multi-arm Case feeding the defer must be rejected"
        );
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

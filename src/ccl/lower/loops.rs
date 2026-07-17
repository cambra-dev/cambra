//! `for`-loop lowering: side-effecting / generator (`yield`) loops lowering to
//! `For` nodes, and mutation-accumulation loops lowering to `Loop` nodes.

use std::collections::HashSet;

use super::*;
use crate::{
    ccl::{Branch, Builtin, Expr, Lit, Name, Type, TypedExprNode},
    chl_parser::ast::{AssignTarget, Expr as ChlExpr, Spanned, Stmt as ChlStmt},
};

// ---------------------------------------------------------------------------
// For-loop lowering — For CCL node
// ---------------------------------------------------------------------------

/// Return `true` if any statement in `stmts` contains a `yield` expression
/// (checked recursively through `if` guards and nested `for` loops).
///
/// Does not recurse into `with`/`try` blocks — those are rejected later by
/// the "only assignments and function definitions" check in `lower_for_body_stmts`.
fn for_body_has_yield(stmts: &[Spanned<ChlStmt>]) -> bool {
    stmts.iter().any(stmt_has_yield)
}

fn stmt_has_yield(stmt: &Spanned<ChlStmt>) -> bool {
    match &stmt.node {
        ChlStmt::Expr(value) => matches!(&value.node, ChlExpr::Yield(_)),
        ChlStmt::If {
            branches,
            else_body,
        } => {
            branches.iter().any(|b| for_body_has_yield(&b.body))
                || else_body.as_deref().is_some_and(for_body_has_yield)
        }
        ChlStmt::For { body, .. } => for_body_has_yield(body),
        _ => false,
    }
}

/// Lower a `for` statement to a `Compose([src, Lambda(x, body)])` CCL expression.
///
/// When the body contains `yield`, the loop is desugared:
/// ```text
/// for i in src:
///     yield e
/// ```
/// becomes
/// ```text
/// let __result = defer() in
///     (src ≫ λi → feed(__result, e)); __result
/// ```
///
/// When the body uses `<<` directly (feeding into a pre-existing defer), the
/// Compose+Lambda is returned with `Unit` type.
///
/// `outer_bindings` carries all names in scope above this loop (function args
/// and preceding lets). Assignments to these names inside the body are rejected
/// as mutation.
pub(super) fn lower_generator_for(
    target: &Spanned<AssignTarget>,
    iter: &Spanned<ChlExpr>,
    body: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let iter_var = extract_name_target(target, "for-loop target")?;

    if for_body_has_yield(body) {
        // A generator with loop-carried state (mutability design notes, §4b) — yield
        // alongside mutation of an outer-scope variable — routes through
        // the same `Loop` lowering as a plain mutation loop, with the
        // yield-defer's per-iteration feed picked up by `desugar_defers`
        // as another `to_<defer>` field on the body Record.  Detect
        // mutation first so we can dispatch on it.
        let acc_names = find_mutation_loop_vars(body, outer_bindings);
        if !acc_names.is_empty() {
            // The generator's defer is bound around the mutation loop
            // and used as the continuation — same shape as the plain
            // yield-only path below.
            let defer_name = ctx.fresh_result_name();
            let inner = lower_mutation_loop(
                target,
                iter,
                body,
                &acc_names,
                Expr::var(defer_name.clone()),
                Some(&defer_name),
                ctx,
            )?;
            return Ok(Expr::let_bind(
                defer_name,
                Expr::new(TypedExprNode::Defer),
                inner,
            ));
        }

        let source = lower_expr(iter, ctx)?;
        let frame_introduced = HashSet::from([iter_var.clone()]);
        // Plain yield without loop-carried mutation: desugar yield → defer + feed.
        let defer_name = ctx.fresh_result_name();
        let for_body = lower_for_body_stmts(
            body,
            Some(&defer_name),
            outer_bindings,
            frame_introduced,
            ctx,
        )?;
        let for_node = Expr::for_loop(iter_var, source, for_body);
        let seq = Expr::expr_stmt(for_node, Expr::var(defer_name.clone()));
        Ok(Expr::let_bind(
            defer_name,
            Expr::new(TypedExprNode::Defer),
            seq,
        ))
    } else {
        let source = lower_expr(iter, ctx)?;
        let frame_introduced = HashSet::from([iter_var.clone()]);
        let for_body = lower_for_body_stmts(body, None, outer_bindings, frame_introduced, ctx)?;
        Ok(Expr::for_loop(iter_var, source, for_body))
    }
}

/// Lower the body statements of a `for`-loop to a single CCL expression.
///
/// Leading statements are lowered to nested [`TypedExprNode::Let`] bindings.
/// The final statement is lowered by [`lower_for_body_terminal`].
///
/// `defer_name` — if `Some`, `yield e` terminals are replaced with
/// `feed(defer_name, e)`. If `None`, a `yield` is an error.
///
/// `mutation_scope` — names that cannot be assigned to (function args,
/// pre-loop lets, and enclosing for's iteration variables). Assignments to
/// these produce a mutation error.
///
/// `frame_introduced` — names introduced by the current for clause (the
/// iteration variable) and any let-bindings accumulated so far. These may
/// be re-bound (shadowed) inside the body without triggering a mutation error.
fn lower_for_body_stmts(
    stmts: &[Spanned<ChlStmt>],
    defer_name: Option<&str>,
    mutation_scope: &HashSet<String>,
    mut frame_introduced: HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Reached via `lower_for_body_stmts` from a parsed for-loop body, which
    // goes through the CHL `block` parser (`.at_least(1)`). Empty here means
    // a caller has bypassed the parser.
    assert!(
        !stmts.is_empty(),
        "lower_for_body_stmts: empty body (parser invariant violated)"
    );
    let (last, rest) = stmts.split_last().unwrap();

    let mut bindings: Vec<(String, Expr, Option<Type>)> = Vec::new();

    for stmt in rest {
        match &stmt.node {
            ChlStmt::Assign { target, value } => {
                let name = extract_name_target(target, "assignment")?;
                if mutation_scope.contains(&name) {
                    return Err(LoweringError::unsupported(
                        stmt.span,
                        format!(
                            "assignment to `{name}` is mutation: `{name}` is bound \
                         outside the for-loop body (function argument or \
                         pre-loop binding)",
                        ),
                    ));
                }
                let val = lower_expr(value, ctx)?;
                frame_introduced.insert(name.clone());
                bindings.push((name, val, None));
            }
            ChlStmt::AnnAssign {
                target,
                annotation,
                value,
            } => {
                let name = extract_name_target(target, "annotated assignment")?;
                if mutation_scope.contains(&name) {
                    return Err(LoweringError::unsupported(
                        stmt.span,
                        format!(
                            "assignment to `{name}` is mutation: `{name}` is bound \
                         outside the for-loop body (function argument or \
                         pre-loop binding)",
                        ),
                    ));
                }
                let ann = lower_type_annotation(annotation)?;
                let val = lower_expr(value, ctx)?;
                frame_introduced.insert(name.clone());
                bindings.push((name, val, Some(ann)));
            }
            ChlStmt::AugAssign { target, op, value } => {
                let name = extract_name_target(target, "augmented assignment")?;
                if mutation_scope.contains(&name) {
                    return Err(LoweringError::unsupported(
                        stmt.span,
                        format!(
                            "assignment to `{name}` is mutation: `{name}` is bound \
                         outside the for-loop body (function argument or \
                         pre-loop binding)",
                        ),
                    ));
                }
                if !frame_introduced.contains(&name) {
                    // x op= e is only valid if x was already introduced in this frame.
                    return Err(LoweringError::unsupported(
                        stmt.span,
                        format!(
                            "augmented assignment to `{name}` in for-loop body: \
                         `{name}` is not bound in this body. Use `{name} = expr` \
                         for a fresh binding.",
                        ),
                    ));
                }
                let val = lower_aug_binop(&name, *op, value, ctx)?;
                bindings.push((name, val, None));
            }
            ChlStmt::Define { .. } => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "`<<=` as a non-terminal statement in a for-loop body \
                     is not supported",
                ));
            }
            ChlStmt::FunctionDef {
                name,
                params,
                body: fn_body,
            } => {
                let name_str = name.as_str().to_string();
                if mutation_scope.contains(&name_str) {
                    return Err(LoweringError::unsupported(
                        stmt.span,
                        format!(
                            "assignment to `{name_str}` is mutation: `{name_str}` is bound \
                         outside the for-loop body (function argument or \
                         pre-loop binding)",
                        ),
                    ));
                }
                let func_expr = lower_function_body(stmt.span, params, fn_body, ctx)?;
                frame_introduced.insert(name_str.clone());
                bindings.push((name_str, func_expr, None));
            }
            _ => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "only assignments and function definitions are supported as \
                     non-terminal statements in for-loop bodies",
                ));
            }
        }
    }

    let terminal =
        lower_for_body_terminal(last, defer_name, mutation_scope, &frame_introduced, ctx)?;

    // Fold let-bindings around the terminal from outermost to innermost.
    Ok(bindings
        .into_iter()
        .rev()
        .fold(terminal, |body, (name, val, ann)| match ann {
            Some(a) => Expr::let_bind_annotated(name, val, body, a),
            None => Expr::let_bind(name, val, body),
        }))
}

/// Lower the terminal (last) statement of a for-loop body.
///
/// Valid terminals:
/// - `yield e` — `Feed(defer_name, lower(e))` (requires `defer_name` to be set)
/// - `r << e` — `Feed("r", lower(e))`
/// - `if cond: body` (no else) — `Case` with `Unit` fallthrough
/// - `for j in ys: body` — nested `Compose([ys, Lambda(j, body)])`
///
/// `mutation_scope` and `frame_introduced` carry the same semantics as in
/// [`lower_for_body_stmts`]; they are threaded through for recursive calls.
fn lower_for_body_terminal(
    stmt: &Spanned<ChlStmt>,
    defer_name: Option<&str>,
    mutation_scope: &HashSet<String>,
    frame_introduced: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    match &stmt.node {
        ChlStmt::Expr(value) => match &value.node {
            ChlExpr::Yield(y) => {
                let name = defer_name.ok_or_else(|| {
                    LoweringError::unsupported(
                        stmt.span,
                        "yield outside a generator for-loop context",
                    )
                })?;
                Ok(Expr::feed(name.to_string(), lower_expr(y, ctx)?))
            }
            // `r << e` — direct feed into a named defer handle.
            // Note: when inside a yield-bearing generator (defer_name is Some),
            // `r` is not validated to equal defer_name; a mismatch would
            // type-check via inference but could produce confusing behaviour.
            // A future improvement could add a lowering-time error here.
            ChlExpr::Feed { target, value } => lower_feed(target, value, ctx),
            _ => Err(LoweringError::unsupported(
                value.span,
                "for-loop body must end in a yield, `<<` feed, nested for, \
                 or if-guard",
            )),
        },
        ChlStmt::If {
            branches,
            else_body,
        } => {
            if else_body.is_some() {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "if/else inside generator for-loop body is not supported; \
                     use a plain if-guard (no else branch)",
                ));
            }
            if branches.len() != 1 {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "if/elif inside generator for-loop body is not supported; \
                     use a plain if-guard (no elif/else branches)",
                ));
            }
            let branch = &branches[0];
            let cond = lower_expr(&branch.cond, ctx)?;
            // Same frame: pass through mutation_scope and frame_introduced
            // unchanged so that the iter_var remains shadowable inside the guard.
            let true_arm = lower_for_body_stmts(
                &branch.body,
                defer_name,
                mutation_scope,
                frame_introduced.clone(),
                ctx,
            )?;
            Ok(Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: vec![
                    Branch {
                        pattern: None,
                        guard: cond,
                        body: true_arm,
                    },
                    Branch {
                        pattern: None,
                        guard: Expr::lit(Lit::Bool(true)),
                        body: Expr::lit(Lit::Unit),
                    },
                ],
            }))
        }
        ChlStmt::For { target, iter, body } => {
            let inner_var = extract_name_target(target, "for-loop target")?;
            let inner_source = lower_expr(iter, ctx)?;
            // New frame: the outer frame's names (including iter_var) move into
            // mutation_scope so that the inner body cannot mutate them.
            let mut inner_mutation_scope = mutation_scope.clone();
            inner_mutation_scope.extend(frame_introduced.iter().cloned());
            let inner_frame = HashSet::from([inner_var.clone()]);
            let inner_body =
                lower_for_body_stmts(body, defer_name, &inner_mutation_scope, inner_frame, ctx)?;
            Ok(Expr::for_loop(inner_var, inner_source, inner_body))
        }
        _ => Err(LoweringError::unsupported(
            stmt.span,
            "for-loop body must end in a yield, `<<` feed, nested for, or if-guard",
        )),
    }
}

// ---------------------------------------------------------------------------
// Mutation loop lowering — `Loop` CCL nodes
// ---------------------------------------------------------------------------

/// If `stmt` is an assignment to a simple name that *could* be a mutation
/// of an existing binding, return that name.
///
/// `Assign` and `AugAssign` to a bare name qualify.  `<<=` is a
/// [`ChlStmt::Define`] (deferred-collection define, not a mutation) and is
/// rejected here automatically because it isn't an `Assign` or `AugAssign`.
fn mutation_target_name(stmt: &Spanned<ChlStmt>) -> Option<&str> {
    match &stmt.node {
        ChlStmt::Assign { target, .. } => name_target_as_name(target),
        ChlStmt::AugAssign { target, .. } => name_target_as_name(target),
        _ => None,
    }
}

/// Scan a for-loop body for assignments that mutate names already
/// bound in `mutation_scope`.  Returns every such name in first-mention
/// order, deduplicated, so the loop can be lowered to a
/// [`TypedExprNode::Loop`] whose `params` cover *all* loop-carried
/// accumulators.
///
/// Used by [`lower_middle_stmt`] both as a predicate ("is this for-loop a
/// mutation accumulator loop?" — non-empty result) and as the canonical
/// param list for [`lower_mutation_loop`].  The body's own sequential
/// walk in [`lower_mutation_loop_body`] handles every individual
/// mutation; this just decides which names are loop-carried.
///
/// `o <<= x` is a [`ChlStmt::Define`] (deferred-collection define), not a
/// mutation — [`mutation_target_name`] filters those out.
pub(super) fn find_mutation_loop_vars(
    body: &[Spanned<ChlStmt>],
    mutation_scope: &HashSet<String>,
) -> Vec<String> {
    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    for stmt in body {
        if let Some(name) = mutation_target_name(stmt)
            && mutation_scope.contains(name)
            && seen.insert(name.to_string())
        {
            vars.push(name.to_string());
        }
    }
    vars
}

/// Recursively search `stmts` for any assignment that mutates a name
/// in `mutation_scope`, descending into the bodies of nested `if` /
/// `for` statements.  Returns the first such name found.
///
/// Used by [`lower_middle_stmt`] to distinguish "this for-body has no
/// supported mutation pattern" from "this for-body has a mutation
/// pattern we don't yet support (nested inside control flow)", so the
/// latter can produce a targeted error rather than the generic
/// generator-for fallback's "must end in yield" message.
pub(super) fn find_nested_mutation_var(
    stmts: &[Spanned<ChlStmt>],
    mutation_scope: &HashSet<String>,
) -> Option<String> {
    for stmt in stmts {
        if let Some(name) = mutation_target_name(stmt)
            && mutation_scope.contains(name)
        {
            return Some(name.to_string());
        }
        match &stmt.node {
            ChlStmt::If {
                branches,
                else_body,
            } => {
                for branch in branches {
                    if let Some(n) = find_nested_mutation_var(&branch.body, mutation_scope) {
                        return Some(n);
                    }
                }
                if let Some(else_body) = else_body
                    && let Some(n) = find_nested_mutation_var(else_body, mutation_scope)
                {
                    return Some(n);
                }
            }
            ChlStmt::For { body, .. } => {
                if let Some(n) = find_nested_mutation_var(body, mutation_scope) {
                    return Some(n);
                }
            }
            _ => {}
        }
    }
    None
}

/// Dispatch wrapper for [`lower_mutation_loop`] that allocates a generator
/// defer when the body contains a `yield`.
///
/// A mutation loop body may also contain `yield e` statements (the
/// mutability design notes' §4b `running_totals` shape: `total += item; yield total`).
/// In that case the surrounding generator-function context needs a fresh
/// defer to collect the yielded values, and the mutation loop's body
/// records `yield e` as a feed into that defer alongside any explicit
/// `<<` feeds.
///
/// When yield is present this builds:
/// ```text
/// let __result = Defer in
///   <lower_mutation_loop result, with yield-defer wired in as one more tap>
/// ```
/// — the same wrapping the plain generator-for path uses, except the
/// surrounding continuation flows through unchanged (the `__result`
/// defer is bound but never directly referenced in user-visible code;
/// [`crate::ccl::desugar_defers`] substitutes the collected feed values
/// and `simplify` drops any unused binding).
///
/// When yield is absent this is just [`lower_mutation_loop`].
pub(super) fn lower_generator_or_mutation_loop(
    target: &Spanned<AssignTarget>,
    iter: &Spanned<ChlExpr>,
    body_stmts: &[Spanned<ChlStmt>],
    acc_names: &[String],
    continuation: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if for_body_has_yield(body_stmts) {
        let yield_defer = ctx.fresh_result_name();
        let inner = lower_mutation_loop(
            target,
            iter,
            body_stmts,
            acc_names,
            continuation,
            Some(&yield_defer),
            ctx,
        )?;
        Ok(Expr::let_bind(
            yield_defer,
            Expr::new(TypedExprNode::Defer),
            inner,
        ))
    } else {
        lower_mutation_loop(target, iter, body_stmts, acc_names, continuation, None, ctx)
    }
}

/// Lower a mutation accumulation for-loop to a [`TypedExprNode::Loop`]
/// node, threading the surrounding `continuation` through the structure.
///
/// The Loop's body lambda emits raw `Feed(d, V)` nodes inline at the
/// positions where each `<<` appears in the source body.  Each feed's
/// `V` is captured with its prefix let-chain (via
/// [`lower_mutation_loop_body`]) so the value is self-contained and can
/// be hoisted to the body's terminal Record by
/// [`crate::ccl::desugar_defers`] without disturbing scope.
///
/// The lifted shape (single-accumulator example shown — for multi-var
/// each post-loop `let acc_i = …` additionally projects `Proj(i)` off
/// `.step`):
///
/// ```text
/// let acc_stream = Loop {
///   loop_body: λp → let acc = p.0 in let i = p.1 in
///                   <body-chain>
///                   ExprStmt(Feed(defer_0, <feed_value_0>),
///                   ExprStmt(Feed(defer_1, <feed_value_1>),
///                     Record({step: <full chain> Var(acc)}))),
/// } in
/// let acc_name = acc_stream ▷ Proj("step") ▷ Last in
///   continuation
/// ```
///
/// `desugar_defers` then absorbs each `Feed(defer_k, V)` into a
/// `to_<defer_k>` field on the body's terminal Record and exposes
/// `acc_stream ▷ Proj("to_<defer_k>")` to the enclosing defer-bind's
/// channelization.
///
/// Each feed expression captures its own let-chain prefix in the body,
/// so feeds before / between / after the mutation see the SSA-style
/// scope the Python source intended: pre-mutation feeds capture the
/// empty chain (their `acc` refers to `p.0`, the previous-iteration
/// value), and post-mutation feeds capture the chain up to and
/// including the mutation.  The Record's `step` field captures the
/// full chain ending in `Var(acc_name)` (or a tuple of all accumulators
/// for multi-var).
///
/// `yield_defer` — if `Some(name)`, `yield e` statements in the body
/// are accepted and lowered as feeds to that defer (which `desugar_defers`
/// then absorbs into a `to_<defer>` field on the body Record alongside
/// any explicit `<<` feeds).  The caller is responsible for binding the
/// defer outside this call; [`lower_generator_or_mutation_loop`] is
/// the usual entry point that arranges that.  If `None`, a `yield`
/// in the body is rejected.
fn lower_mutation_loop(
    target: &Spanned<AssignTarget>,
    iter: &Spanned<ChlExpr>,
    body_stmts: &[Spanned<ChlStmt>],
    acc_names: &[String],
    continuation: Expr,
    yield_defer: Option<&str>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    assert!(
        !acc_names.is_empty(),
        "lower_mutation_loop: empty acc_names"
    );
    let iter_var_name = extract_name_target(target, "for-loop target")?;
    let source = lower_expr(iter, ctx)?;
    let MutationLoopBody { step, feeds } =
        lower_mutation_loop_body(body_stmts, acc_names, yield_defer, ctx)?;

    // Build the body lambda's outer let-chain `let acc_i = p.i in … let
    // iter_var = p.n in <inner>` for an (n+1)-tuple param `p` whose
    // components are the n previous-iteration accumulator values followed
    // by the source element.
    let build_body_lambda = |inner: Expr, ctx: &mut LoweringContext| -> Expr {
        let p_name = ctx.fresh_tuple_arg();
        let item_idx = acc_names.len();
        let mut wrapped = Expr::let_bind(
            &iter_var_name,
            Expr::apply(Expr::var(&p_name), Expr::proj_index(item_idx)),
            inner,
        );
        for (i, name) in acc_names.iter().enumerate().rev() {
            wrapped = Expr::let_bind(
                name.clone(),
                Expr::apply(Expr::var(&p_name), Expr::proj_index(i)),
                wrapped,
            );
        }
        Expr::lambda(&p_name, Type::Hole, wrapped)
    };

    // Initial-accumulator values, one per loop-carried variable, in
    // declaration order.  Evaluated outside the loop's param scope.
    let init_args: Vec<Expr> = acc_names.iter().map(|n| Expr::var(n.clone())).collect();

    // Build the body's terminal: a Record({step: recurrence}).  Feeds are
    // prepended as `ExprStmt(Feed(defer_k, value_k), …)` wrappers in
    // *source order*; desugar_defers will absorb them into the Record as
    // `to_<defer_k>` fields.
    let record_body = Expr::new(TypedExprNode::Record(vec![("step".to_string(), step)]));
    let mut inner = record_body;
    for (defer_name, feed_value) in feeds.into_iter().rev() {
        inner = Expr::expr_stmt(Expr::feed(defer_name, feed_value), inner);
    }

    let step_lambda = build_body_lambda(inner, ctx);
    let loop_expr = Expr::loop_node(
        acc_names.iter().map(Name::from).collect(),
        init_args,
        source,
        step_lambda,
    );

    // Wrap the continuation in:
    //   let acc_stream = Loop {…} in
    //   let acc_i = acc_stream ▷ Proj("step") [▷ Proj(i)] ▷ Last in …
    //     continuation
    //
    // For a single accumulator the inner `▷ Proj(i)` is omitted —
    // `.step` is already the scalar value.  For multi-var, `.step`
    // carries a `Tuple` and each accumulator is reached by an
    // additional positional projection.
    let acc_stream_name = ctx.fresh_acc_stream_name();
    let mut wrapped = continuation;
    let multi_acc = acc_names.len() > 1;
    for (i, name) in acc_names.iter().enumerate().rev() {
        let mut chain = vec![Expr::var(&acc_stream_name), Expr::proj_field("step")];
        if multi_acc {
            chain.push(Expr::proj_index(i));
        }
        // `LastOrDefault(stream, default)` extracts the body's final
        // step value, or returns `default` when the source domain is
        // empty (the loop body ran zero times).  We pass the pre-loop
        // value of the accumulator (`Var(name)`, which resolves to the
        // outer-scope binding because the let we're building below
        // shadows it only inside `wrapped`) as the default.
        let scalar = Expr::apply(
            Expr::tuple(vec![Expr::compose(chain), Expr::var(name.clone())]),
            Expr::builtin(Builtin::LastOrDefault),
        );
        wrapped = Expr::let_bind(name.clone(), scalar, wrapped);
    }
    Ok(Expr::let_bind(acc_stream_name, loop_expr, wrapped))
}

/// Lower the body statements of a mutation accumulation loop to a single
/// step expression plus a list of feed snapshots.
///
/// The body is walked sequentially.  Each statement is classified:
/// - **Assignment** (mutation `x = …`, augmented mutation `x op= …`, or any
///   ordinary `y = …` let-binding) — appended to the running let-chain.
///   Mutations of `acc_name` shadow the existing `acc_name` binding via the
///   chain's lexical scoping; ordinary lets introduce fresh names.
/// - **Feed `o << e`** — snapshotted: a lambda body is built as the
///   *current* let-chain (every assignment seen so far in body order)
///   wrapped around the lowered `e`.  This captures the SSA-style scope
///   that `e` was written in: pre-mutation feeds see the Loop's
///   accumulator param directly (an empty / pre-mutation prefix chain),
///   in-between-mutation feeds see the chain up to that point, and
///   post-mutation feeds see the full chain.  The feeds list contains
///   one such snapshot per `<<`.
/// - **`yield e`** — equivalent to `<<` against a synthesised generator
///   defer.  When `yield_defer` is `Some(name)`, the yield is recorded
///   as a feed into that name using the same let-chain snapshotting
///   rules; when `None`, a `yield` is rejected.  This lets a generator
///   with loop-carried state (the mutability design notes' §4b
///   `running_totals`) reuse the same `Loop` lowering as a plain
///   mutation loop — the yield's defer is collected by
///   `desugar_defers` as another `to_<defer>` field on the body Record.
///
/// The Loop's `loop_body` step expression is the full let-chain ending in
/// `Var(acc_name)` — the final accumulator value after every mutation in
/// the body has been applied.
///
/// Feeds anywhere in the body are supported.  [`lower_mutation_loop`]
/// wraps each captured lambda body in `λp → let acc_name = p ▷ Proj(0)
/// in let iter_var = p ▷ Proj(1) in <body>`, where `p` is the
/// per-iteration tuple `(prev_acc, item)`.  The outer let-bindings
/// shadow the per-iteration values into the names the body's let-chain
/// expects, so pre-mutation references to `acc_name` resolve to `p.0`
/// (the previous-iteration accumulator — the value `Recurse` emits at
/// the corresponding domain position), and post-mutation references
/// resolve to the most recent mutation binding in the chain.
fn lower_mutation_loop_body(
    stmts: &[Spanned<ChlStmt>],
    acc_names: &[String],
    yield_defer: Option<&str>,
    ctx: &mut LoweringContext,
) -> Result<MutationLoopBody, LoweringError> {
    let mut let_chain: Vec<(String, Expr)> = Vec::new();
    let mut feeds: Vec<(String, Expr)> = Vec::new();

    let wrap_chain = |chain: &[(String, Expr)], tail: Expr| {
        chain.iter().rev().fold(tail, |body, (name, val)| {
            Expr::let_bind(name.clone(), val.clone(), body)
        })
    };

    for stmt in stmts {
        match &stmt.node {
            // Simple `name = value` — either a mutation of one of the
            // loop-carried accumulators (when `name` is in `acc_names`)
            // or an ordinary let-binding.  Both get appended to the chain
            // in body order; the chain's lexical scoping does the rest.
            ChlStmt::Assign { target, value } => {
                let name = extract_name_target(target, "assignment")?;
                let val = lower_expr(value, ctx)?;
                let_chain.push((name, val));
            }
            // Augmented assignment `x op= value` — desugars to `x = x op value`.
            // CHL's `AugOp` doesn't include `<<` (that's its own statement,
            // `ChlStmt::Define`, which falls through to the catch-all below).
            ChlStmt::AugAssign { target, op, value } => {
                let name = extract_name_target(target, "augmented assignment")?;
                let val = lower_aug_binop(&name, *op, value, ctx)?;
                let_chain.push((name, val));
            }
            // `o << value` — captured as a feed.  Snapshot the current
            // let-chain and wrap the lowered feed value in it.
            ChlStmt::Expr(value)
                if let ChlExpr::Feed {
                    target: feed_target,
                    value: feed_value,
                } = &value.node =>
            {
                let defer_name = match &feed_target.node {
                    ChlExpr::Name(id) => id.as_str().to_string(),
                    _ => {
                        return Err(LoweringError::unsupported(
                            feed_target.span,
                            "feed target: only simple name targets are supported",
                        ));
                    }
                };
                let lowered = lower_expr(feed_value, ctx)?;
                let wrapped = wrap_chain(&let_chain, lowered);
                feeds.push((defer_name, wrapped));
            }
            // `yield value` — treated as a feed into the surrounding
            // generator's synthesised defer.  Same let-chain snapshotting
            // as `<<` so that pre/in/post-mutation yields see the right
            // SSA-style scope.
            ChlStmt::Expr(value) if let ChlExpr::Yield(y) = &value.node => {
                let defer_name = yield_defer.ok_or_else(|| {
                    LoweringError::unsupported(
                        value.span,
                        "yield outside a generator for-loop context",
                    )
                })?;
                let feed_value = lower_expr(y, ctx)?;
                let wrapped = wrap_chain(&let_chain, feed_value);
                feeds.push((defer_name.to_string(), wrapped));
            }
            _ => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "only assignments (`x = …`, `x op= …`), `<<` feeds, and \
                     `yield` are supported inside a mutation loop body",
                ));
            }
        }
    }

    // The cycle's step expression: the full let-chain wrapped around the
    // step terminator.  For a single accumulator the terminator is just
    // `Var(acc_name)`; for multiple it is a `Tuple([Var(acc_0), …])` so
    // op-conversion can expose every loop-carried value through one Join
    // and the surrounding lowering picks each off via positional `Proj ▷
    // Last`.
    let step_terminator = if acc_names.len() == 1 {
        Expr::var(acc_names[0].clone())
    } else {
        Expr::tuple(acc_names.iter().map(|n| Expr::var(n.clone())).collect())
    };
    let step = wrap_chain(&let_chain, step_terminator);

    Ok(MutationLoopBody { step, feeds })
}

/// The split of a mutation loop body: the per-iteration step expression
/// (the full assignment let-chain, ending in `Var(acc_name)` — the final
/// accumulator value), and a list of feed snapshots taken at each `<<`
/// statement in body order.  See [`lower_mutation_loop_body`] for the
/// per-statement rules.
struct MutationLoopBody {
    /// The Join's per-iteration step expression — the entire body's
    /// let-chain (every `x = …`, `x op= …`, and ordinary `y = …`) ending
    /// in `Var(acc_name)`.  The Join's `loop_body` codomain equals the
    /// accumulator type.
    step: Expr,
    /// `(defer_name, wrapped_feed_value)` for each `<<` statement in the
    /// body.  Each `wrapped_feed_value` is the lowered RHS wrapped in the
    /// let-chain up to (but not including) the feed itself — so its
    /// references to `acc_name` resolve in the same SSA-style scope the
    /// original Python source intended.
    feeds: Vec<(String, Expr)>,
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;

    // -----------------------------------------------------------------------
    // Generator function tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Simple generator: map pattern.
    #[case(
        "\
def doubles(xs):
    for x in xs:
        yield x * 2
doubles",
        "\
let doubles : (_ ⇒ _) = λ xs → let __result_0 = defer
in xs ≫ (λ x → feed(__result_0, x * 2)); __result_0
in doubles"
    )]
    // Multi-param generator: captures outer parameter. Uncurried params
    // appear as projections of the synthetic `__arg_tuple_0`.
    #[case(
        "\
def add_to(xs, n):
    for x in xs:
        yield x + n
add_to",
        "\
let add_to : (_ ⇒ _) = λ __arg_tuple_1 → let __result_0 = defer
in __arg_tuple_1.0 ≫ (λ x → feed(__result_0, x + __arg_tuple_1.1)); __result_0
in add_to"
    )]
    // Generator with if-guard: guard becomes a Case in the For body.
    #[case(
        "\
def positives(xs):
    for x in xs:
        if x > 0:
            yield x
positives",
        "\
let positives : (_ ⇒ _) = λ xs → let __result_0 = defer
in xs ≫ (λ x → { x > 0 → feed(__result_0, x); true → unit }); __result_0
in positives"
    )]
    // Nested for-loops: inner iter independent of outer loop variable.
    #[case(
        "\
def cross(xs, ys):
    for x in xs:
        for y in ys:
            yield x + y
cross",
        "\
let cross : (_ ⇒ _) = λ __arg_tuple_1 → let __result_0 = defer
in __arg_tuple_1.0 ≫ (λ x → __arg_tuple_1.1 ≫ (λ y → feed(__result_0, x + y))); __result_0
in cross"
    )]
    // Three-level nested for.
    #[case(
        "\
def triple(xs, ys, zs):
    for x in xs:
        for y in ys:
            for z in zs:
                yield x + y + z
triple",
        "\
let triple : (_ ⇒ _) = λ __arg_tuple_1 → let __result_0 = defer
in __arg_tuple_1.0 ≫ (λ x → __arg_tuple_1.1 ≫ (λ y → __arg_tuple_1.2 ≫ (λ z → feed(__result_0, x + y + z)))); __result_0
in triple"
    )]
    // Guard before inner for: Case wraps the nested For node.
    #[case(
        "\
def cross_filtered(xs, ys):
    for x in xs:
        if x > 0:
            for y in ys:
                yield y
cross_filtered",
        "\
let cross_filtered : (_ ⇒ _) = λ __arg_tuple_1 → let __result_0 = defer
in __arg_tuple_1.0 ≫ (λ x → { x > 0 → __arg_tuple_1.1 ≫ (λ y → feed(__result_0, y)); true → unit }); __result_0
in cross_filtered"
    )]
    // Let-binding in generator body: y is a fresh local per iteration.
    #[case(
        "\
def with_let(xs):
    for x in xs:
        y = x + 1
        yield y * 2
with_let",
        "\
let with_let : (_ ⇒ _) = λ xs → let __result_0 = defer
in xs ≫ (λ x → let y = x + 1
in feed(__result_0, y * 2)); __result_0
in with_let"
    )]
    // Iter-var shadowing: x = x + 1 re-binds x as a let inside the For body.
    #[case(
        "\
def shadow(xs):
    for x in xs:
        x = x + 1
        yield x
shadow",
        "\
let shadow : (_ ⇒ _) = λ xs → let __result_0 = defer
in xs ≫ (λ x → let x = x + 1
in feed(__result_0, x)); __result_0
in shadow"
    )]
    // Dependent inner iter: inner source references the outer iter var.
    #[case(
        "\
def dep(xss):
    for xs in xss:
        for x in xs:
            yield x
dep",
        "\
let dep : (_ ⇒ _) = λ xss → let __result_0 = defer
in xss ≫ (λ xs → xs ≫ (λ x → feed(__result_0, x))); __result_0
in dep"
    )]
    // Let inside an if-guard body.
    #[case(
        "\
def guarded_let(xs):
    for x in xs:
        if x > 0:
            y = x * 2
            yield y
guarded_let",
        "\
let guarded_let : (_ ⇒ _) = λ xs → let __result_0 = defer
in xs ≫ (λ x → { x > 0 → let y = x * 2
in feed(__result_0, y); true → unit }); __result_0
in guarded_let"
    )]
    fn test_lower_generator_fn(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Generator function negative / mutation-loop tests
    // -----------------------------------------------------------------------

    /// Augmented assignment to iter var (shadowing) in a generator for-loop.
    /// This is NOT a yield — the for-loop body ends in `bad` (the bare var),
    /// which is not a yield, so this should still be rejected.
    #[test]
    fn test_generator_aug_assign_no_yield_rejected() {
        let code = "\
def bad(xs):
    for x in xs:
        x += 1
bad";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        assert!(matches!(err, LoweringError::Unsupported { .. }));
    }

    /// Mutability design notes, §4b — a generator with loop-carried state lowers to a
    /// `Loop` whose body contains a raw `Feed(__result_*, …)` followed by
    /// a `(step: …)` Record, with the surrounding `let __result = defer`
    /// collecting the yields.  [`crate::ccl::desugar_defers`] absorbs
    /// the raw `Feed` into a `to_<defer>` field on the same Record
    /// before inference.
    #[test]
    fn test_generator_with_loop_carried_mutation_lowers() {
        let code = "\
def running_totals(items):
    total = 0
    for item in items:
        total += item
        yield total
running_totals";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("running_totals should lower as a mutation loop with a yield-tap");
        let s = symbolic(&ccl);
        assert!(
            s.contains("__result_") && s.contains("defer"),
            "should bind a defer for the generator's yields: {s}"
        );
        assert!(
            s.contains("loop total") || s.contains("loop (total"),
            "should produce a Loop carrying `total`: {s}"
        );
        assert!(
            s.contains("step: "),
            "Loop body Record should expose `step`: {s}"
        );
        assert!(
            s.contains("feed(__result_"),
            "should emit a raw `Feed(__result_*, …)` inside the loop body \
             (desugar_defers turns this into a `to_<defer>` Record field): {s}"
        );
    }

    /// Generator with a directly-mutated argument: same shape as
    /// `running_totals` but the accumulator is a function parameter
    /// rather than a pre-loop local.  Verifies that the `acc_names`
    /// scan walks the function-parameter scope, not just pre-loop lets.
    #[test]
    fn test_generator_mutation_of_arg_lowers() {
        let code = "\
def bad(xs, n):
    for x in xs:
        n = n + 1
        yield n
bad";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("generator mutating an argument should lower as a mutation loop");
        let s = symbolic(&ccl);
        assert!(
            s.contains("loop n") && s.contains("feed(__result_"),
            "should be a `Loop` over `n` whose body emits a yield-feed: {s}"
        );
    }

    /// Mutation of an outer-frame variable from inside a *nested* generator
    /// for-loop is still rejected.  The outer for-body has a yield (via the
    /// inner loop), so the mutation-loop path doesn't fire; the generator
    /// path then sees `y = y + z` as an assignment to a name bound outside
    /// the inner for's own frame and rejects it.
    #[test]
    fn test_generator_mutation_across_nested_for_rejected() {
        let code = "\
def bad(xs, ys):
    for x in xs:
        y = 0
        for z in ys:
            y = y + z
            yield y
bad";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message: msg, .. } = &err;
        assert!(
            msg.contains("mutation") && msg.contains("`y`"),
            "error should mention mutation of `y`: {msg}"
        );
    }

    /// Mutation of an outer-scope variable nested inside an `if` in a
    /// for-loop body is rejected with a targeted message that names the
    /// variable and points at the nesting, rather than falling through
    /// to the generator-for fallback's generic "must end in yield".
    #[test]
    fn test_mutation_nested_in_if_rejected() {
        let code = "\
x = 0
for i in [1, 2]:
    if i > 0:
        x = x + i
x";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message: msg, .. } = &err;
        assert!(
            msg.contains("nested") && msg.contains("`x`"),
            "error should call out nested mutation of `x`: {msg}"
        );
    }

    /// Same shape but mutation nested in an inner `for` rather than `if`.
    #[test]
    fn test_mutation_nested_in_for_rejected() {
        let code = "\
x = 0
for i in [1, 2]:
    for j in [10, 20]:
        x = x + i + j
x";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message: msg, .. } = &err;
        assert!(
            msg.contains("nested") && msg.contains("`x`"),
            "error should call out nested mutation of `x`: {msg}"
        );
    }

    /// `if/else` inside a generator for-loop body is rejected.
    #[test]
    fn test_generator_if_else_in_body_rejected() {
        let code = "\
def bad(xs):
    for x in xs:
        if x > 0:
            yield x
        else:
            yield 0
bad";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        match &err {
            LoweringError::Unsupported { message: msg, .. } => {
                assert!(
                    msg.contains("if/else inside generator"),
                    "error should mention if/else in generator: {msg}"
                );
            }
        }
    }

    /// A for/yield loop preceded by assignments is supported: the preceding
    /// lets wrap the generator expression.
    #[test]
    fn test_generator_with_preloop_let() {
        let code = "\
def f(xs):
    a = 5
    for x in xs:
        yield x + a
f";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        let s = symbolic(&ccl);
        assert!(
            s.contains("let a = 5") && s.contains("x + a"),
            "should have pre-loop let and body referencing it: {s}"
        );
    }
}

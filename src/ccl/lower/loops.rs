//! `for`-loop lowering: side-effecting / generator (`yield`) loops lowering to
//! `For` nodes, and mutation-accumulation loops lowering to `Loop` nodes.

use std::collections::HashSet;

use super::*;
use crate::{
    ccl::{Branch, Expr, Lit, Type, TypedBinding, TypedExprNode},
    chl_parser::ast::{AssignTarget, Expr as ChlExpr, IfBranch, Spanned, Stmt as ChlStmt},
};

// ---------------------------------------------------------------------------
// For-loop lowering — For CCL node
// ---------------------------------------------------------------------------

/// Return `true` if any statement in `stmts` contains a `yield` expression
/// (checked recursively through `if` guards and nested `for` loops).
///
/// Does not recurse into `with`/`try` blocks — those are rejected later by
/// the "only assignments and function definitions" check in `lower_for_body_stmts`.
pub(super) fn for_body_has_yield(stmts: &[Spanned<ChlStmt>]) -> bool {
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

/// Return `true` if any statement in `stmts` contains a `<<` feed expression
/// (checked recursively through `if` guards and nested `for` loops), mirroring
/// [`for_body_has_yield`].
///
/// Used to keep a feed-bearing side-effect loop on the `Compose`/`channelize`
/// path: only a loop with neither a feed nor a yield (a bare-effect body such
/// as `for x: bump(cnt)`, whose only possible effect is a hidden mutable write
/// inside a call) is routed to the direct-mirror `For` marker.
pub(super) fn for_body_has_feed(stmts: &[Spanned<ChlStmt>]) -> bool {
    stmts.iter().any(stmt_has_feed)
}

fn stmt_has_feed(stmt: &Spanned<ChlStmt>) -> bool {
    match &stmt.node {
        ChlStmt::Expr(value) => matches!(&value.node, ChlExpr::Feed { .. }),
        ChlStmt::If {
            branches,
            else_body,
        } => {
            branches.iter().any(|b| for_body_has_feed(&b.body))
                || else_body.as_deref().is_some_and(for_body_has_feed)
        }
        ChlStmt::For { body, .. } => for_body_has_feed(body),
        _ => false,
    }
}

/// Whether the loop body contains a top-level `with begin():` transaction block.
///
/// A routing predicate, like [`for_body_has_yield`]/[`for_body_has_feed`]: a
/// for-loop whose body has a `with` block (with or without sibling induction
/// writes/feeds) takes the direct-mirror `For` path, where the block lowers to a
/// [`TypedExprNode::Begin`] marker `transact_phase` later strips. (A `with`
/// nested under an `if`/inner `for` is not this shape; the body walker rejects
/// it.)
pub(super) fn for_body_has_with(stmts: &[Spanned<ChlStmt>]) -> bool {
    stmts.iter().any(|s| matches!(s.node, ChlStmt::With { .. }))
}

/// Return `true` if the loop body's **terminal** statement is a bare *effect*
/// expression — a call (or other expression) that is neither a `yield` nor a
/// `<<` feed, e.g. `for x in xs: bump(cnt)`. Such a terminal is a hidden-writer
/// / side-effect statement (a pass-by-reference call may write an outer mutable variable,
/// invisible pre-inference), which [`lower_direct_mirror_loop`] carries. A
/// terminal that reassigns the loop variable (`x += 1`) or a non-mutable is *not*
/// a bare effect and stays rejected by the generator path. Gates the
/// final-statement hidden-writer fallback in [`super::stmts::lower_final_stmt`];
/// mirrors the non-yield/non-feed `ChlStmt::Expr` arm of `lower_for_body_terminal`.
pub(super) fn for_body_terminal_is_bare_effect(stmts: &[Spanned<ChlStmt>]) -> bool {
    matches!(
        stmts.last().map(|s| &s.node),
        Some(ChlStmt::Expr(value))
            if !matches!(&value.node, ChlExpr::Yield(_) | ChlExpr::Feed { .. })
    )
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
    for_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let iter_var = extract_name_target(target, "for-loop target")?;

    if for_body_has_yield(body) {
        // A generator with loop-carried state (the mutability design notes' §4b) — yield
        // alongside mutation of an outer-scope variable — routes through the
        // direct-mirror `For`/`MutWrite`/`Feed` path; the unified letrec
        // phase (src/ccl/design/mutability.md) builds the recurrence and
        // hoists the yield-feed to an ordinary feed of the loop's history.
        // Detect loop-carried writes (`:=` / `+=` to an outer-scope name) so we
        // can dispatch on them; mutability of each write is checked
        // post-inference, not here.
        let acc_names = find_mutation_loop_vars(body, outer_bindings);
        if !acc_names.is_empty() {
            // The generator's defer is bound around the loop and used as the
            // continuation — same shape as the plain yield-only path below.
            let defer_name = ctx.fresh_result_name();
            let continuation = ctx.tag_machinery(
                Expr::var(defer_name.clone()),
                for_span,
                "lower.generator_defer",
            );
            let site = ForSite {
                target,
                iter,
                body_stmts: body,
                acc_names: &acc_names,
                outer_bindings,
                for_span,
            };
            let inner = lower_direct_mirror_loop(&site, continuation, Some(&defer_name), ctx)?;
            return Ok(generator_defer_binding(defer_name, inner, for_span, ctx));
        }

        let source = lower_expr(iter, ctx)?;
        let frame_introduced = HashSet::from([iter_var.clone()]);
        // Plain yield without loop-carried mutation: desugar yield → defer + feed.
        let defer_name = ctx.fresh_result_name();
        // The loop target shadows a like-named transactional mutable variable in the body.
        let for_body = ctx.with_shadowed([iter_var.clone()], |ctx| {
            lower_for_body_stmts(
                body,
                Some(&defer_name),
                outer_bindings,
                frame_introduced,
                ctx,
            )
        })?;
        let for_node = tagged_for_loop(iter_var, source, for_body, for_span, ctx);
        let handle = ctx.tag_machinery(
            Expr::var(defer_name.clone()),
            for_span,
            "lower.generator_defer",
        );
        let seq = ctx.tag_machinery(
            Expr::expr_stmt(for_node, handle),
            for_span,
            "lower.generator_defer",
        );
        Ok(generator_defer_binding(defer_name, seq, for_span, ctx))
    } else {
        let source = lower_expr(iter, ctx)?;
        let frame_introduced = HashSet::from([iter_var.clone()]);
        // The loop target shadows a like-named transactional mutable variable in the body.
        let for_body = ctx.with_shadowed([iter_var.clone()], |ctx| {
            lower_for_body_stmts(body, None, outer_bindings, frame_introduced, ctx)
        })?;
        Ok(tagged_for_loop(iter_var, source, for_body, for_span, ctx))
    }
}

/// Build the `Compose([source, Lambda(iter_var, body)])` loop encoding (the
/// shape of [`Expr::for_loop`]), tagging **both** minted nodes — the `Compose`
/// and the interior `Lambda` — as the for statement's direct image.
///
/// Stamped `Data`: a loop over a collection *is* that collection mapped, and
/// this is the site that knows it. Leaving the function unstamped would hand the
/// question to whatever consumed the chain, which is how a loop ends up reading
/// as a capability.
fn tagged_for_loop(
    iter_var: String,
    source: Expr,
    body: Expr,
    for_span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let lambda = ctx.tag_image(Expr::lambda(iter_var, Type::Hole, body), for_span);
    ctx.tag_image(
        Expr::compose(vec![source, lambda])
            .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
        for_span,
    )
}

/// Wrap a generator's lowered loop in its synthesized defer binding,
/// `let <defer_name> = Defer in <inner>` — manufactured wiring of the
/// yield-desugaring rule.
fn generator_defer_binding(
    defer_name: String,
    inner: Expr,
    for_span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let defer = ctx.tag_machinery(
        Expr::new(TypedExprNode::Defer),
        for_span,
        "lower.generator_defer",
    );
    ctx.tag_machinery(
        Expr::let_bind(defer_name, defer, inner),
        for_span,
        "lower.generator_defer",
    )
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
/// Rejection for a write to a name bound *outside* a for-loop body. Inside a
/// loop a plain `=` cannot carry state across iterations, and `=` is immutable
/// regardless — it would be a per-iteration shadow that silently discards each
/// update. To mutate a mutable variable, introduce it with `:=` before the loop and write
/// it with `:=` / `+=`.
pub(super) fn outer_binding_write_error(span: Span, name: &str) -> LoweringError {
    LoweringError::unsupported(
        span,
        format!(
            "assignment to `{name}` is mutation: `{name}` is bound outside the \
             for-loop body (function argument or pre-loop binding). `=` binds \
             immutably; to mutate a mutable variable, introduce it with `:=` before the \
             loop and write it with `{name} := …` or `{name} += …`"
        ),
    )
}

/// Rejection for a **mutable variable introduced inside a for-loop body**, at any
/// spelling: `x := e`, `x: T := e`, or `x: Mut(V) = e`.
///
/// The mutable variable would have to be scoped to one iteration, and its sequencing
/// domain is the loop's own iteration extent — so the loop body would carry a
/// nested recurrence the unified phase has no domain for. Blocked at lowering
/// rather than misinterpreted: the alternative every spelling used to fall back
/// on is a per-iteration shadowing `let`, which silently discards each update at
/// the iteration boundary.
///
/// Uniform across spellings on purpose. Whether the introduction carries a type
/// annotation says nothing about whether it introduces a mutable variable, so gating on
/// the annotation accepted `x := e` and rejected `x: Mut(V) := e` for the same
/// construct.
fn in_loop_mut_var_error(span: Span, name: &str) -> LoweringError {
    LoweringError::unsupported(
        span,
        format!(
            "`{name}` is a mutable variable introduced inside a for-loop body, \
             which is not supported: declare it before the loop (`{name} := …`) \
             so its updates carry across iterations, or bind a per-iteration \
             value immutably with `{name} = …`"
        ),
    )
}

/// Rejection for `x op= e` inside a for-loop body where `x` is not a mutable
/// variable declared before the loop.
///
/// `op=` is a mutable write and the spec says so — *a `+=` to an immutable binding is
/// a type error, not a silent rebind*. The fallback this replaces was a per-iteration
/// shadowing `let`, which is wrong twice over: the update is discarded at the
/// iteration boundary, and because `op=` reads the old value, each iteration reads the
/// binding's *initial* value rather than the running one.
fn in_loop_aug_assign_error(span: Span, name: &str) -> LoweringError {
    LoweringError::unsupported(
        span,
        format!(
            "`{name}` is not a mutable variable, so `{name} op= …` inside a for-loop \
             body cannot accumulate into it: declare it before the loop with \
             `{name} := …` so its updates carry across iterations, or compute a \
             per-iteration value with `{name} = …`"
        ),
    )
}

/// The names a for-loop body's statement sits under: those bound above the loop
/// and those the frame has bound. A block right-hand side is lowered in this
/// scope, which decides whether a `:=` inside it writes a variable from outside
/// the block or introduces one of its own
/// ([`lower_block_value`](super::stmts::lower_block_value)); a nested `for`
/// takes it as its own `mutation_scope`, since its body may not mutate the
/// frame either.
fn body_scope(
    mutation_scope: &HashSet<String>,
    frame_introduced: &HashSet<String>,
) -> HashSet<String> {
    mutation_scope.union(frame_introduced).cloned().collect()
}

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

    // Each binding carries its statement's span so the `Let` folded around the
    // terminal below can be tagged as that statement's direct image.
    let mut bindings: Vec<(String, Expr, Option<Type>, Span)> = Vec::new();

    for stmt in rest {
        match &stmt.node {
            ChlStmt::Assign { target, value } => {
                let name = extract_name_target(target, "assignment")?;
                if mutation_scope.contains(&name) {
                    return Err(outer_binding_write_error(stmt.span, &name));
                }
                let scope = body_scope(mutation_scope, &frame_introduced);
                let val = lower_assigned_value(value, &[], &scope, ctx)?;
                frame_introduced.insert(name.clone());
                bindings.push((name, val, None, stmt.span));
            }
            ChlStmt::AnnAssign {
                target,
                annotation,
                value,
            } => {
                let name = extract_name_target(target, "annotated assignment")?;
                if mutation_scope.contains(&name) {
                    return Err(outer_binding_write_error(stmt.span, &name));
                }
                if mut_annotation_parts(&annotation.ty, ctx).is_some() {
                    return Err(in_loop_mut_var_error(stmt.span, &name));
                }
                let ann = lower_type_annotation(annotation, ctx)?;
                let scope = body_scope(mutation_scope, &frame_introduced);
                let val = lower_assigned_value(value, &[], &scope, ctx)?;
                frame_introduced.insert(name.clone());
                bindings.push((name, val, Some(ann), stmt.span));
            }
            ChlStmt::AugAssign { target, .. } => {
                let name = extract_name_target(target, "augmented assignment")?;
                if mutation_scope.contains(&name) {
                    return Err(outer_binding_write_error(stmt.span, &name));
                }
                // `op=` is a mutable write, and nothing in this body is mutable: an
                // outer-scope target was rejected above, and everything `frame_introduced`
                // holds was bound immutably by `=` (or is the iteration variable).
                // Rebinding it per iteration is what the spec forbids by name — the
                // update is discarded at the boundary, and since `op=` reads the old
                // value, each iteration would read the *initial* one. This path has no
                // accumulators by construction: a loop with loop-carried writes routes
                // to `lower_direct_mirror_loop` instead.
                return Err(in_loop_aug_assign_error(stmt.span, &name));
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
                output,
                body: fn_body,
            } => {
                let name_str = name.as_str().to_string();
                if mutation_scope.contains(&name_str) {
                    return Err(outer_binding_write_error(stmt.span, &name_str));
                }
                let func_expr =
                    lower_function_body(stmt.span, params, output.as_ref(), fn_body, ctx)?;
                frame_introduced.insert(name_str.clone());
                bindings.push((name_str, func_expr, None, stmt.span));
            }
            // A `with begin():` transaction inside a *generator* loop body is a
            // later increment; top-level and simple `for … with begin():` loops
            // are lowered in `stmts.rs`/`transactions.rs`.
            ChlStmt::With { .. } => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "a `with begin():` transaction inside a generator/nested for-loop body \
                     is not yet supported",
                ));
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

    // Fold let-bindings around the terminal from outermost to innermost; each
    // `Let` images its binding statement.
    Ok(bindings
        .into_iter()
        .rev()
        .fold(terminal, |body, (name, val, ann, span)| {
            let let_expr = match ann {
                Some(a) => Expr::let_bind_annotated(name, val, body, a),
                None => Expr::let_bind(name, val, body),
            };
            ctx.tag_image(let_expr, span)
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
                let feed = Expr::feed(name.to_string(), lower_expr(y, ctx)?);
                Ok(ctx.tag_image(feed, stmt.span))
            }
            // `r << e` — direct feed into a named defer handle.
            // Note: when inside a yield-bearing generator (defer_name is Some),
            // `r` is not validated to equal defer_name; a mismatch would
            // type-check via inference but could produce confusing behaviour.
            // A future improvement could add a lowering-time error here.
            ChlExpr::Feed { target, value: v } => {
                let feed = lower_feed(target, v, ctx)?;
                Ok(ctx.tag_image(feed, value.span))
            }
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
            // `if` / `elif` [/ `else`]: one `Case` branch per guard, in source
            // order. A feeding multi-arm `Case` is fanned out by `channelize` into
            // one refined-source channel per feeding arm (predicate
            // `gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`, first-matching-guard-wins), so `elif` and `else` are
            // both ordinary arms. The trailing arm is the `else` body when present
            // (guard `true`, so its first-match predicate is `¬⋁ⱼ gⱼ`), else a
            // `true → Unit` fallthrough (positions no guard admits do nothing).
            let mut out_branches = Vec::with_capacity(branches.len() + 1);
            for branch in branches {
                let cond = lower_expr(&branch.cond, ctx)?;
                // Same frame: pass through mutation_scope and frame_introduced
                // unchanged so the iter_var remains shadowable inside the guard.
                let arm = lower_for_body_stmts(
                    &branch.body,
                    defer_name,
                    mutation_scope,
                    frame_introduced.clone(),
                    ctx,
                )?;
                out_branches.push(Branch {
                    pattern: None,
                    guard: cond,
                    body: arm,
                });
            }
            // The fallthrough arm's guard is manufactured encoding; the `Case`
            // itself images the `if` statement. An `else` body is *not*
            // manufactured — its nodes are recorded by their own lowering, and
            // re-tagging its root here would overwrite that attribution with
            // `Machinery` (last tag wins) — so only the `Unit` synthesized to
            // stand in for a missing `else` is tagged.
            let fallthrough = match else_body {
                Some(else_body) => lower_for_body_stmts(
                    else_body,
                    defer_name,
                    mutation_scope,
                    frame_introduced.clone(),
                    ctx,
                )?,
                None => {
                    ctx.tag_machinery(Expr::lit(Lit::Unit), stmt.span, "lower.guard_fallthrough")
                }
            };
            out_branches.push(Branch {
                pattern: None,
                guard: ctx.tag_machinery(
                    Expr::lit(Lit::Bool(true)),
                    stmt.span,
                    "lower.guard_fallthrough",
                ),
                body: fallthrough,
            });
            Ok(ctx.tag_image(
                Expr::new(TypedExprNode::Case {
                    scrutinee: None,
                    branches: out_branches,
                }),
                stmt.span,
            ))
        }
        ChlStmt::For { target, iter, body } => {
            let inner_var = extract_name_target(target, "for-loop target")?;
            let inner_source = lower_expr(iter, ctx)?;
            // New frame: the outer frame's names (including iter_var) move into
            // mutation_scope so that the inner body cannot mutate them.
            let inner_mutation_scope = body_scope(mutation_scope, frame_introduced);
            let inner_frame = HashSet::from([inner_var.clone()]);
            // The inner loop target shadows a like-named transactional mutable variable.
            let inner_body = ctx.with_shadowed([inner_var.clone()], |ctx| {
                lower_for_body_stmts(body, defer_name, &inner_mutation_scope, inner_frame, ctx)
            })?;
            Ok(tagged_for_loop(
                inner_var,
                inner_source,
                inner_body,
                stmt.span,
                ctx,
            ))
        }
        // A `with begin():` transaction as a *generator* loop-body terminal is a
        // later increment; top-level and simple `for … with begin():` loops are
        // lowered in `stmts.rs`/`transactions.rs`.
        ChlStmt::With { .. } => Err(LoweringError::unsupported(
            stmt.span,
            "a `with begin():` transaction inside a generator/nested for-loop body \
             is not yet supported",
        )),
        _ => Err(LoweringError::unsupported(
            stmt.span,
            "for-loop body must end in a yield, `<<` feed, nested for, or if-guard",
        )),
    }
}

// ---------------------------------------------------------------------------
// Mutation loop lowering — `Loop` CCL nodes
// ---------------------------------------------------------------------------

/// If `stmt` is a *mutation* of an existing binding to a simple name, return
/// that name.
///
/// Only the mutation operators qualify: `:=` ([`ChlStmt::MutAssign`]) and its
/// shorthand `+=` ([`ChlStmt::AugAssign`]). A plain `=` ([`ChlStmt::Assign`]) is
/// an immutable binding, never a mutable write — a loop body's `x = e` is a
/// per-iteration `let`, so it is *not* a loop-carried accumulator and does not
/// qualify here. (A plain `=` to a name bound *outside* the loop is then caught
/// as an error by the generator-loop path, which forbids rebinding an outer
/// name — the author must use `:=` to write a mutable variable.) `<<=` is a
/// [`ChlStmt::Define`] (deferred-collection define, not a mutation) and is
/// rejected here automatically.
fn mutation_target_name(stmt: &Spanned<ChlStmt>) -> Option<&str> {
    match &stmt.node {
        ChlStmt::AugAssign { target, .. } => name_target_as_name(target),
        ChlStmt::MutAssign { target, .. } => name_target_as_name(target),
        _ => None,
    }
}

/// The statement an assignment's block right-hand side wraps, when this
/// statement has one.
///
/// The accumulator scans below walk statements, and a block right-hand side
/// puts statements inside an expression, so a write in one of its branches is
/// invisible to them without this. It is a loop-carried write like any other:
/// `push_bindings_into_writing_cases` pushes the binding into the branches,
/// which puts the write on a spine `transform_chain` merges into the writer
/// decision (`src/ccl/design/mutability.md`, "A write inside a `Case` bound by
/// a `Let`").
fn block_value_stmt(stmt: &Spanned<ChlStmt>) -> Option<&Spanned<ChlStmt>> {
    let value = match &stmt.node {
        ChlStmt::Assign { value, .. }
        | ChlStmt::AnnAssign { value, .. }
        | ChlStmt::AugAssign { value, .. }
        | ChlStmt::MutAssign { value, .. }
        | ChlStmt::Define { value, .. }
        | ChlStmt::Expr(value) => value,
        _ => return None,
    };
    match &value.node {
        ChlExpr::Block(inner) => Some(inner),
        _ => None,
    }
}

/// Scan a for-loop body for assignments that mutate names already
/// bound in `mutation_scope`.  Returns every such name in first-mention
/// order, deduplicated, so the direct-mirror loop's `acc_names` cover
/// *all* loop-carried accumulators.
///
/// Used by [`lower_middle_stmt`] both as a predicate ("is this for-loop a
/// mutation accumulator loop?" — non-empty result) and as the canonical
/// accumulator list for [`lower_direct_mirror_loop`].  The body's own
/// sequential walk there handles every individual mutation; this just
/// decides which names are loop-carried.
///
/// `o <<= x` is a [`ChlStmt::Define`] (deferred-collection define), not a
/// mutation — [`mutation_target_name`] filters those out.
pub(super) fn find_mutation_loop_vars(
    body: &[Spanned<ChlStmt>],
    mutation_scope: &HashSet<String>,
) -> Vec<String> {
    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    collect_mutation_loop_vars(body, mutation_scope, &mut vars, &mut seen);
    vars
}

/// Recurse the accumulator scan into `if`/`elif`/`else` branches: a `+=` / `:=`
/// under a conditional is still a loop-carried accumulator (the conditional
/// induction write becomes one recurrence leg per path). We descend into `if`
/// branches only — **not** inner `for` loops (nested-loop mutation is still
/// unsupported, and a write buried in an inner `for` must stay invisible here so
/// the caller's `find_nested_mutation_var` reject still fires) nor `with begin()`
/// blocks (those carry their own transactional keys).
fn collect_mutation_loop_vars(
    body: &[Spanned<ChlStmt>],
    scope: &HashSet<String>,
    vars: &mut Vec<String>,
    seen: &mut HashSet<String>,
) {
    for stmt in body {
        if let Some(name) = mutation_target_name(stmt)
            && scope.contains(name)
            && seen.insert(name.to_string())
        {
            vars.push(name.to_string());
        }
        if let ChlStmt::If {
            branches,
            else_body,
        } = &stmt.node
        {
            for branch in branches {
                collect_mutation_loop_vars(&branch.body, scope, vars, seen);
            }
            if let Some(else_body) = else_body {
                collect_mutation_loop_vars(else_body, scope, vars, seen);
            }
        }
        if let Some(inner) = block_value_stmt(stmt) {
            collect_mutation_loop_vars(std::slice::from_ref(inner), scope, vars, seen);
        }
    }
}

/// The first top-level plain `=` ([`ChlStmt::Assign`]) in `body` that rebinds a
/// name bound *outside* the loop (`mutation_scope`).
///
/// `=` binds immutably, so such a write is not a mutable-variable mutation — it is a
/// per-iteration shadow that silently discards each update, almost always a
/// mistaken accumulator. A no-yield / no-feed mutation loop bypasses
/// [`lower_for_body_stmts`] (which rejects the same shape), so its caller uses
/// this to reject it explicitly and point the author at `:=`. Real mutations
/// (`:=` / `+=`) are surfaced by [`find_mutation_loop_vars`], not here.
pub(super) fn first_outer_plain_assign<'a>(
    body: &'a [Spanned<ChlStmt>],
    mutation_scope: &HashSet<String>,
) -> Option<&'a str> {
    body.iter().find_map(|stmt| match &stmt.node {
        ChlStmt::Assign { target, .. } => {
            name_target_as_name(target).filter(|n| mutation_scope.contains(*n))
        }
        _ => None,
    })
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
        if let Some(inner) = block_value_stmt(stmt)
            && let Some(n) = find_nested_mutation_var(std::slice::from_ref(inner), mutation_scope)
        {
            return Some(n);
        }
    }
    None
}

/// The `for` statement a loop-lowering entry point is lowering: everything the
/// statement itself says, as against the continuation and the generator defer
/// the caller supplies.
///
/// `acc_names` may be empty: a bare-effect loop (`for x: bump(cnt)`) has no
/// *visible* accumulator, since the write is hidden inside a call and only
/// surfaces post-inline. The phase then decides — a `MutWrite` in the inlined
/// body makes it an accumulator loop, a write-free body makes it a no-op.
///
/// `outer_bindings` is the scope the loop sits in. The body's own statements
/// consult it to lower a block right-hand side, whose meaning depends on which
/// names are bound above the block
/// ([`lower_block_value`](super::stmts::lower_block_value)).
pub(super) struct ForSite<'a> {
    pub target: &'a Spanned<AssignTarget>,
    pub iter: &'a Spanned<ChlExpr>,
    pub body_stmts: &'a [Spanned<ChlStmt>],
    pub acc_names: &'a [String],
    pub outer_bindings: &'a HashSet<String>,
    pub for_span: Span,
}

/// Lower a mutation loop to the direct-mirror shape
/// `ExprStmt(For { target, iter, body }, continuation)` consumed by the
/// unified letrec phase (src/ccl/design/mutability.md).
///
/// The body lowers statement-by-statement without read-your-writes
/// shadowing: writes to `acc_names` become [`TypedExprNode::MutWrite`]
/// markers, `<<` feeds and `yield`s become [`TypedExprNode::Feed`] markers,
/// a bare expression statement (e.g. a call to a pass-by-reference writer
/// `bump(cnt)`) becomes a side-effect `ExprStmt`, and their embedded reads
/// stay bare `Var`s. The phase threads the recurrence, the read-your-writes
/// shadowing, and hoists each in-loop feed to an ordinary feed of the loop's
/// history for channelize to route. Other assignments are per-iteration `Let`s.
///
/// `yield_defer` names the synthesised generator defer a `yield` feeds; a
/// `yield` with no `yield_defer` in scope is an error.
pub(super) fn lower_direct_mirror_loop(
    site: &ForSite<'_>,
    continuation: Expr,
    yield_defer: Option<&str>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let &ForSite {
        target,
        iter,
        body_stmts,
        acc_names,
        outer_bindings,
        for_span,
    } = site;
    let iter_var = extract_name_target(target, "for-loop target")?;
    let source = lower_expr(iter, ctx)?;

    // Build the statement chain right-to-left, ending in Unit (the For's
    // body is a statement, not a value). The loop target is in scope over the
    // body — shadow it so a body read of a like-named transactional mutable variable is
    // read as the loop local, not gated as an out-of-block mutable variable read.
    let chain = ctx.with_shadowed([iter_var.clone()], |ctx| {
        lower_loop_body_chain(
            body_stmts,
            acc_names,
            yield_defer,
            false,
            outer_bindings,
            for_span,
            ctx,
        )
    })?;

    // The direct-mirror `For` images the for statement; the sequencing
    // `ExprStmt` splicing it before the continuation is manufactured.
    let for_node = ctx.tag_image(
        Expr::new(TypedExprNode::For {
            target: TypedBinding {
                name: iter_var.into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            iter: Box::new(source),
            body: Box::new(chain),
        }),
        for_span,
    );
    Ok(ctx.tag_machinery(
        Expr::expr_stmt(for_node, continuation),
        for_span,
        "lower.stmt_seq",
    ))
}

/// Lower a for-loop body's statement list to the direct-mirror statement chain
/// (right-to-left, ending in `Unit`; the `For` body is a statement, not a
/// value). Shared by [`lower_direct_mirror_loop`] and the conditional-write
/// `ChlStmt::If` arm below, which recurses through it to lower each branch's
/// body identically — so a `+=` under an `if` produces the same `MutWrite`
/// marker it would at top level, just nested inside a statement-position `Case`.
///
/// `in_conditional` is `true` when lowering an `if`-branch body: a per-iteration
/// `with begin():` transaction inside a conditional is not yet supported (the
/// per-path transaction verdict — see `design/mutability.md`), so it is rejected
/// there rather than emitted as a `Begin` marker.
fn lower_loop_body_chain(
    body_stmts: &[Spanned<ChlStmt>],
    acc_names: &[String],
    yield_defer: Option<&str>,
    in_conditional: bool,
    outer_bindings: &HashSet<String>,
    for_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Every node this chain mints is recorded: an unrecorded lowering mint is a
    // `Leak::Unrecorded` at the lowering boundary. A statement's own image gets
    // `tag_image`; the `ExprStmt` that sequences one statement before the rest is
    // manufactured plumbing (`src/ccl/design/provenance.md`, "The seam").
    let mut chain = ctx.tag_machinery(Expr::lit(Lit::Unit), for_span, "lower.loop_unit");
    for stmt in body_stmts.iter().rev() {
        chain = match &stmt.node {
            // `x = value` — a plain immutable binding. Inside a loop body it
            // is a per-iteration shadowing `let`, *never* a mutable write: `=`
            // is not a mutation operator (accumulators are written with `:=`
            // / `+=`). A loop-carried accumulator therefore never appears here.
            ChlStmt::Assign { target, value } => {
                let name = extract_name_target(target, "assignment")?;
                check_mut_write_context(&name, stmt.span, ctx)?;
                let val = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                ctx.tag_image(Expr::let_bind(name, val, chain), stmt.span)
            }
            // `x op= value` — a mutable write, always. A write to an accumulator
            // declared before the loop is the `MutWrite` the phase threads as the
            // recurrence; `op=` on anything else is a write to a non-mutable, which
            // is a type error and not a rebind. It cannot fall back to a shadowing
            // `let` for the same reason `:=` cannot: the update would be discarded
            // at the iteration boundary, and `op=` reads the old value, so a
            // per-iteration rebind reads the *seed* every time.
            ChlStmt::AugAssign { target, op, value } => {
                let name = extract_name_target(target, "augmented assignment")?;
                if !acc_names.contains(&name) {
                    return Err(in_loop_aug_assign_error(stmt.span, &name));
                }
                check_mut_write_context(&name, stmt.span, ctx)?;
                let rhs = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                let val = lower_aug_binop(&name, *op, rhs, stmt.span, ctx)?;
                let write = ctx.tag_image(Expr::mut_write(name, val), stmt.span);
                ctx.tag_image(Expr::expr_stmt(write, chain), stmt.span)
            }
            // `x := value` — a write to an accumulator declared before the
            // loop, lowered to the `MutWrite` the phase threads as the
            // recurrence.
            //
            // A `:=` naming anything *else* introduces a mutable variable, and a
            // mutable variable declared inside a loop body is not supported at any
            // spelling — the annotation is orthogonal to that. It cannot fall
            // back to a per-iteration `let`: `:=` is a mutable operator, and
            // silently rebinding it would be the shadowing the design forbids
            // by name (`src/ccl/design/mutability.md`, "Sequencing domains"),
            // discarding every update at the iteration boundary.
            ChlStmt::MutAssign { target, value, .. } => {
                let name = extract_name_target(target, "mutable assignment")?;
                if !acc_names.contains(&name) {
                    return Err(in_loop_mut_var_error(stmt.span, &name));
                }
                check_mut_write_context(&name, stmt.span, ctx)?;
                let val = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                let write = ctx.tag_image(Expr::mut_write(name, val), stmt.span);
                ctx.tag_image(Expr::expr_stmt(write, chain), stmt.span)
            }
            // `y: T = value` — an ordinary annotated per-iteration local, the
            // annotated counterpart of the plain `y = value` binding above.
            // Lowers to an annotated shadowing `let` (never a `MutWrite`: a
            // `Mut(…)` accumulator must be declared *before* the loop, matching
            // `lower_for_body_stmts`).
            ChlStmt::AnnAssign {
                target,
                annotation,
                value,
            } => {
                let name = extract_name_target(target, "annotated assignment")?;
                if mut_annotation_parts(&annotation.ty, ctx).is_some() {
                    return Err(in_loop_mut_var_error(stmt.span, &name));
                }
                let ann = lower_type_annotation(annotation, ctx)?;
                let val = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                ctx.tag_image(Expr::let_bind_annotated(name, val, chain, ann), stmt.span)
            }
            // `o << value` — an in-loop feed. Emitted as a raw `Feed` marker
            // (reads stay bare); the phase resolves its value in the
            // read-your-writes environment and hoists it out of the loop.
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
                let feed = ctx.tag_image(Expr::feed(defer_name, lowered), value.span);
                ctx.tag_machinery(Expr::expr_stmt(feed, chain), stmt.span, "lower.stmt_seq")
            }
            // `yield value` — a feed into the surrounding generator's defer.
            ChlStmt::Expr(value) if let ChlExpr::Yield(y) = &value.node => {
                let defer_name = yield_defer.ok_or_else(|| {
                    LoweringError::unsupported(
                        value.span,
                        "yield outside a generator for-loop context",
                    )
                })?;
                let lowered = lower_expr(y, ctx)?;
                let feed = ctx.tag_image(Expr::feed(defer_name.to_string(), lowered), value.span);
                ctx.tag_machinery(Expr::expr_stmt(feed, chain), stmt.span, "lower.stmt_seq")
            }
            // `if p: … [else: …]` — a conditional write path. Lowered to a
            // statement-position filter-`Case` (`[gᵢ → branchᵢ; true → else|unit]`)
            // that `letrec_phase` forks into one recurrence leg per path (the
            // write legs plus the carry-forward complement). See
            // `src/ccl/design/mutability.md`, "Value-selecting `Case` and
            // conditional induction writes (partially implemented)".
            ChlStmt::If {
                branches,
                else_body,
            } => {
                let case = build_loop_if_case(
                    branches,
                    else_body.as_deref(),
                    acc_names,
                    yield_defer,
                    outer_bindings,
                    stmt.span,
                    ctx,
                )?;
                ctx.tag_machinery(Expr::expr_stmt(case, chain), stmt.span, "lower.stmt_seq")
            }
            // A bare expression statement — the `Feed`/`Yield` guards above
            // did not match, so this is an ordinary side-effect (e.g. a call
            // to a pass-by-reference writer, `bump(cnt)`). Sequence it before
            // the rest; its value is discarded (the loop body is a statement).
            // Post-inline it may reveal a `MutWrite` (accumulator loop) or turn
            // out pure (the phase drops the loop as a no-op).
            ChlStmt::Expr(value) => {
                let lowered = lower_expr(value, ctx)?;
                ctx.tag_machinery(Expr::expr_stmt(lowered, chain), stmt.span, "lower.stmt_seq")
            }
            // `with begin(): <block>` inside an `if` in the loop body: a per-path
            // transaction site is unsound (§4.3 transaction verdict) — rejected.
            ChlStmt::With { .. } if in_conditional => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "a `with begin():` transaction inside an `if` in a for-loop body \
                     is not supported; move it to the loop's top level",
                ));
            }
            // `with begin(): <block>` — a per-iteration transaction, emitted
            // as a `Begin` marker (one statement in the loop body). Its
            // atomic writes/reads live in the block; sibling induction `+=`
            // writes and `<<` feeds around it stay on this loop body.
            // `transact_phase` strips the `Begin` into a commit-record site
            // keyed on this loop and leaves the induction remainder for the
            // recurrence — which is what lets one loop mix both.
            ChlStmt::With { .. } => {
                let block = lower_with_block(stmt, outer_bindings, ctx)?;
                let begin = ctx.tag_image(Expr::begin(block), stmt.span);
                ctx.tag_machinery(Expr::expr_stmt(begin, chain), stmt.span, "lower.stmt_seq")
            }
            _ => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "only assignments (`x = …`, `x op= …`), `<<` feeds, \
                     `yield`, `if` guards, `with begin():` transactions, and bare \
                     side-effect calls are supported inside a for-loop body",
                ));
            }
        };
    }
    Ok(chain)
}

/// Build the statement-position filter-`Case` for an `if`/`elif`/`else` in a
/// for-loop body (a conditional induction write / feed). Each branch's body is
/// lowered through [`lower_loop_body_chain`] (so nested writes and feeds lower
/// identically to top-level ones); a missing `else` becomes an implicit
/// `true → unit` carry-forward branch — the position where the accumulator
/// keeps its previous value. `letrec_phase` forks this `Case` into one
/// recurrence leg per branch.
fn build_loop_if_case(
    branches: &[IfBranch],
    else_body: Option<&[Spanned<ChlStmt>]>,
    acc_names: &[String],
    yield_defer: Option<&str>,
    outer_bindings: &HashSet<String>,
    stmt_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let mut out = Vec::with_capacity(branches.len() + 1);
    for br in branches {
        let guard = lower_expr(&br.cond, ctx)?;
        let body = lower_loop_body_chain(
            &br.body,
            acc_names,
            yield_defer,
            true,
            outer_bindings,
            br.cond.span,
            ctx,
        )?;
        out.push(Branch {
            pattern: None,
            guard,
            body,
        });
    }
    let else_chain = match else_body {
        Some(eb) => lower_loop_body_chain(
            eb,
            acc_names,
            yield_defer,
            true,
            outer_bindings,
            stmt_span,
            ctx,
        )?,
        // The implicit carry-forward arm: manufactured, so it is tagged here rather
        // than carrying a statement's image.
        None => ctx.tag_machinery(Expr::lit(Lit::Unit), stmt_span, "lower.loop_if_carry"),
    };
    out.push(Branch {
        pattern: None,
        guard: ctx.tag_machinery(Expr::lit(Lit::Bool(true)), stmt_span, "lower.loop_if_carry"),
        body: else_chain,
    });
    // The `Case` images the `if` statement inside the loop body.
    Ok(ctx.tag_image(
        Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: out,
        }),
        stmt_span,
    ))
}

/// Lower a mutation loop that feeds or yields, via the direct-mirror
/// `For`/`MutWrite`/`Feed` path (the unified letrec phase routes the feeds).
/// A `yield`ing loop is a generator: allocate its `__result` defer, wrap the
/// loop in `let __result = Defer in <loop>; __result`, and lower each `yield`
/// as a feed to `__result`. A `<<`-only loop feeds pre-existing defers/sinks
/// and needs no wrapper.
pub(super) fn lower_generator_or_mutation_loop(
    site: &ForSite<'_>,
    continuation: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if for_body_has_yield(site.body_stmts) {
        let yield_defer = ctx.fresh_result_name();
        let inner = lower_direct_mirror_loop(site, continuation, Some(&yield_defer), ctx)?;
        Ok(generator_defer_binding(
            yield_defer,
            inner,
            site.for_span,
            ctx,
        ))
    } else {
        lower_direct_mirror_loop(site, continuation, None, ctx)
    }
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

    /// A `with begin():` block that neither writes a transactional mutable variable nor
    /// feeds a read does nothing observable and is rejected. Covers standalone,
    /// middle, and loop-body positions — here `x`/`y` are plain locals, not
    /// `Mut(_, Txn)` stores, and there is no feed.
    #[test]
    fn test_with_begin_requires_effect() {
        for code in [
            "with begin():\n    x = 1\nx",
            "with begin():\n    x = 1\ny = 2\ny",
            "for r in [1]:\n    with begin():\n        x = 1\nx",
        ] {
            let stmts = parse_module(code);
            let err = expect_one_lowering_error(&stmts);
            let LoweringError::Unsupported { message: msg, .. } = &err;
            assert!(
                msg.contains("must do something"),
                "expected a `with begin()` no-effect error, got: {msg}"
            );
        }
    }

    /// `store: Mut(Int, Txn) := 0` lowers as a plain `let store = 0`, registering
    /// `store` transactional. A *bare* trailing read is then rejected — a
    /// transactional mutable variable may be read only inside a `with begin():` block.
    #[test]
    fn test_mut_txn_bare_read_rejected() {
        let stmts = parse_module("store: Mut(Int, Txn) := 0\nstore");
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message: msg, .. } = &err;
        assert!(
            msg.contains("inside a `with begin():` block"),
            "expected a `with begin():` hint for a bare transactional read, got: {msg}"
        );
    }

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

    /// Brainstorm §4b — a generator with loop-carried state lowers to a
    /// `Loop` whose body contains a raw `Feed(__result_*, …)` followed by
    /// a `(step: …)` Record, with the surrounding `let __result = defer`
    /// collecting the yields.  [`crate::ccl::channelize`] absorbs
    /// the raw `Feed` into a `to_<defer>` field on the same Record
    /// before inference.
    #[test]
    fn test_generator_with_loop_carried_mutation_lowers() {
        let code = "\
def running_totals(items):
    total := 0
    for item in items:
        total += item
        yield total
running_totals";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("running_totals should lower as a direct-mirror generator loop");
        let s = symbolic(&ccl);
        // The generator lowers to the direct-mirror shape: a `__result` defer
        // bound around a `For` loop whose body writes `total` and feeds the
        // defer with each yield. The unified letrec phase turns this into a
        // causal `LetRec` and hoists the yield-feed (src/ccl/design/mutability.md).
        assert!(
            s.contains("__result_") && s.contains("defer"),
            "should bind a defer for the generator's yields: {s}"
        );
        assert!(
            s.contains("for item in"),
            "should produce a direct-mirror `For` loop over `item`: {s}"
        );
        assert!(
            s.contains("total :="),
            "should emit a `MutWrite` (`total := …`) for the accumulator: {s}"
        );
        assert!(
            s.contains("feed(__result_"),
            "should feed the generator defer with each yield: {s}"
        );
    }

    /// Rebinding a function *parameter* with a plain `=` inside a generator
    /// loop is rejected: `=` binds immutably, so it cannot carry state across
    /// iterations. The error points at `:=` (introduce a mutable variable to mutate).
    #[test]
    fn test_generator_mutation_of_arg_rejected() {
        let code = "\
def bad(xs, n):
    for x in xs:
        n = n + 1
        yield n
bad";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message: msg, .. } = &err;
        assert!(
            msg.contains("mutation") && msg.contains("`n`") && msg.contains(":="),
            "error should call out mutation of `n` and hint at `:=`: {msg}"
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

    /// A plain `=` accumulator (`x = x + i` over an outer `x`, no `:=`) is
    /// rejected rather than silently lowering to a no-op per-iteration shadow:
    /// `=` binds immutably. The error points at `:=` — accumulators are opt-in.
    #[test]
    fn test_plain_accumulator_requires_mut() {
        let code = "\
x = 0
for i in [1, 2, 3]:
    x = x + i
x";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message: msg, .. } = &err;
        assert!(
            msg.contains("mutation") && msg.contains("`x`") && msg.contains(":="),
            "error should hint at `:=`: {msg}"
        );
    }

    /// Mutation of an outer-scope variable nested inside an `if` in a
    /// for-loop body is rejected with a targeted message that names the
    /// variable and points at the nesting, rather than falling through
    /// to the generator-for fallback's generic "must end in yield".
    #[test]
    fn test_mutation_nested_in_if_else_now_lowers() {
        // A mutation nested under an `if`/`else` is a conditional induction
        // write — no longer rejected. Both legs become branches of the
        // statement-position filter-`Case`; `letrec_phase` forks them into
        // per-path recurrence legs.
        let code = "\
x := 0
for i in [1, 2]:
    if i > 0:
        x := x + i
    else:
        x := x - i
x";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("conditional if/else induction write should lower");
        let s = symbolic(&ccl);
        assert_eq!(
            s,
            "x : Mut(_, _) := 0\n\
             in for i in [1, 2] do { i > 0 → x := x + i; unit; \
             true → x := x - i; unit }; unit; x",
            "if/else conditional write lowers to a two-branch filter-Case, each \
             leg carrying its own MutWrite: {s}"
        );
    }

    /// Same shape but mutation nested in an inner `for` rather than `if`.
    #[test]
    fn test_mutation_nested_in_for_rejected() {
        let code = "\
x := 0
for i in [1, 2]:
    for j in [10, 20]:
        x := x + i + j
x";
        let stmts = parse_module(code);
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message: msg, .. } = &err;
        assert!(
            msg.contains("nested") && msg.contains("`x`"),
            "error should call out nested mutation of `x`: {msg}"
        );
    }

    /// `if/else` inside a generator for-loop body lowers: the `else` becomes the
    /// trailing `true`-guarded `Case` arm (its first-match predicate `¬(x > 0)`),
    /// which `channelize` fans out as its own feeding channel.
    #[test]
    fn test_generator_if_else_in_body_lowers() {
        let code = "\
def bad(xs):
    for x in xs:
        if x > 0:
            yield x
        else:
            yield 0
bad";
        let stmts = parse_module(code);
        lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("if/else in a generator for-loop body should lower");
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

    /// A conditional induction write `if p: x += i` lowers the loop body to
    /// a statement-position filter-`Case` — the write leg under the guard and an
    /// implicit `true → unit` carry-forward branch — with the accumulator write a
    /// `MutWrite` marker inside the guarded branch. `letrec_phase` forks this into
    /// per-path recurrence legs.
    #[test]
    fn test_lower_conditional_induction_write() {
        let code = "\
x := 0
for i in [1, 2, 3]:
    if i > 1:
        x += i
x";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("conditional induction write should lower");
        let s = symbolic(&ccl);
        assert_eq!(
            s,
            "x : Mut(_, _) := 0\n\
             in for i in [1, 2, 3] do { i > 1 → x := x + i; unit; true → unit }; unit; x",
            "conditional write lowers to a statement-position filter-Case with the \
             MutWrite in the guarded leg and a `true → unit` carry-forward complement"
        );
    }
}

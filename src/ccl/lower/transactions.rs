//! Lowering of `with begin():` transaction blocks — standalone and as a loop
//! body — to the direct-mirror `For`/`MutWrite` shape `transact_phase` folds
//! into one shared commit store.
//!
//! A transaction is lowered exactly like an induction mutation loop
//! (`ExprStmt(For{target, iter, block}, continuation)`); the *only* structural
//! difference is that its `MutWrite`s target `Mut[V, Txn]` stores, which
//! `transact_phase` recognizes (by the store's registered base name) and routes
//! to the commit engine rather than the induction `Recurse`. A standalone
//! transaction is one commit over a synthesized singleton source. Writes and
//! reads inside the block run with `in_tx_body = true`, so a bare store read is
//! a snapshot (a bare store read *outside* a block is the rejected out-of-block
//! read) and an assignment is a write; a nested `with begin():` is rejected. A
//! read fed out of a block that does not write that store is a live as-of read;
//! trailing sibling `<<` feeds are request-indexed replies (see
//! `lower_transaction_loop`).

use super::*;
use crate::{
    ccl::{Branch, Expr, Lit, Type, TypedBinding, TypedExprNode},
    chl_parser::ast::{AssignTarget, Expr as ChlExpr, IfBranch, Span, Spanned, Stmt as ChlStmt},
};

/// Whether `for_body` is a `with begin():` block optionally followed by sibling
/// `<<` reply feeds — a transaction loop (one transaction per iteration). The
/// leading block writes/reads transactional stores; each trailing feed is a
/// request-indexed reply (`resp << e`) that rides the request loop, independent
/// of the commit clock (e.g. a POST loop's `with begin(): store = req` followed
/// by `resp << "ok\n"`). A `<<` before the block, or any other trailing
/// statement, is not this shape.
pub(super) fn for_body_is_transaction(for_body: &[Spanned<ChlStmt>]) -> bool {
    matches!(
        for_body.first().map(|s| &s.node),
        Some(ChlStmt::With { .. })
    ) && for_body[1..].iter().all(is_feed_stmt)
}

/// Whether `stmt` is a bare `resp << e` feed statement.
fn is_feed_stmt(stmt: &Spanned<ChlStmt>) -> bool {
    matches!(&stmt.node, ChlStmt::Expr(e) if matches!(&e.node, ChlExpr::Feed { .. }))
}

/// Validate that a `with` block's context is the `begin()` transaction marker.
/// Rejects the retired `with tx():` form and any other context expression.
/// The `with t = begin():` transaction *handle* (binding the commit time to
/// `t`) parses but is not yet consumable inside the block: a body reference to
/// `t` would silently resolve to an outer `t` in scope (or fail with an opaque
/// "unbound variable") rather than the commit time. Reject the handle form until
/// it is implemented — see the divergence list in src/ccl/design-mut-txn-feed.md.
fn reject_txn_handle<T>(binding: &Option<T>, span: Span) -> Result<(), LoweringError> {
    if binding.is_some() {
        return Err(LoweringError::unsupported(
            span,
            "the `with t = begin():` transaction handle is not supported yet; use `with begin():` \
             (the commit time is not yet bindable inside the block)",
        ));
    }
    Ok(())
}

fn validate_begin_context(context: &Spanned<ChlExpr>) -> Result<(), LoweringError> {
    if let ChlExpr::Call { func, args } = &context.node
        && let ChlExpr::Name(id) = &func.node
        && id.as_str() == "begin"
        && args.is_empty()
    {
        return Ok(());
    }
    Err(LoweringError::unsupported(
        context.span,
        "a `with` block's context must be `begin()` (the transaction marker); \
         write `with begin():` or `with t = begin():`",
    ))
}

/// Lower `for <target> in <iter>: with begin(): <block>` (optionally followed by
/// sibling `resp << e` reply feeds) to `ExprStmt(For{target, iter, <block>},
/// <reply feeds> ; continuation)` — one transaction per iteration, the loop
/// source driving the writer.
///
/// Each trailing sibling feed becomes a **request-indexed** reply — a plain map
/// of the loop source, `Feed(resp, source ≫ (λ item → e))`, independent of the
/// commit clock. This is the outer index the HTTP response sink dispatches by (a
/// per-commit tap inside the block would be commit-tick-indexed and misdispatch).
/// The reply may reference the loop item and outer bindings, but not a
/// transactional store (a store read outside a `with begin():` block is rejected)
/// — a *live* read must sit inside the block, where it becomes an as-of read.
pub(super) fn lower_transaction_loop(
    target: &Spanned<AssignTarget>,
    iter: &Spanned<ChlExpr>,
    for_body: &[Spanned<ChlStmt>],
    continuation: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let with_stmt = &for_body[0];
    let ChlStmt::With {
        binding,
        context,
        body,
    } = &with_stmt.node
    else {
        unreachable!("for_body_is_transaction guarantees a leading With statement")
    };
    reject_txn_handle(binding, with_stmt.span)?;
    validate_begin_context(context)?;
    let iter_var = extract_name_target(target, "for-loop target")?;
    let source = lower_expr(iter, ctx)?;
    let block = lower_tx_block(body, with_stmt.span, ctx)?;
    let for_node = for_over(iter_var.clone(), source.clone(), block);
    // Wrap the continuation in one reply-feed `ExprStmt` per trailing sibling
    // feed, innermost-last so the first source feed is the outermost `ExprStmt`
    // (desugar collects feeds outermost-first, preserving source order).
    let mut result = continuation;
    for feed_stmt in for_body[1..].iter().rev() {
        let ChlStmt::Expr(e) = &feed_stmt.node else {
            unreachable!("for_body_is_transaction guarantees trailing feed statements")
        };
        let ChlExpr::Feed {
            target: resp,
            value,
        } = &e.node
        else {
            unreachable!("for_body_is_transaction guarantees trailing feed statements")
        };
        let reply = lower_sibling_reply(&iter_var, &source, resp, value, ctx)?;
        result = Expr::expr_stmt(reply, result);
    }
    Ok(Expr::expr_stmt(for_node, result))
}

/// Lower a trailing sibling reply feed `resp << e` of a transaction loop to
/// `Feed(resp, source ≫ (λ iter_var → e))` — a per-request map of the loop
/// source (the request-indexed reply). `e` is lowered with `in_tx_body = false`,
/// so a bare transactional store read in the reply is rejected.
fn lower_sibling_reply(
    iter_var: &str,
    source: &Expr,
    resp: &Spanned<ChlExpr>,
    value: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let ChlExpr::Name(resp_name) = &resp.node else {
        return Err(LoweringError::unsupported(
            resp.span,
            "reply feed target must be a simple name (e.g. `resps << e`)",
        ));
    };
    // The loop target is in scope over the reply — shadow it so a reply that
    // reads a register spelled like the loop variable (`for store in reqs: …;
    // resps << store`) reads the loop local, not the register (which would
    // otherwise trip the out-of-block read gate).
    let body = ctx.with_shadowed([iter_var.to_string()], |ctx| lower_expr(value, ctx))?;
    let lambda = Expr::lambda(iter_var.to_string(), Type::Hole, body);
    let map = Expr::compose(vec![source.clone(), lambda]);
    Ok(Expr::feed(resp_name.as_str().to_string(), map))
}

/// Lower a standalone `with begin(): <block>` (anywhere a statement can appear)
/// to `ExprStmt(For{__txn_item, [unit], <block>}, continuation)` — one commit
/// over a synthesized singleton source (one item → one transaction).
pub(super) fn lower_standalone_transaction(
    with_stmt: &Spanned<ChlStmt>,
    continuation: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let ChlStmt::With {
        binding,
        context,
        body,
    } = &with_stmt.node
    else {
        unreachable!("caller guarantees a With statement")
    };
    reject_txn_handle(binding, with_stmt.span)?;
    validate_begin_context(context)?;
    let block = lower_tx_block(body, with_stmt.span, ctx)?;
    let iter_var = ctx.fresh_txn_item();
    // A singleton source `[unit]`: one element → exactly one transaction. The
    // item is never read (the block reads only stores).
    let source = Expr::list(vec![Expr::lit(Lit::Unit)]);
    let for_node = for_over(iter_var, source, block);
    Ok(Expr::expr_stmt(for_node, continuation))
}

/// `For { target: <iter_var> (untyped), iter: <source>, body: <block> }`.
fn for_over(iter_var: String, source: Expr, block: Expr) -> Expr {
    Expr::new(TypedExprNode::For {
        target: TypedBinding {
            name: iter_var.into(),
            ty: Type::Hole,
            user_annotation: None,
        },
        iter: Box::new(source),
        body: Box::new(block),
    })
}

/// Lower a `with begin():` block body to a per-transaction statement chain
/// ending in `Unit` — the `For` body `transact_phase` reads to build the writer
/// decision. Runs with `in_tx_body = true` (bare store reads are snapshots).
fn lower_tx_block(
    stmts: &[Spanned<ChlStmt>],
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if ctx.in_tx_body {
        return Err(LoweringError::unsupported(
            span,
            "nested `with begin():` transactions are not supported",
        ));
    }
    ctx.in_tx_body = true;
    let result = lower_tx_block_inner(stmts, ctx);
    ctx.in_tx_body = false;
    let block = result?;
    // A transaction must *do* something observable: either write a transactional
    // store (a committing transaction — a commit-record footprint) or feed a read
    // (`out << store`), a read-only transaction whose fed store read is a live
    // as-of read indexed by the enclosing loop. A block that does neither has no
    // footprint at all (its local `let`s are discarded), so reject it — a truly
    // empty transaction is a program error, not a no-op to silently drop.
    if !contains_mut_write(&block) && !contains_feed(&block) {
        return Err(LoweringError::unsupported(
            span,
            "a `with begin():` block must do something: write a transactional \
             (`Mut[_, Txn]`) variable, or feed a read (`out << …`)",
        ));
    }
    Ok(block)
}

/// Whether the lowered block chain contains a `MutWrite` (i.e. writes a
/// transactional store — `write_or_let` emits `MutWrite` only for those).
fn contains_mut_write(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::MutWrite { .. }) || e.any_child(contains_mut_write)
}

/// Whether the lowered block chain contains a `Feed` (`out << e`) — the
/// footprint of a read-only transaction, whose fed store read is a live as-of
/// read.
fn contains_feed(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::Feed { .. }) || e.any_child(contains_feed)
}

/// Build the block's statement chain right-to-left. Assignments to
/// transactional stores become `MutWrite` markers (reads stay bare `Var`
/// snapshots); `if cond:` guards become `Case` (the no-else deny branch); other
/// assignments are per-iteration `Let`s.
fn lower_tx_block_inner(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let mut chain = Expr::lit(Lit::Unit);
    for stmt in stmts.iter().rev() {
        chain = match &stmt.node {
            // `store := value` — the transactional register write. `:=` is the
            // sole store-write operator; `write_or_let` gates it (a register
            // write commits; a non-store `:=` is a per-transaction local `let`).
            ChlStmt::MutAssign { target, value, .. } => {
                let name = extract_name_target(target, "mutable assignment")?;
                let val = lower_expr(value, ctx)?;
                write_or_let(name, val, chain, stmt.span, ctx)?
            }
            // `store += value` — the compound-write shorthand, likewise a write.
            ChlStmt::AugAssign { target, op, value } => {
                let name = extract_name_target(target, "augmented assignment")?;
                let val = lower_aug_binop(&name, *op, value, ctx)?;
                write_or_let(name, val, chain, stmt.span, ctx)?
            }
            // `x = value` — a plain immutable binding: a per-transaction local
            // `let`. `=` never writes a store; a plain `=` to a register would be
            // a silent no-op shadow that dies at block end, so reject it and point
            // at `:=`. (A genuine local shadowing the register's name is fine.)
            ChlStmt::Assign { target, value } => {
                let name = extract_name_target(target, "assignment")?;
                if !ctx.is_shadowed(&name) && ctx.is_transactional_store(&name) {
                    return Err(LoweringError::unsupported(
                        stmt.span,
                        format!(
                            "write store `{name}` inside a `with begin():` block with `:=` \
                             (`=` binds immutably — a plain `=` here is a no-op shadow)"
                        ),
                    ));
                }
                let val = lower_expr(value, ctx)?;
                Expr::let_bind(name, val, chain)
            }
            // `if cond: <writes>` — a conditional (deny) write. The no-else
            // branch is the deny: `commit = false` for the whole transaction.
            ChlStmt::If {
                branches,
                else_body,
            } => {
                let case = lower_tx_if(branches, else_body.as_deref(), ctx)?;
                Expr::expr_stmt(case, chain)
            }
            // `out << e` inside the block — a per-commit feed. Its value reads
            // the read-your-writes snapshot at this point (a bare store read
            // resolves to the just-written value); `transact_phase` collects it
            // as a `to_<defer>` tap on the writer decision and hoists a
            // `Feed(defer, __store ▷ .to_<defer>)` into the store body, so each
            // emission carries *its own* commit's value. Mirrors the induction
            // phase's in-loop feeds (see `src/ccl/letrec_phase.rs`).
            ChlStmt::Expr(value) if matches!(&value.node, ChlExpr::Feed { .. }) => {
                let feed = lower_expr(value, ctx)?;
                Expr::expr_stmt(feed, chain)
            }
            ChlStmt::With { .. } => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "nested `with begin():` transactions are not supported",
                ));
            }
            _ => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "a `with begin():` block supports store writes (`x := …`, `x += …`), \
                     local bindings (`x = …`), `if cond:` guards, and feeds (`out << e`)",
                ));
            }
        };
    }
    Ok(chain)
}

/// A `:=` / `+=` write inside a transaction. The only legal target is a
/// transactional register (→ a `MutWrite` the commit engine folds); a name
/// shadowed by an inner binder is a genuine local (→ a per-transaction `Let`).
///
/// Any other target — an induction (`Mut[…]`, non-`Txn`) store or a plain
/// binding from an enclosing scope — is rejected: `transact_phase` folds only
/// transactional writes, so the write would be a block-local shadow that dies at
/// block end (computing `[0, 0, …]`). Because store-ness carries no lowering
/// registry, the target cannot be classified here; but inside a block the write
/// *must* be transactional to have any commit footprint, so rejecting every
/// non-register, non-shadowed target is both sound and precise for the reachable
/// cases (a block-local scratch should use `=`, not `:=`).
fn write_or_let(
    name: String,
    val: Expr,
    chain: Expr,
    span: Span,
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    if ctx.is_shadowed(&name) {
        return Ok(Expr::let_bind(name, val, chain));
    }
    if ctx.is_transactional_store(&name) {
        return Ok(Expr::expr_stmt(Expr::mut_write(name, val), chain));
    }
    Err(LoweringError::unsupported(
        span,
        format!(
            "induction store `{name}` (`Mut[…]`) cannot be written inside a `with begin():` \
             block; declare it `Mut[…, Txn]` for a transactional register, or move the write \
             outside the block"
        ),
    ))
}

/// Lower an `if`/`elif`/`else` guard inside a transaction to a `Case`. A bare
/// `if cond:` (no `else`) is the deny idiom — its implicit else branch is `Unit`
/// (no writes), which `transact_phase` reads as `commit = false`.
fn lower_tx_if(
    branches: &[IfBranch],
    else_body: Option<&[Spanned<ChlStmt>]>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // The transaction guard model supports only a single bare `if cond:` — a
    // *deny* guard whose implicit empty else means "do not commit". An `elif`
    // chain or an `else` branch that writes would instead need each written key
    // to become a conditional value (`k = if cond: v_then else: v_else`) with
    // the transaction committing unconditionally — a distinct semantics from
    // the deny guard, and a choice (deny vs. value-select) not yet settled.
    // Reject both here rather than panicking downstream in `transact_phase`.
    if branches.len() > 1 {
        return Err(LoweringError::unsupported(
            branches[1].cond.span,
            "`elif` inside a `with begin():` block is not supported; only a bare \
             `if cond:` deny guard is",
        ));
    }
    if else_body.is_some() {
        return Err(LoweringError::unsupported(
            branches[0].cond.span,
            "an `else` branch inside a `with begin():` block is not supported; a bare \
             `if cond:` is a deny guard (the transaction commits only when `cond` holds)",
        ));
    }
    let mut out_branches = Vec::with_capacity(branches.len() + 1);
    for branch in branches {
        let guard = lower_expr(&branch.cond, ctx)?;
        let body = lower_tx_block_inner(&branch.body, ctx)?;
        out_branches.push(Branch {
            pattern: None,
            guard,
            body,
        });
    }
    let else_expr = match else_body {
        Some(stmts) => lower_tx_block_inner(stmts, ctx)?,
        None => Expr::lit(Lit::Unit),
    };
    out_branches.push(Branch {
        pattern: None,
        guard: Expr::lit(Lit::Bool(true)),
        body: else_expr,
    });
    Ok(Expr::new(TypedExprNode::Case {
        scrutinee: None,
        branches: out_branches,
    }))
}

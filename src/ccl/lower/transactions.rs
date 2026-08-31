//! Lowering of `with begin():` transaction blocks — standalone and as a loop
//! body — to the direct-mirror `For`/`MutWrite` shape `transact_phase` folds
//! into one shared commit mutable variable.
//!
//! A transaction is lowered exactly like an induction mutation loop
//! (`ExprStmt(For{target, iter, block}, continuation)`); the *only* structural
//! difference is that its `MutWrite`s target `Mut(V, Txn)` stores, which
//! `transact_phase` recognizes (by the mutable variable's registered base name) and routes
//! to the commit engine rather than the induction store. A standalone
//! transaction is one commit over a synthesized singleton source. Writes and
//! reads inside the block run with `in_tx_body = true`, so a bare mutable variable read is
//! a snapshot (a bare mutable variable read *outside* a block is the rejected out-of-block
//! read) and an assignment is a write; a nested `with begin():` is rejected. A
//! read fed out of a block that does not write that mutable variable is a live as-of read;
//! trailing sibling `<<` feeds are request-indexed replies (see
//! `lower_transaction_loop`).

use smol_str::SmolStr;

use super::*;
use crate::{
    ccl::{Branch, Expr, Lit, Type, TypedBinding, TypedExprNode},
    chl_parser::ast::{Expr as ChlExpr, IfBranch, Span, Spanned, Stmt as ChlStmt},
};

/// Validate that a `with` block's context is the `begin()` transaction marker.
/// Rejects the retired `with tx():` form and any other context expression.
/// The `with t = begin():` transaction *handle* (binding the commit time to
/// `t`) parses but is not yet consumable inside the block: a body reference to
/// `t` would silently resolve to an outer `t` in scope (or fail with an opaque
/// "unbound variable") rather than the commit time. Reject the handle form until
/// it is implemented — see the divergence list in src/ccl/design/mutability.md.
fn reject_txn_handle(binding: &Option<SmolStr>, span: Span) -> Result<(), LoweringError> {
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

/// Lower a `with begin(): <block>` statement to its per-transaction block chain
/// — the body of a [`TypedExprNode::Begin`] marker. Validates the `begin()`
/// context and rejects the handle form (nested `with` is rejected inside
/// [`lower_tx_block`]). The block is lowered with `in_tx_body = true` (bare mutable variable
/// reads are snapshots).
///
/// The caller wraps the returned chain in `Expr::begin(..)` and places it as one
/// statement of a loop body (a per-iteration transaction) or a singleton `For`
/// (a standalone transaction). `transact_phase` strips each `Begin` into a
/// commit-record site keyed on the enclosing loop.
pub(super) fn lower_with_block(
    with_stmt: &Spanned<ChlStmt>,
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
    lower_tx_block(body, with_stmt.span, ctx)
}

/// Lower a standalone `with begin(): <block>` (anywhere a statement can appear)
/// to `ExprStmt(For{__txn_item, [unit], Begin{<block>}}, continuation)` — one
/// commit over a synthesized singleton source (one item → one transaction). The
/// synthetic `For` gives `transact_phase` an enclosing loop to key the site on,
/// uniform with a per-iteration transaction inside a real loop.
pub(super) fn lower_standalone_transaction(
    with_stmt: &Spanned<ChlStmt>,
    continuation: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let block = lower_with_block(with_stmt, ctx)?;
    let iter_var = ctx.fresh_txn_item();
    // A singleton source `[unit]`: one element → exactly one transaction. The
    // item is never read (the block reads only stores). The `Begin` sits as an
    // `ExprStmt` effect on the (singleton) loop body — the same shape a
    // per-iteration transaction has, so `transact_phase::strip` handles both.
    // The whole singleton-loop scaffolding is manufactured encoding; only the
    // `Begin` images the `with begin():` the user wrote.
    let ts = "lower.txn_singleton";
    let span = with_stmt.span;
    let unit_item = ctx.tag_machinery(Expr::lit(Lit::Unit), span, ts);
    let source = ctx.tag_machinery(Expr::list(vec![unit_item]), span, ts);
    let begin = ctx.tag_image(Expr::begin(block), span);
    let body_unit = ctx.tag_machinery(Expr::lit(Lit::Unit), span, ts);
    let body = ctx.tag_machinery(Expr::expr_stmt(begin, body_unit), span, ts);
    let for_node = ctx.tag_machinery(for_over(iter_var, source, body), span, ts);
    Ok(ctx.tag_machinery(Expr::expr_stmt(for_node, continuation), span, ts))
}

/// `For { target: <iter_var> (untyped), iter: <source>, body: <block> }`.
fn for_over(iter_var: String, source: Expr, block: Expr) -> Expr {
    Expr::new(TypedExprNode::For {
        target: TypedBinding {
            name: iter_var.into(),
            ty: Type::Hole,
            user_annotation: None,
            name_span: None,
        },
        iter: Box::new(source),
        body: Box::new(block),
    })
}

/// Lower a `with begin():` block body to a per-transaction statement chain
/// ending in `Unit` — the `For` body `transact_phase` reads to build the writer
/// decision. Runs with `in_tx_body = true` (bare mutable variable reads are snapshots).
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
    let result = lower_tx_block_inner(stmts, span, ctx);
    ctx.in_tx_body = false;
    let block = result?;
    // A transaction must *do* something observable: either write a transactional
    // mutable variable (a committing transaction — a commit-record footprint) or feed a read
    // (`out << balance`), a read-only transaction whose fed mutable variable read is a live
    // as-of read indexed by the enclosing loop. A block that does neither has no
    // footprint at all (its local `let`s are discarded), so reject it — a truly
    // empty transaction is a program error, not a no-op to silently drop.
    if !contains_mut_write(&block) && !contains_feed(&block) {
        return Err(LoweringError::unsupported(
            span,
            "a `with begin():` block must do something: write a transactional \
             (`Mut(_, Txn)`) variable, or feed a read (`out << …`)",
        ));
    }
    Ok(block)
}

/// Whether the lowered block chain contains a `MutWrite` (i.e. writes a
/// transactional mutable variable — `write_or_let` emits `MutWrite` only for those).
fn contains_mut_write(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::MutWrite { .. }) || e.any_child(contains_mut_write)
}

/// Whether the lowered block chain contains a `Feed` (`out << e`) — the
/// footprint of a read-only transaction, whose fed mutable variable read is a live as-of
/// read.
fn contains_feed(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::Feed { .. }) || e.any_child(contains_feed)
}

/// Build the block's statement chain right-to-left. Assignments to
/// transactional mutable variables become `MutWrite` markers (reads stay bare `Var`
/// snapshots); `if cond:` guards become `Case` (the no-else deny branch); other
/// assignments are per-iteration `Let`s.
///
/// `fallback_span` anchors the manufactured chain terminal when the statement
/// list is empty (the block's own statement spans win when present).
fn lower_tx_block_inner(
    stmts: &[Spanned<ChlStmt>],
    fallback_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Multiple `if` guards, `elif` chains, and `else` branches are all supported:
    // `transact_phase`'s path walk scopes each write to its own control-flow path,
    // rejoins each key with a carry-forward `Case`, and commits on the disjunction
    // of the write paths (see `src/ccl/design/mutability.md`). A guard is no longer
    // transaction-scoped — a spine write beside an `if` commits unconditionally.
    //
    // The chain terminal is manufactured sequencing (spanned to the block's
    // statements — the `with` construct when the block is empty).
    let block_span = match (stmts.first(), stmts.last()) {
        (Some(first), Some(last)) => first.span.join(last.span),
        _ => fallback_span,
    };
    let mut chain = ctx.tag_machinery(Expr::lit(Lit::Unit), block_span, "lower.txn_unit");
    for stmt in stmts.iter().rev() {
        chain = match &stmt.node {
            // `balance := value` — the transactional mutable variable write. `:=` is the
            // sole variable-write operator; `write_or_let` gates it (a write to a
            // mutable variable commits; a `:=` to anything else is a
            // per-transaction local `let`).
            ChlStmt::MutAssign { target, value, .. } => {
                let name = extract_name_target(target, "mutable assignment")?;
                let val = lower_expr(value, ctx)?;
                write_or_let(name, val, chain, stmt.span, ctx)?
            }
            // `balance += value` — the compound-write shorthand, likewise a write.
            ChlStmt::AugAssign { target, op, value } => {
                let name = extract_name_target(target, "augmented assignment")?;
                let val = lower_aug_binop(&name, *op, lower_expr(value, ctx)?, stmt.span, ctx)?;
                write_or_let(name, val, chain, stmt.span, ctx)?
            }
            // `x = value` — a plain immutable binding: a per-transaction local
            // `let`. `=` never writes a mutable variable; a plain `=` to a mutable variable would be
            // a silent no-op shadow that dies at block end, so reject it and point
            // at `:=`. (A genuine local shadowing the mutable variable's name is fine.)
            ChlStmt::Assign { target, value } => {
                let name = extract_name_target(target, "assignment")?;
                if !ctx.is_shadowed(&name) && ctx.is_transactional_mut_var(&name) {
                    return Err(LoweringError::unsupported(
                        stmt.span,
                        format!(
                            "write mutable variable `{name}` inside a `with begin():` block with `:=` \
                             (`=` binds immutably — a plain `=` here is a no-op shadow)"
                        ),
                    ));
                }
                let val = lower_expr(value, ctx)?;
                ctx.tag_image(Expr::let_bind(name, val, chain), stmt.span)
            }
            // `if cond: <writes>` — a conditional (deny) write. The no-else
            // branch is the deny: `commit = false` for the whole transaction.
            ChlStmt::If {
                branches,
                else_body,
            } => {
                let case = lower_tx_if(branches, else_body.as_deref(), ctx)?;
                ctx.tag_machinery(Expr::expr_stmt(case, chain), stmt.span, "lower.stmt_seq")
            }
            // `out << e` inside the block — a per-commit feed. Its value reads
            // the read-your-writes snapshot at this point (a bare mutable variable read
            // resolves to the just-written value); `transact_phase` collects it
            // as a `to_<defer>` tap on the writer decision and hoists a
            // `Feed(defer, __hist ▷ .to_<defer>)` into the mutable variable body, so each
            // emission carries *its own* commit's value. Mirrors the induction
            // phase's in-loop feeds (see `src/ccl/mut_elim.rs`).
            ChlStmt::Expr(value) if matches!(&value.node, ChlExpr::Feed { .. }) => {
                let feed = lower_expr(value, ctx)?;
                ctx.tag_machinery(Expr::expr_stmt(feed, chain), stmt.span, "lower.stmt_seq")
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
                    "a `with begin():` block supports mutable writes (`x := …`, `x += …`), \
                     local bindings (`x = …`), `if cond:` guards, and feeds (`out << e`)",
                ));
            }
        };
    }
    Ok(chain)
}

/// A `:=` / `+=` write inside a transaction, emitted as a `MutWrite` marker (a
/// name shadowed by an inner binder is a genuine local → a per-transaction
/// `Let`). Mutability carries no lowering registry, so the target is *not*
/// classified here: `transact_phase` reads the `Mut(…)` type and routes each
/// write — a transactional mutable variable joins the atomic commit decision; an
/// induction accumulator is lifted onto the enclosing loop as its own recurrence
/// (the two run on independent domains). A write to something that is not a
/// mutable variable surfaces
/// post-inference (`check_mut_write_targets`), not here.
fn write_or_let(
    name: String,
    val: Expr,
    chain: Expr,
    stmt_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if ctx.is_shadowed(&name) {
        return Ok(ctx.tag_image(Expr::let_bind(name, val, chain), stmt_span));
    }
    let write = ctx.tag_image(Expr::mut_write(name, val), stmt_span);
    Ok(ctx.tag_image(Expr::expr_stmt(write, chain), stmt_span))
}

/// Lower an `if`/`elif`/`else` guard inside a transaction to a `Case`. A bare
/// `if cond:` (no `else`) is the deny idiom — its implicit else branch is `Unit`
/// (no writes), which `transact_phase` reads as `commit = false`.
fn lower_tx_if(
    branches: &[IfBranch],
    else_body: Option<&[Spanned<ChlStmt>]>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // `if`/`elif`/`else` inside a block lowers to the general first-match `Case`
    // (branches in order, a trailing `true → else|unit` complement). A bare
    // `if cond:` (no `else`) keeps the deny idiom — its implicit empty-`else`
    // carry means the transaction does not commit that write when `cond` fails;
    // an `elif`/`else` that writes routes each key per path (`transact_phase`).
    let mut out_branches = Vec::with_capacity(branches.len() + 1);
    for branch in branches {
        let guard = lower_expr(&branch.cond, ctx)?;
        let body = lower_tx_block_inner(&branch.body, branch.cond.span, ctx)?;
        out_branches.push(Branch {
            pattern: None,
            guard,
            body,
        });
    }
    // The implicit deny arm (`true → Unit`, "do not commit") is manufactured
    // encoding of the bare `if cond:` deny idiom; the `Case` itself images
    // the guard statement.
    let guard_span = branches[0].cond.span;
    let else_expr = match else_body {
        Some(stmts) => lower_tx_block_inner(stmts, guard_span, ctx)?,
        None => ctx.tag_machinery(Expr::lit(Lit::Unit), guard_span, "lower.txn_deny"),
    };
    out_branches.push(Branch {
        pattern: None,
        guard: ctx.tag_machinery(Expr::lit(Lit::Bool(true)), guard_span, "lower.txn_deny"),
        body: else_expr,
    });
    Ok(ctx.tag_image(
        Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: out_branches,
        }),
        guard_span,
    ))
}

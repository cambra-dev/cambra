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
    ccl::{Branch, Expr, Lit, TypedExprNode},
    chl_parser::{
        SurfaceBuiltin,
        ast::{AssignTarget, Expr as ChlExpr, IfBranch, Span, Spanned, Stmt as ChlStmt},
    },
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
        && SurfaceBuiltin::from_name(id) == Some(SurfaceBuiltin::Begin)
        && SurfaceBuiltin::Begin.arity().accepts(args.len())
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
/// statement of a loop body (a per-iteration transaction) or of any other statement
/// chain (a standalone transaction). `transact_phase` strips each `Begin` into a
/// commit-record site keyed on the enclosing loop, or on a singleton source outside one.
pub(super) fn lower_with_block(
    with_stmt: &Spanned<ChlStmt>,
    outer_bindings: &HashSet<String>,
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
    lower_tx_block(body, outer_bindings, with_stmt.span, false, ctx)
}

/// Lower a `with begin():` block in value position (`x = with begin(): …`) to its
/// [`TypedExprNode::Begin`] marker, whose body chain ends in the block's value: the value of
/// its last statement, an expression or an `if`, `match` or `try` whose blocks each end in
/// one (`docs/chl-spec.md`, "A block is also the value it computes [Decided]"). The enclosing
/// binding carries the value past the block; `transact_phase` strips the `Begin` into a commit
/// site whose every path commits the value.
pub(super) fn lower_valued_with_block(
    with_stmt: &Spanned<ChlStmt>,
    outer_bindings: &HashSet<String>,
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
    let block = lower_tx_block(body, outer_bindings, with_stmt.span, true, ctx)?;
    Ok(ctx.tag_image(Expr::begin(block), with_stmt.span))
}

/// Lower a standalone `with begin(): <block>` (anywhere a statement can appear) to
/// `ExprStmt(Begin{<block>}, continuation)`. The transaction phase runs it once, over a
/// singleton source.
pub(super) fn lower_standalone_transaction(
    with_stmt: &Spanned<ChlStmt>,
    continuation: Expr,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let block = lower_with_block(with_stmt, outer_bindings, ctx)?;
    let begin = ctx.tag_image(Expr::begin(block), with_stmt.span);
    Ok(ctx.tag_machinery(
        Expr::expr_stmt(begin, continuation),
        with_stmt.span,
        "lower.stmt_seq",
    ))
}

/// Lower a `with begin():` block body to a per-transaction statement chain
/// ending in `Unit`, or in the block's value where `valued` — the `For` body `transact_phase`
/// reads to build the writer decision. Runs with `in_tx_body = true` (bare mutable variable
/// reads are snapshots).
fn lower_tx_block(
    stmts: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    span: Span,
    valued: bool,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if ctx.in_tx_body {
        return Err(LoweringError::unsupported(
            span,
            "nested `with begin():` transactions are not supported",
        ));
    }
    ctx.in_tx_body = true;
    let result = lower_tx_block_inner(stmts, outer_bindings, span, valued, ctx);
    ctx.in_tx_body = false;
    result
}

/// Build the block's statement chain right-to-left. Assignments to
/// transactional mutable variables become `MutWrite` markers (reads stay bare `Var`
/// snapshots); `if cond:` guards and `match` dispatch become `Case` (an `if`
/// without an `else` carries the deny branch); other assignments are
/// per-iteration `Let`s.
///
/// `fallback_span` anchors the manufactured chain terminal when the statement
/// list is empty (the block's own statement spans win when present).
///
/// Where `valued`, the last statement is the chain's terminal: its value is the block's
/// ([`lower_tx_tail`]).
fn lower_tx_block_inner(
    stmts: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    fallback_span: Span,
    valued: bool,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // A `with begin():` body is a block, so it declares its own type aliases.
    with_block_type_aliases(stmts, ctx, |ctx| {
        lower_tx_block_scoped(stmts, outer_bindings, fallback_span, valued, ctx)
    })
}

/// [`lower_tx_block_inner`] with the block's type aliases already in scope.
fn lower_tx_block_scoped(
    stmts: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    fallback_span: Span,
    valued: bool,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Multiple `if` guards, `elif` chains, `else` branches and `match` arms are all
    // supported: `transact_phase`'s path walk scopes each write to its own
    // control-flow path, rejoins each key with a carry-forward `Case`, and commits
    // on the disjunction of the write paths (see `src/ccl/design/mutability.md`).
    // A guard is not transaction-scoped — a spine write beside a branch commits
    // unconditionally.
    //
    // The chain terminal is manufactured sequencing (spanned to the block's
    // statements — the `with` construct when the block is empty).
    let block_span = match (stmts.first(), stmts.last()) {
        (Some(first), Some(last)) => first.span.join(last.span),
        _ => fallback_span,
    };
    let mut contributing = contributing_stmts(stmts).rev();
    let mut chain = if valued {
        let (_, last) = contributing
            .next()
            .ok_or_else(|| block_contributes_nothing(stmts))?;
        lower_tx_tail(last, outer_bindings, ctx)?
    } else {
        ctx.tag_machinery(Expr::lit(Lit::Unit), block_span, "lower.txn_unit")
    };
    for (_, stmt) in contributing {
        chain = match &stmt.node {
            // `balance := value` — the transactional mutable variable write. `:=` is the
            // sole variable-write operator; `write_or_let` gates it (a write to a
            // mutable variable commits; a `:=` to anything else is a
            // per-transaction local `let`).
            // `store[k] := value` — the keyed write, a write to one key of a
            // transactional collection. Never a local `let`: a subscript binds nothing,
            // so `write_or_let`'s fallback does not apply and the target must already
            // be a mutable variable.
            ChlStmt::MutAssign { target, value, .. }
                if matches!(target.node, AssignTarget::Subscript { .. }) =>
            {
                let AssignTarget::Subscript { target, index } = &target.node else {
                    unreachable!("guarded by the match arm above")
                };
                let write =
                    lower_keyed_write(target, index, value, &[], outer_bindings, stmt.span, ctx)?;
                ctx.tag_machinery(Expr::expr_stmt(write, chain), stmt.span, "lower.stmt_seq")
            }
            ChlStmt::MutAssign { target, value, .. } => {
                let name = extract_name_target(target, "mutable assignment")?;
                let val = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                write_or_let(name, val, chain, stmt.span, ctx)?
            }
            // `balance += value` — the compound-write shorthand, likewise a write.
            ChlStmt::AugAssign { target, op, value } => {
                let name = extract_name_target(target, "augmented assignment")?;
                let rhs = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                let val = lower_aug_binop(&name, *op, rhs, stmt.span, ctx)?;
                write_or_let(name, val, chain, stmt.span, ctx)?
            }
            ChlStmt::Assign { target, value, .. } if type_alias_decl(target, value).is_some() => {
                lower_type_alias_decl(target, stmt.span, chain, ctx)
            }
            // `x = value` — a plain immutable binding: a per-transaction local
            // `let`. `=` never writes a mutable variable; a plain `=` to a mutable variable would be
            // a silent no-op shadow that dies at block end, so reject it and point
            // at `:=`. (A genuine local shadowing the mutable variable's name is fine.)
            // A constructor pattern's names are each checked so.
            ChlStmt::Assign {
                target,
                value,
                transparency,
            } => {
                refuse_nested_sink(target, value, stmt.span)?;
                let assignment = AssignmentBindings::of(target, *transparency, stmt.span, ctx)?;
                for name in assignment.names() {
                    if !ctx.is_shadowed(&name) && ctx.is_transactional_mut_var(&name) {
                        return Err(LoweringError::unsupported(
                            stmt.span,
                            format!(
                                "write mutable variable `{name}` inside a `with begin():` block \
                                 with `:=` (`=` binds immutably — a plain `=` here is a no-op \
                                 shadow)"
                            ),
                        ));
                    }
                }
                let val = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                assignment.wrap(val, chain, stmt.span, ctx)
            }
            // `if cond: <writes>` — a conditional (deny) write. The no-else
            // branch is the deny: `commit = false` for the whole transaction.
            ChlStmt::If {
                branches,
                else_body,
            } => {
                let case = lower_tx_if(branches, else_body.as_deref(), outer_bindings, false, ctx)?;
                ctx.tag_machinery(Expr::expr_stmt(case, chain), stmt.span, "lower.stmt_seq")
            }
            // `out << e` inside the block — a per-commit feed. Its value reads
            // the read-your-writes snapshot at this point (a bare mutable variable read
            // resolves to the just-written value); `transact_phase` collects it
            // as a `__to_<defer>` tap on the writer decision and hoists a
            // `Feed(defer, __hist ▷ .__to_<defer>)` into the mutable variable body, so each
            // emission carries *its own* commit's value. Mirrors the induction
            // phase's in-loop feeds (see `src/ccl/mut_elim.rs`).
            ChlStmt::Expr(value) if matches!(&value.node, ChlExpr::Feed { .. }) => {
                let feed = lower_expr(value, ctx)?;
                ctx.tag_machinery(Expr::expr_stmt(feed, chain), stmt.span, "lower.stmt_seq")
            }
            // ``match m: case `tag(w): <writes>`` — tag dispatch, the `match`
            // counterpart of the `if` above. The arms share one first-match rule
            // over one `Case`, and `transact_phase` scopes each arm's writes to
            // its own path exactly as it does an `if` arm's. Arms partition the
            // tags, so there is no deny complement of the kind a bare `if cond:`
            // leaves — the trailing `true → unit` a `match` without a `case _:`
            // gains is minted by
            // [`tag_case_to_guard_case`](crate::ccl::ccl_utils::tag_case_to_guard_case),
            // not here.
            ChlStmt::Match { scrutinee, arms } => {
                let case = lower_match_over(
                    stmt.span,
                    scrutinee,
                    arms,
                    outer_bindings,
                    ctx,
                    |body, scope, ctx| lower_tx_block_inner(body, scope, stmt.span, false, ctx),
                )?;
                ctx.tag_machinery(Expr::expr_stmt(case, chain), stmt.span, "lower.stmt_seq")
            }
            // `raise e` — the rest of the block runs only where it does not raise, which
            // exception elimination decides.
            ChlStmt::Raise(value) => {
                let value = lower_expr(value, ctx)?;
                let raise = ctx.tag_image(
                    Expr::new(TypedExprNode::Raise {
                        value: Box::new(value),
                    }),
                    stmt.span,
                );
                ctx.tag_machinery(Expr::expr_stmt(raise, chain), stmt.span, "lower.stmt_seq")
            }
            // `try: … except T as e: …` — its blocks are write paths of the transaction, as a
            // `match`'s arms are.
            ChlStmt::Try { body, handlers } => {
                let attempt = lower_try_over(
                    stmt.span,
                    body,
                    handlers,
                    outer_bindings,
                    ctx,
                    |body, scope, _, ctx| lower_tx_block_inner(body, scope, stmt.span, false, ctx),
                )?;
                ctx.tag_machinery(Expr::expr_stmt(attempt, chain), stmt.span, "lower.stmt_seq")
            }
            ChlStmt::With { .. } => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "nested `with begin():` transactions are not supported",
                ));
            }
            ChlStmt::Expr(value) => {
                let effect = lower_expr(value, ctx)?;
                ctx.tag_machinery(
                    Expr::expr_stmt(effect, chain),
                    stmt.span,
                    EXPRESSION_STATEMENT,
                )
            }
            _ => {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "a `with begin():` block supports mutable writes (`x := …`, `x += …`), \
                     local bindings (`x = …`), `if cond:` guards, `match` dispatch, \
                     `raise` and `try`, and feeds (`out << e`). A declaration goes above the block, \
                     `@LoadFrom` included: its value is the predecessor's, read once \
                     at the swap",
                ));
            }
        };
    }
    Ok(chain)
}

/// The last statement of a `with begin():` block in value position, as the chain's terminal:
/// a bare expression is the value, and an `if`, `match` or `try` is a `Case` whose blocks
/// each end in one. Every other statement leaves the block without a value.
fn lower_tx_tail(
    stmt: &Spanned<ChlStmt>,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    match &stmt.node {
        ChlStmt::Expr(value) if !matches!(&value.node, ChlExpr::Feed { .. }) => {
            lower_expr(value, ctx)
        }
        ChlStmt::If {
            branches,
            else_body: Some(else_body),
        } => lower_tx_if(branches, Some(else_body), outer_bindings, true, ctx),
        ChlStmt::If { .. } => Err(LoweringError::unsupported(
            stmt.span,
            "a `with begin():` block whose value is used ends in an `if` with an `else`; \
             without one the block has no value where no guard holds",
        )),
        ChlStmt::Match { scrutinee, arms } => lower_match_over(
            stmt.span,
            scrutinee,
            arms,
            outer_bindings,
            ctx,
            |body, scope, ctx| lower_tx_block_inner(body, scope, stmt.span, true, ctx),
        ),
        ChlStmt::Try { body, handlers } => lower_try_over(
            stmt.span,
            body,
            handlers,
            outer_bindings,
            ctx,
            |body, scope, _, ctx| lower_tx_block_inner(body, scope, stmt.span, true, ctx),
        ),
        _ => Err(LoweringError::unsupported(
            stmt.span,
            "a `with begin():` block whose value is used ends in an expression, or in an \
             `if`, `match` or `try` whose blocks each end in one",
        )),
    }
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
/// (no writes), which `transact_phase` reads as `commit = false`. Where `valued`, the
/// `if` ends a block in value position and each branch ends in its value.
fn lower_tx_if(
    branches: &[IfBranch],
    else_body: Option<&[Spanned<ChlStmt>]>,
    outer_bindings: &HashSet<String>,
    valued: bool,
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
        let body =
            lower_tx_block_inner(&branch.body, outer_bindings, branch.cond.span, valued, ctx)?;
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
        Some(stmts) => lower_tx_block_inner(stmts, outer_bindings, guard_span, valued, ctx)?,
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

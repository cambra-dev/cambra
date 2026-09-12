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
    chl_parser::ast::{AssignTarget, Expr as ChlExpr, IfBranch, Span, Spanned, Stmt as ChlStmt},
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
    lower_tx_block(body, outer_bindings, with_stmt.span, ctx)
}

/// Lower a standalone `with begin(): <block>` (anywhere a statement can appear)
/// to `ExprStmt(For{__txn_item, [unit], Begin{<block>}}, continuation)` — one
/// commit over a synthesized singleton source (one item → one transaction). The
/// synthetic `For` gives `transact_phase` an enclosing loop to key the site on,
/// uniform with a per-iteration transaction inside a real loop.
pub(super) fn lower_standalone_transaction(
    with_stmt: &Spanned<ChlStmt>,
    continuation: Expr,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let block = lower_with_block(with_stmt, outer_bindings, ctx)?;
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
    outer_bindings: &HashSet<String>,
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
    let result = lower_tx_block_inner(stmts, outer_bindings, span, ctx);
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
/// snapshots); `if cond:` guards and `match` dispatch become `Case` (an `if`
/// without an `else` carries the deny branch); other assignments are
/// per-iteration `Let`s.
///
/// `fallback_span` anchors the manufactured chain terminal when the statement
/// list is empty (the block's own statement spans win when present).
fn lower_tx_block_inner(
    stmts: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    fallback_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // A `with begin():` body is a block, so it declares its own type aliases.
    with_block_type_aliases(stmts, ctx, |ctx| {
        lower_tx_block_scoped(stmts, outer_bindings, fallback_span, ctx)
    })
}

/// [`lower_tx_block_inner`] with the block's type aliases already in scope.
fn lower_tx_block_scoped(
    stmts: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    fallback_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // The chain terminal is manufactured sequencing (spanned to the block's
    // statements — the `with` construct when the block is empty).
    let block_span = match (stmts.first(), stmts.last()) {
        (Some(first), Some(last)) => first.span.join(last.span),
        _ => fallback_span,
    };
    let unit = ctx.tag_machinery(Expr::lit(Lit::Unit), block_span, "lower.txn_unit");
    lower_tx_stmts_onto(stmts, unit, outer_bindings, ctx)
}

/// [`lower_tx_block_scoped`]'s fold, over a caller-supplied `tail` rather than the
/// block's `Unit` terminal.
///
/// The terminal is a parameter because a `for` inside the block is expanded *into*
/// the chain ([`lower_tx_for`]): each copy of the loop body continues into the
/// statements after the loop, not into a `Unit` of its own. A block's own chain
/// ends in `Unit` because a block is a statement, and `lower_tx_block_scoped`
/// passes that.
fn lower_tx_stmts_onto(
    stmts: &[Spanned<ChlStmt>],
    tail: Expr,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Multiple `if` guards, `elif` chains, `else` branches and `match` arms are all
    // supported: `transact_phase`'s path walk scopes each write to its own
    // control-flow path, rejoins each key with a carry-forward `Case`, and commits
    // on the disjunction of the write paths (see `src/ccl/design/mutability.md`).
    // A guard is not transaction-scoped — a spine write beside a branch commits
    // unconditionally.
    let mut chain = tail;
    for stmt in stmts.iter().rev() {
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
            // `x = value` — a plain immutable binding: a per-transaction local
            // `let`. `=` never writes a mutable variable; a plain `=` to a mutable variable would be
            // a silent no-op shadow that dies at block end, so reject it and point
            // at `:=`. (A genuine local shadowing the mutable variable's name is fine.)
            // A type alias binds nothing, so the chain passes through unchanged.
            ChlStmt::Assign { target, value } if type_alias_decl(target, value).is_some() => chain,
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
                let val = lower_assigned_value(value, &[], outer_bindings, ctx)?;
                ctx.tag_image(Expr::let_bind(name, val, chain), stmt.span)
            }
            // `if cond: <writes>` — a conditional (deny) write. The no-else
            // branch is the deny: `commit = false` for the whole transaction.
            ChlStmt::If {
                branches,
                else_body,
            } => {
                let case = lower_tx_if(branches, else_body.as_deref(), outer_bindings, ctx)?;
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
                    |body, scope, ctx| lower_tx_block_inner(body, scope, stmt.span, ctx),
                )?;
                ctx.tag_machinery(Expr::expr_stmt(case, chain), stmt.span, "lower.stmt_seq")
            }
            // `for x in [a, b]: <writes>` — the loop, expanded into this chain
            // (see [`lower_tx_for`]). The expansion is why the arm produces the
            // whole remaining chain rather than one statement spliced before
            // `chain`: a copy of the body per element, each continuing into the
            // one after it and the last into the statements below the loop.
            ChlStmt::For {
                target,
                iter,
                guard,
                body,
            } => {
                let body = &guarded_body(guard, body);
                lower_tx_for(target, iter, body, chain, outer_bindings, stmt.span, ctx)?
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
                     local bindings (`x = …`), `if cond:` guards, `match` dispatch, \
                     `for` loops over a list literal, and feeds (`out << e`)",
                ));
            }
        };
    }
    Ok(chain)
}

/// Lower a `for x in [e₀, …, eₙ₋₁]: <body>` **inside** a `with begin():` block by
/// expanding it into the block's statement chain: one copy of the body per
/// element, the binder a `Let` over that copy, the last copy continuing into
/// `tail` (the statements below the loop).
///
/// # The loop is a fold over the block's read-your-writes environment
///
/// A block denotes one decision — `snapshot ⇒ {`commit{writes} | `abort}` — whose
/// per-key write is a **term over that one snapshot**
/// (`src/ccl/design/mutability.md`, "A `for` inside a block (over a list
/// literal)"). A loop inside the block is therefore a fold: iteration *i* runs
/// the body against the environment iterations `0..i` left, and the block
/// continues from the environment the last one left. Nothing about that is new machinery —
/// `transact_phase::walk_block` already threads exactly this environment through a
/// straight-line chain of `Let`s and `MutWrite`s, and read-your-writes through the
/// expansion is the same substitution it does between two sibling statements. That
/// is the whole reason the loop is expanded *here*, in lowering, rather than
/// carried into the phase as a marker node: the fold's meaning is a chain of
/// statements, so writing it as one leaves every downstream rule (the path walk,
/// the per-key carry-forward `Case`, the `__to_<defer>` feed taps, the dense commit
/// payload) applying unchanged, with no arm to add anywhere below.
///
/// # The commit condition is the loop's position, never its length
///
/// The writes a loop body performs commit on the path condition of the statement
/// position the `for` occupies — the enclosing guard, or `true` on the spine —
/// exactly as if the body had been written out by hand. A loop that iterates zero
/// times contributes no write and no feed, and so contributes nothing to the
/// commit disjunction; it does **not** deny the transaction. Two independent
/// reasons, and either alone settles it:
///
/// - The `commit` payload is dense: an unwritten key on a committing path carries
///   its snapshot value, a no-op re-write. "The loop ran zero times" and "the loop
///   wrote every key back unchanged" are therefore the same observation, so a
///   zero-iteration loop cannot be allowed to change the grant/deny tag.
/// - A path condition is a `Bool` term over the snapshot. A source's cardinality is
///   not such a term, so "the loop is non-empty" is not a condition the decision
///   could carry even if we wanted it to.
///
/// This is the same rule a spine write beside a false guard follows (`commit =
/// p ∨ true`, pinned by `spine_write_commits_beside_false_guard`): a construct
/// that writes nothing neither grants nor denies on its own.
///
/// # Why the source must be a list literal
///
/// Because the decision is one term, the fold has to be **finitely denoted**, and
/// the only finite denotation available is the expansion above — there is no fold
/// term in the algebra to defer to. A source whose length is known only at runtime
/// would need the block's write for a key to be `merge(snapshot, ⟨the loop's
/// contribution⟩)`: a bulk keyed update, built per transaction from a collection
/// the snapshot itself supplies. Neither half exists — there is no merge builtin
/// (`Builtin::Insert` writes one key), and a comprehension inside a block that
/// reads the snapshot does not survive op-conversion today. Rejecting the source
/// outright, rather than silently accepting the literal case under a general-looking
/// syntax, is what keeps that gap visible; `src/ccl/design/mutability.md` carries
/// the shape the general case wants.
///
/// The binder shadows a like-named transactional mutable variable over the body
/// (`with_shadowed`), as every other binding site does, and the body is a block, so
/// it declares its own type aliases.
fn lower_tx_for(
    target: &Spanned<AssignTarget>,
    iter: &Spanned<ChlExpr>,
    body: &[Spanned<ChlStmt>],
    tail: Expr,
    outer_bindings: &HashSet<String>,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let iter_var = extract_name_target(target, "for-loop target")?;
    let ChlExpr::List(elements) = &iter.node else {
        return Err(LoweringError::unsupported(
            iter.span,
            "a `for` inside a `with begin():` block iterates a list literal \
             (`for x in [a, b]:`): the block is one decision over one snapshot, so the \
             loop is expanded into it at compile time and its elements have to be \
             written out. A source whose length is only known at runtime needs a bulk \
             keyed update (`m := merge(m, …)`), which does not exist yet",
        ));
    };
    // Every element expression is lowered here, in the scope *around* the loop and
    // in source order — a source is evaluated once, before the binder exists, and
    // minting synthetic names in the order the user wrote them keeps a lowering log
    // readable. The expansion below walks them backwards, which is a property of
    // building a statement chain right-to-left, not of the source.
    let values: Vec<Expr> = elements
        .iter()
        .map(|element| lower_expr(element, ctx))
        .collect::<Result<_, _>>()?;

    // The binder is in scope over the body for the same reason a `let` above the
    // loop would be: a nested block value (`x = if …:`) lowered inside the body
    // resolves names against it.
    let mut scope = outer_bindings.clone();
    scope.insert(iter_var.clone());

    let mut chain = tail;
    for value in values.into_iter().rev() {
        let continuation = chain;
        let copy = ctx.with_shadowed([iter_var.clone()], |ctx| {
            with_block_type_aliases(body, ctx, |ctx| {
                lower_tx_stmts_onto(body, continuation, &scope, ctx)
            })
        })?;
        // Each copy's binder images the `for` statement: it is the loop target,
        // bound to the one element this copy runs for.
        chain = ctx.tag_image(Expr::let_bind(iter_var.clone(), value, copy), span);
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
    outer_bindings: &HashSet<String>,
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
        let body = lower_tx_block_inner(&branch.body, outer_bindings, branch.cond.span, ctx)?;
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
        Some(stmts) => lower_tx_block_inner(stmts, outer_bindings, guard_span, ctx)?,
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

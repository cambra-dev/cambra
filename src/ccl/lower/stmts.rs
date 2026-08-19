//! Statement-block lowering: `Let` chains, `if`/`else`, the `http_serve`
//! tuple-assign wiring, and mutation-loop dispatch.

use std::{cell::RefCell, collections::HashSet, rc::Rc, sync::Arc};

use super::*;
use crate::{
    ccl::{BaseType, Branch, Expr, FieldKey, Lit, Pattern, Type, TypedBinding, TypedExprNode},
    chl_parser::ast::{
        AnnotationMode, AssignTarget, BinOp as ChlBinOp, IfBranch, MatchArm, PayloadPattern, Span,
        Spanned, Stmt as ChlStmt, TypeAnnotation,
    },
    interpreter::{DataSink, HttpServerDataSource, http_server::SharedHttpServer},
};

/// Top-level statement-iteration with per-statement error recovery.
///
/// Differs from [`lower_stmts_inner`] (used by nested blocks) in that an error
/// on any single statement is recorded into `errors`, a placeholder
/// [`TypedExprNode::Error`] is substituted, and lowering continues on the
/// remaining statements. The result is therefore a best-effort tree whose
/// validity depends on `errors` being empty.
///
/// The sink-bindings record-wrap from the original `lower_stmts` is still
/// applied around the recovered tree.
pub(super) fn lower_stmts_recovering(
    stmts: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
    errors: &mut Vec<LoweringError>,
) -> Option<Expr> {
    if stmts.is_empty() {
        // Defensive catch-all for callers that bypass [`compile_program`]'s
        // empty-program short-circuit (which emits a properly-spanned error).
        // We cannot synthesise a meaningful span here because we don't see the
        // source string — the file's only feature is its emptiness.
        errors.push(LoweringError::unsupported(
            Span::new(0, 0),
            "empty program: file contains no top-level statements",
        ));
        return None;
    }
    let outer_bindings = HashSet::new();
    // Pre-register transactional mutable variables and `Mut`-parameter `def`s in this
    // (top-level) block before lowering right-to-left: a call site or a
    // variable-writing loop is lowered before the `:=` / `def` that precedes it
    // textually. (No transactional-registry snapshot here — the top level is the
    // outermost scope, so nothing to restore to.)
    pre_register_txn_decls(stmts, ctx);
    let (last, rest) = stmts.split_last().unwrap();

    // Final statement: recover by substituting Expr::error() on failure.
    let final_expr = match lower_final_stmt(last, rest, &outer_bindings, ctx) {
        Ok(e) => e,
        Err(e) => {
            errors.push(e);
            Expr::error()
        }
    };

    // Middle statements: each call takes ownership of `acc` (the continuation
    // we've built so far), so when one fails we need a snapshot to fall back
    // to. Cloning unconditionally is fine — lowering isn't a hot path and
    // errors are exceptional.
    //
    // The snapshot preserves ids, and must. It is a *rollback copy*, not a
    // sibling: at most one of `acc` and `backup` ever reaches the tree.
    //
    // TODO(rollback-copy): ripe for refactoring — this is quadratic. The
    // continuation grows with every statement and is copied whole for each one,
    // so a clean compile of an n-statement program does O(n^2) node copies for a
    // value the happy path drops. Preserving ids keeps it off the *id* ledger
    // (a freshening clone would deep-mint all of it), but the copy itself
    // remains. The fix is to stop needing a snapshot: have `lower_middle_stmt`
    // borrow, or return the continuation back on the error path, so recovery
    // costs nothing when nothing fails.
    let body = rest
        .iter()
        .enumerate()
        .rev()
        .fold(final_expr, |acc, (i, stmt)| {
            let backup = acc.clone_preserving_ids();
            match lower_middle_stmt(stmt, &rest[..i], acc, &outer_bindings, ctx, true) {
                Ok(e) => e,
                Err(e) => {
                    errors.push(e);
                    // Wrap with a placeholder ExprStmt so the continuation
                    // (`backup`) and any later siblings remain reachable in
                    // the partial tree. The tree is not consumed past
                    // lowering when errors are present, so the placeholder's
                    // role is purely structural.
                    Expr::expr_stmt(Expr::error(), backup)
                }
            }
        });

    if ctx.sink_bindings.is_empty() {
        return Some(body);
    }

    // Build a Record whose fields are the sink-bound names in sorted order
    // (sort for determinism — HashMap iteration is unordered). The record, its
    // field `Var`s, and the tail `ExprStmt` are program-owned plumbing with no
    // owning statement; they carry the whole-program span.
    let program_span = stmts[0].span.join(stmts[stmts.len() - 1].span);
    let mut sink_names: Vec<String> = ctx.sink_bindings.keys().cloned().collect();
    sink_names.sort();
    let fields = sink_names
        .iter()
        .map(|n| {
            let var = ctx.tag_machinery(Expr::var(n), program_span, "lower.sink_record");
            (n.clone(), var)
        })
        .collect();
    let record = ctx.tag_machinery(
        Expr::new(TypedExprNode::Record(fields)),
        program_span,
        "lower.sink_record",
    );
    // Place ExprStmt(body, record) at the innermost position of the Let* chain
    // so the Record has the sink Var references in scope.
    Some(append_record_at_tail(body, record, program_span, ctx))
}

/// Walk to the innermost non-`Let`/`ExprStmt` continuation and wrap it with
/// `ExprStmt(current_tail, record)`.
///
/// Recurses through both `Let` and `ExprStmt` nodes: a for-loop in the middle
/// of the program produces an `ExprStmt(effect, continuation)` where the
/// continuation may contain further `Let` bindings from later `http_serve`
/// calls.  Stopping at the first `ExprStmt` would place the `Record` outside
/// those inner bindings, making their names unbound.
///
/// The `ExprStmt` node "drives the feed": `simplify` drops it once
/// [`crate::ccl::channelize`] has extracted all `Feed` nodes from the body,
/// leaving a clean `Let* Record{…}` shape that `compile_program` can pattern-match on.
fn append_record_at_tail(
    expr: Expr,
    record: Expr,
    program_span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    match expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_body = append_record_at_tail(*body, record, program_span, ctx);
            Expr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(new_body),
                },
                ..expr
            }
        }
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            let new_body = append_record_at_tail(*body, record, program_span, ctx);
            Expr {
                node: TypedExprNode::MutDecl {
                    binding,
                    init,
                    body: Box::new(new_body),
                },
                ..expr
            }
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            let new_body = append_record_at_tail(*body, record, program_span, ctx);
            Expr {
                node: TypedExprNode::ExprStmt {
                    expr: effect,
                    body: Box::new(new_body),
                },
                ..expr
            }
        }
        // Terminal continuation: wrap with ExprStmt so simplify can drop it.
        _ => ctx.tag_machinery(
            Expr::expr_stmt(expr, record),
            program_span,
            "lower.sink_record",
        ),
    }
}

/// Core implementation of [`lower_stmts`] that threads an `outer_bindings`
/// set — names already in scope above this statement block (e.g., function
/// parameters). The generator-lowering path uses this to detect mutation
/// (reassignment of variables from enclosing scopes).
///
/// `is_top_level` is `true` only for the outermost call from [`lower_stmts`].
/// It is `false` for if/else arms and function bodies so that `http_serve`
/// assignments are rejected outside the top-level program scope.
pub(super) fn lower_stmts_inner(
    stmts: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
    is_top_level: bool,
) -> Result<Expr, LoweringError> {
    // The CHL `block` parser uses `.at_least(1)`, so nested blocks always have
    // at least one statement by the time they reach us.
    assert!(
        !stmts.is_empty(),
        "lower_stmts_inner: empty nested block (parser invariant violated)"
    );

    // A nested block is its own scope: snapshot *both* the transactional
    // registry and the `mut_param_fns` set so declarations local to this block —
    // a `Mut(…, Txn)` mutable variable, or a `Mut`-param `def`'s curried call shape —
    // revert on exit and do not leak into an enclosing or sibling scope.
    // Induction mutability carries no lowering-time registry (it is the
    // `Type::History` on the binding, checked post-inference). This block's
    // `def`s still shadow outer same-named ones *within* the block (pre-registration
    // overwrites them here; the restore reinstates the outer ones on exit).
    // Restored on both the success and error paths below.
    let snapshot = ctx.snapshot_transactional();
    let saved_mut_param_fns = ctx.mut_param_fns.clone();
    pre_register_txn_decls(stmts, ctx);
    let (last, rest) = stmts.split_last().unwrap();

    // The final statement must be a bare expression, an if/else block, or
    // a for-loop that contains a yield chain (generator pattern). Wrap the
    // preceding assignments and function definitions in Let bindings,
    // innermost-first. (Mutability is carried by `Type::History` and checked
    // post-inference; introduction-vs-write is decided by lexical scope.)
    let result = lower_final_stmt(last, rest, outer_bindings, ctx).and_then(|final_expr| {
        rest.iter()
            .enumerate()
            .rev()
            .try_fold(final_expr, |acc, (i, stmt)| {
                lower_middle_stmt(stmt, &rest[..i], acc, outer_bindings, ctx, is_top_level)
            })
    });
    ctx.restore_transactional(snapshot);
    ctx.mut_param_fns = saved_mut_param_fns;
    result
}

/// Lower the final statement in a block, which must be a bare expression, an if/else block,
/// or a for-loop with a yield chain (generator pattern).
pub(super) fn lower_final_stmt(
    last: &Spanned<ChlStmt>,
    preceding: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    match &last.node {
        ChlStmt::Expr(value) => lower_expr(value, ctx),
        ChlStmt::If {
            branches,
            else_body,
        } => {
            // Propagate outer bindings + rest names so that generator-fors
            // inside the if branches can check for mutation correctly.
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);
            lower_if(last.span, branches, else_body.as_deref(), &scope, ctx)
        }
        ChlStmt::Match { scrutinee, arms } => {
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);
            lower_match(last.span, scrutinee, arms, &scope, ctx)
        }
        ChlStmt::For {
            target,
            iter,
            body: for_body,
        } => {
            // Build outer bindings: caller's bindings + all names from rest.
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);
            // A non-yielding loop that mutates a declared `Mut(…)`
            // accumulator is a valid *final* statement — the loop runs and its
            // final mutable-variable value is simply unobserved (`Unit`). Mirror
            // `lower_middle_stmt`'s mutation-loop dispatch here, with `Unit` as
            // the continuation. This subsumes the feed-only accumulator (an
            // HTTP loop whose `<<` reply is not a `yield`, which
            // `lower_generator_for`'s yield-gated mutation path would miss). (A
            // *yielding* loop — a generator, with or without loop-carried
            // mutation — falls through to `lower_generator_for`, whose value is
            // the collected yields; a bare non-accumulating loop keeps its
            // existing "must end in a yield/feed" rejection there too.)
            if !for_body_has_yield(for_body) {
                // Any `:=` / `+=` to an outer-scope name is a loop-carried mutable
                // write (mutability is checked post-inference; a non-mutable write
                // is rejected there, not here). A plain `=` to an outer name is
                // caught separately by the generator path below.
                let acc_names = find_mutation_loop_vars(for_body, &scope);
                if !acc_names.is_empty() || for_body_has_with(for_body) {
                    let unit =
                        ctx.tag_machinery(Expr::lit(Lit::Unit), last.span, "lower.loop_unit");
                    return lower_generator_or_mutation_loop(
                        target, iter, for_body, &acc_names, unit, last.span, ctx,
                    );
                }
                // Mirror `lower_middle_stmt`'s remaining mutation guards before
                // the hidden-writer fallback below — the final-position path must
                // reject the same mistaken shapes, not silently swallow them as
                // no-op `For`s. A *nested* mutation of an outer name (under an
                // `if`/inner `for`) is unsupported; a *plain* `=` to an outer name
                // is a mistaken accumulator (`=` binds immutably, so it would be a
                // per-iteration shadow silently discarding each update). Both
                // otherwise reach the bare-effect hidden-writer path and compile
                // to a silent no-op — the exact gap the generator path catches
                // when a trailing read makes the loop non-final.
                if let Some(nested) = find_nested_mutation_var(for_body, &scope) {
                    return Err(LoweringError::unsupported(
                        last.span,
                        format!(
                            "mutation of `{nested}` is nested inside an inner \
                             `for` in this for-loop body; nested-loop mutation \
                             is not yet supported (a conditional `if p: \
                             {nested} += …` write is supported — only an inner \
                             `for` is not).  Move the mutation to the outer loop \
                             body, or rewrite using a generator expression."
                        ),
                    ));
                }
                if let Some(name) = first_outer_plain_assign(for_body, &scope) {
                    return Err(outer_binding_write_error(last.span, name));
                }
                // A non-yielding, non-feeding loop whose body's terminal
                // statement is a bare *effect* expression — a call that may hide
                // a pass-by-reference mutable write (`for x in xs: bump(cnt)`),
                // invisible pre-inference — is a valid final statement: the loop
                // runs and its mutable-variable value is simply unobserved (`Unit`). Mirror
                // `lower_middle_stmt`'s hidden-writer path (with `Unit` as the
                // continuation) and let the letrec phase classify it (a call that
                // beta-reduces to a `MutWrite` → an accumulator; a pure body → a
                // dropped no-op). Without this it wrongly hit the generator path's
                // "must end in a yield/feed" rejection. A terminal that reassigns
                // the loop variable (`x += 1`) or a non-mutable is *not* a bare
                // effect, so it stays rejected by the generator path below — it is
                // a likely-mistaken no-op, not a hidden writer.
                if !for_body_has_feed(for_body) && for_body_terminal_is_bare_effect(for_body) {
                    let unit =
                        ctx.tag_machinery(Expr::lit(Lit::Unit), last.span, "lower.loop_unit");
                    return lower_direct_mirror_loop(
                        target,
                        iter,
                        for_body,
                        &[],
                        unit,
                        None,
                        last.span,
                        ctx,
                    );
                }
            }
            lower_generator_for(target, iter, for_body, &scope, last.span, ctx)
        }
        // A `+=` as the final statement is a mutable write — a pass-by-reference
        // writer body (`def bump(c): c += 1`) or a program ending in a mutable-variable
        // update with no trailing read. Emit a *bare* `MutWrite` (no
        // continuation) so inlining splices it into the caller's sequence and
        // the letrec phase normalizes it; the check requires the target to be a
        // mutable variable. (A plain `=` is an immutable binding and reaches the
        // "must end in a value" error below, never this arm.)
        ChlStmt::AugAssign { target, op, value } => {
            let name = extract_name_target(target, "augmented assignment")?;
            check_mut_write_context(&name, last.span, ctx)?;
            let val = lower_aug_binop(&name, *op, value, last.span, ctx)?;
            Ok(ctx.tag_image(Expr::mut_write(name, val), last.span))
        }
        // A bare `x := e` as the final statement is a mutable-variable *write* when `x` is
        // already in scope (a mutation-loop body's terminal write, an inlined
        // pass-by-ref writer, or a program ending in a mutable-variable update): a bare
        // `MutWrite` the letrec phase normalizes. A `:=` *introduction* (a fresh
        // name) can't be a value-producing final statement — it falls through to
        // the "must end in a value" error. Mutability is checked post-inference.
        ChlStmt::MutAssign {
            target,
            annotation: None,
            value,
        } if name_target_as_name(target).is_some_and(|n| {
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);
            scope.contains(n)
        }) =>
        {
            let name = extract_name_target(target, "mutable assignment")?;
            check_mut_write_context(&name, last.span, ctx)?;
            let val = lower_expr(value, ctx)?;
            Ok(ctx.tag_image(Expr::mut_write(name, val), last.span))
        }
        // A standalone `with begin():` as the program's final statement: one
        // transaction whose value is `Unit` (a trailing transaction produces no
        // value — its replies ride the feed, and a program that wants a committed
        // value reads it inside a `with begin():` block that feeds it out).
        ChlStmt::With { .. } => {
            let unit = ctx.tag_machinery(Expr::lit(Lit::Unit), last.span, "lower.txn_unit");
            lower_standalone_transaction(last, unit, ctx)
        }
        // Parse-recovery placeholder: silently substitute. See `ChlExpr::Error`.
        ChlStmt::Error => Ok(Expr::error()),
        _ => Err(LoweringError::unsupported(
            last.span,
            "last statement must be a bare expression, if/else, or \
                 for/yield generator loop",
        )),
    }
}

/// Lower a single statement in the middle of a block.
/// This is usually some sort of let-binding, but can also be a bare expression
///
/// `stmt` is the current statement to be lowered
/// `preceding` are the statements that come before `stmt` in the block
/// `body` is the already-lowered expression for the rest of the block after `stmt`
/// `outer_bindings` are the names already in scope above this block (e.g., function parameters)
/// `is_top_level` is `false` inside if/else arms and function bodies; `http_serve` is only
/// permitted at the top level of a program.
pub(super) fn lower_middle_stmt(
    stmt: &Spanned<ChlStmt>,
    preceding: &[Spanned<ChlStmt>],
    body: Expr,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
    is_top_level: bool,
) -> Result<Expr, LoweringError> {
    match &stmt.node {
        // Special case: `requests, responses = http_serve(port, method, path)`.
        //
        // Lowers to:
        //   let <requests> = Source("__http_requests_N") in
        //   let <responses> = Defer              in
        //   <body>
        // TODO we shouldn't need to special-case this.  Instead, we should support multi-return
        // in general.
        ChlStmt::Assign { target, value } if is_http_serve_tuple_assign(target, value) => {
            if !is_top_level {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    "http_serve is only supported at the top level of a program, \
                     not inside an if/else branch or function body",
                ));
            }
            let (req_name, resp_name) = extract_http_serve_names(target)?;
            let (port, method, path) = extract_http_serve_args(value)?;
            // Create and mutable variable the source now; the caller drains new_sources
            // via take_new_sources() after lower_stmts returns, before type inference.
            let port_u16: u16 = port.parse().map_err(|_| {
                LoweringError::unsupported(
                    value.span,
                    format!("http_serve port must be a u16, got {port:?}"),
                )
            })?;
            // Share one tiny_http::Server per port across all http_serve routes.
            if let std::collections::hash_map::Entry::Vacant(e) = ctx.shared_servers.entry(port_u16)
            {
                let server = SharedHttpServer::new(port_u16).map_err(|e| {
                    LoweringError::unsupported(
                        value.span,
                        format!("http_serve: failed to bind port {port_u16}: {e}"),
                    )
                })?;
                e.insert(Arc::new(server));
            }
            let server = ctx.shared_servers[&port_u16].clone();
            let source_name = http_requests_source_name(&port, &method, &path);
            if ctx.sources.contains_key(&source_name) {
                return Err(LoweringError::unsupported(
                    value.span,
                    format!(
                        "duplicate http_serve registration: port={port}, method={method}, path={path}"
                    ),
                ));
            }
            let source_obj = Rc::new(RefCell::new(HttpServerDataSource::new(
                &server,
                method.clone(),
                path.clone(),
                source_name.clone(),
            )));
            let sink: Arc<dyn DataSink> = source_obj.borrow().sink();
            ctx.sources.insert(source_name.clone(), source_obj);
            let requests_expr = ctx.tag_machinery(
                Expr::new(TypedExprNode::Source(source_name.clone())),
                stmt.span,
                "lower.http_serve",
            );
            // The responses binding is a plain Defer; the sink is registered by
            // binding name so the scheduler can subscribe it independently.
            let responses_expr = ctx.tag_machinery(
                Expr::new(TypedExprNode::Defer),
                stmt.span,
                "lower.http_serve",
            );
            ctx.register_sink_binding(resp_name.clone(), sink);
            // The outer `requests` binding images the assignment statement (the
            // real source construct); the inner `responses` Defer let, the
            // Source node, and the Defer are manufactured plumbing of the
            // http_serve expansion.
            let inner_let = ctx.tag_machinery(
                Expr::let_bind(resp_name, responses_expr, body),
                stmt.span,
                "lower.http_serve",
            );
            let let_expr = Expr::let_bind(req_name, requests_expr, inner_let);
            Ok(ctx.tag_image(let_expr, stmt.span))
        }
        // `x = e` — a plain immutable binding: a shadowing `let`. `=` is never a
        // mutable write (the mutation operators are `:=` and `+=`), so even a
        // top-level `=` to a name that is *also* a live mutable variable just shadows it.
        ChlStmt::Assign { target, value } => {
            let name = extract_name_target(target, "assignment")?;
            let val = lower_expr(value, ctx)?;
            Ok(ctx.tag_image(Expr::let_bind(name, val, body), stmt.span))
        }
        ChlStmt::AnnAssign {
            target,
            annotation,
            value,
        } => {
            let name = extract_name_target(target, "annotated assignment")?;
            if mut_annotation_parts(&annotation.ty, ctx).is_some() {
                // `x: Mut(V) = init` / `x: Mut(V, Txn) = init` — a `Mut`
                // annotation with the *immutable* `=` operator. This is
                // contradictory under the cutover: `=` is a plain immutable
                // binding, and every mutable (induction or transactional) is
                // introduced solely with `:=`. Reject and point at `:=` (the
                // value type — and `Txn` — still ride the annotation:
                // `x: Mut(V) := init`, `x: Mut(V, Txn) := init`).
                return Err(LoweringError::unsupported(
                    stmt.span,
                    format!(
                        "`{name}: Mut(…) = …` introduces a mutable with the immutable \
                         `=` operator; use `:=` instead (e.g. `{name}: Mut(V) := init`, \
                         `{name}: Mut(V, Txn) := init`, or a bare `{name} := init` to \
                         infer the value type)"
                    ),
                ));
            }
            let annotation_ty = lower_type_annotation(annotation, ctx)?;
            let val = lower_expr(value, ctx)?;
            Ok(ctx.tag_image(
                Expr::let_bind_annotated(name, val, body, annotation_ty),
                stmt.span,
            ))
        }
        // `x := e` — a mutable **introduction** or **write**, split by scope:
        //  - a bare `x := e` where `x` is already in scope is a *write* — a
        //    `MutWrite` marker (which the check requires to target a mutable variable, and
        //    the unified phase normalizes: a recurrence in a loop, a shadowing
        //    advance at the top level);
        //  - otherwise (a fresh name, or an annotated `x: T := e` / `x: Mut(V) := e`
        //    declaration) it is an *introduction* — a `let` whose binding is
        //    stamped `Mut(V, _)` so inference binds `x` at `Mut` and reads deref
        //    (domain inferred for an induction accumulator).
        // In-loop writes are handled by `lower_direct_mirror_loop`, not here.
        ChlStmt::MutAssign {
            target,
            annotation,
            value,
        } => {
            let name = extract_name_target(target, "mutable assignment")?;
            // A *bare* `x := e` (no annotation) to an already-live mutable variable is a
            // write / sequential re-bind, not a declaration: gate it like any
            // mutable write. A transactional mutable variable written here (outside a
            // `with begin():` block) is rejected; an induction accumulator re-bind
            // passes (`check_mut_write_context` is a no-op for it). An
            // *annotated* `:=` is the introduction and needs no gate.
            if annotation.is_none() {
                check_mut_write_context(&name, stmt.span, ctx)?;
            }
            let val = lower_expr(value, ctx)?;
            // A bare `x := e` where `x` is already in scope is a *write*, not a
            // declaration: emit a `MutWrite` marker (mutability checked
            // post-inference; the unified phase turns it into a recurrence in a
            // loop or a shadowing advance at the top level). A transactional
            // mutable variable write here was already rejected by
            // `check_mut_write_context` above (a mutable variable write must sit inside
            // a `with begin():` block).
            if annotation.is_none() {
                let mut scope = outer_bindings.clone();
                collect_stmt_names(preceding, &mut scope);
                if scope.contains(&name) {
                    // The `MutWrite` is the image of `x := e`; the `ExprStmt`
                    // that sequences it onto the rest of the block is
                    // manufactured — the user wrote no sequencing operator. Two
                    // `"lower.image"` tags at one `stmt.span` would have two
                    // nodes each claiming to be the image of one statement.
                    let write = ctx.tag_image(Expr::mut_write(name, val), stmt.span);
                    return Ok(ctx.tag_machinery(
                        Expr::expr_stmt(write, body),
                        stmt.span,
                        "lower.stmt_seq",
                    ));
                }
            }
            // Otherwise this is an *introduction*. Resolve the optional
            // annotation to `(value type, transactional?)`:
            //   (none)                → induction accumulator, value type inferred
            //   `x: Mut(V) := e`      → induction accumulator at value type `V`
            //   `x: Mut(V, Txn) := e` → transactional mutable variable at value type `V`
            //
            // Those are the only forms: an annotation on a `:=` binder is exact and
            // is a `Mut(…)` (`check_mut_decl_annotation`).
            let (value_ty, is_txn) = match annotation {
                None => (Type::Hole, false),
                Some(ann) => check_mut_decl_annotation(&name, ann, stmt.span, ctx)?,
            };
            // Stamp the binding `Mut(V, D)` (so inference binds `x` at `Mut` and
            // its references deref to `V`). `D = Txn` for a transactional mutable variable
            // (fixed here, never inferred), which also mutable variables `x` so its
            // `with begin():` writes lower to `MutWrite` and its bare reads are
            // gated. An induction accumulator gets `D = Hole` and carries *no* lowering
            // registry — its mutability is this `Mut` type, checked
            // post-inference; its domain is the loop it accumulates over, which
            // the unified phase resolves. See src/ccl/design/mutability.md.
            let domain = if is_txn {
                ctx.register_transactional(name.clone());
                Type::Txn
            } else {
                Type::Hole
            };
            let mut_ty = Type::History {
                value: Box::new(value_ty),
                domain: Box::new(domain),
                kind: crate::ccl::HistoryKind::Overwrite,
            };
            Ok(ctx.tag_image(Expr::mut_decl(name, mut_ty, val, body), stmt.span))
        }
        // Desugar `x op= e` → `MutWrite(x, x op e)`. `+=` is a mutable write: the
        // check requires `x` to be a mutable variable (never a shadowing rebind of
        // an immutable), and the unified phase turns the marker into a recurrence
        // (in a loop) or a shadowing advance (outside one). Only simple name
        // targets are supported; tuple-destructuring `(a, b) += …` is Unsupported.
        ChlStmt::AugAssign { target, op, value } => {
            let name = extract_name_target(target, "augmented assignment")?;
            // A `+=` to a transactional mutable variable outside a `with begin():` block
            // is rejected here (a mutable variable write must commit inside a block);
            // otherwise it is a bare mutable write whose target-is-a-mutable check
            // runs post-inference.
            check_mut_write_context(&name, stmt.span, ctx)?;
            let val = lower_aug_binop(&name, *op, value, stmt.span, ctx)?;
            let write = ctx.tag_image(Expr::mut_write(name, val), stmt.span);
            Ok(ctx.tag_image(Expr::expr_stmt(write, body), stmt.span))
        }
        // `x <<= e` — defer-define statement, distinct from AugAssign.
        ChlStmt::Define { target, value } => {
            let lowered = lower_define(target, value, ctx)?;
            let define = ctx.tag_image(lowered, stmt.span);
            Ok(ctx.tag_image(Expr::expr_stmt(define, body), stmt.span))
        }
        // Function definition → Let binding with curried lambda body.
        ChlStmt::FunctionDef {
            name,
            params,
            output,
            body: fn_body,
        } => {
            let func_expr = lower_function_body(stmt.span, params, output.as_ref(), fn_body, ctx)?;
            Ok(ctx.tag_image(
                Expr::let_bind(name.as_str().to_string(), func_expr, body),
                stmt.span,
            ))
        }
        // For a for-loop in the middle of a block, check whether it is a mutation
        // accumulation loop (lowered to `Loop`) or a side-effecting streaming
        // loop (lowered to Compose + expr_stmt).
        ChlStmt::For {
            target,
            iter,
            body: for_body,
            ..
        } => {
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);

            // Detect a mutation loop: at least one `:=` / `+=` to a variable
            // from the outer scope.  Yields are not a barrier — a generator with
            // loop-carried state (the mutability design notes' §4b `running_totals` shape) is
            // just a mutation loop whose body also feeds an auto-generated defer.
            // The surrounding `body` (the continuation) is threaded into
            // `lower_mutation_loop` so it can lift post-mutation feeds outside
            // the loop and wrap the continuation. Mutability of each write is
            // checked post-inference; a `:=` / `+=` to a non-mutable surfaces there.
            let acc_names = find_mutation_loop_vars(for_body, &scope);
            if !acc_names.is_empty() || for_body_has_with(for_body) {
                // All such loops — mutation accumulators, per-iteration
                // `with begin():` transactions, and mixes of both (plus their
                // feeds/yields) — take the direct-mirror `For` path; the unified
                // phases (src/ccl/design/mutability.md) build the recurrence,
                // strip each `Begin` into a commit site, and hoist feeds.
                return lower_generator_or_mutation_loop(
                    target, iter, for_body, &acc_names, body, stmt.span, ctx,
                );
            }
            // Top-level scan found nothing, but a *nested* `if` or
            // `for` may still mutate an outer-scope variable — we
            // don't yet support either of those (nested-for is
            // future work; mutations under `if` need refinement
            // propagation).  Reject early with a specific message
            // so users don't see the generic "must end in yield"
            // error from the generator-for fallback below.
            if let Some(nested) = find_nested_mutation_var(for_body, &scope) {
                return Err(LoweringError::unsupported(
                    stmt.span,
                    format!(
                        "mutation of `{nested}` is nested inside an inner `for` \
                     in this for-loop body; nested-loop mutation is not yet \
                     supported (a conditional `if p: {nested} += …` write is \
                     supported — only an inner `for` is not).  Move the mutation \
                     to the outer loop body, or rewrite using a generator \
                     expression."
                    ),
                ));
            }

            // A plain `=` to a name bound *outside* the loop is not a mutable variable
            // write — `=` binds immutably, so it would be a per-iteration
            // shadow that silently discards each update (a mistaken
            // accumulator). The hidden-writer path below would accept it as a
            // no-op `For`, so reject it here and point at `:=`, mirroring the
            // generator-loop guard in `lower_for_body_stmts`.
            if let Some(name) = first_outer_plain_assign(for_body, &scope) {
                return Err(outer_binding_write_error(stmt.span, name));
            }

            // A loop with no visible accumulator, no `<<` feed, and no `yield`
            // still may mutate a `Mut` variable through a *call* — `for x:
            // bump(cnt)`, where `bump(c: Mut(…))` writes `c`. Lowering runs
            // before inference, so we can't see the write hidden inside the
            // call; emit a direct-mirror `For` marker (its body a plain
            // side-effect statement) and let the post-inline letrec phase
            // classify it: a call that beta-reduces to a `MutWrite` makes it an
            // accumulator loop; a genuinely pure body leaves it write-free and
            // the phase drops it as a no-op. (`Expr::for_loop` builds a
            // *`Compose`*, a stateless map that cannot thread the accumulator,
            // so a hidden writer must take the `For` path, not that one.)
            if !for_body_has_yield(for_body) && !for_body_has_feed(for_body) {
                return lower_direct_mirror_loop(
                    target,
                    iter,
                    for_body,
                    &[],
                    body,
                    None,
                    stmt.span,
                    ctx,
                );
            }

            // A feed/yield loop with no accumulator is a side-effecting
            // `Compose` (desugar routes its feeds).
            let for_expr = lower_generator_for(target, iter, for_body, &scope, stmt.span, ctx)?;
            Ok(ctx.tag_machinery(Expr::expr_stmt(for_expr, body), stmt.span, "lower.stmt_seq"))
        }
        ChlStmt::Expr { .. } | ChlStmt::If { .. } | ChlStmt::Match { .. } => {
            let effect = lower_final_stmt(stmt, preceding, outer_bindings, ctx)?;
            Ok(ctx.tag_machinery(Expr::expr_stmt(effect, body), stmt.span, "lower.stmt_seq"))
        }
        // A standalone `with begin():` transaction — one commit over a
        // synthesized singleton source, which `transact_phase` folds into the commit
        // store holding the mutable variables it touches (see src/ccl/design/mutability.md).
        ChlStmt::With { .. } => lower_standalone_transaction(stmt, body, ctx),
        // Parse-recovery placeholder: silently drop the broken statement and
        // pass the continuation through. See `ChlExpr::Error`.
        ChlStmt::Error => Ok(body),
        _ => Err(LoweringError::unsupported(
            stmt.span,
            "only assignment and function definition statements are supported \
             before the final expression",
        )),
    }
}

/// Collect simple-name targets from assignment / function-def statements
/// into `names`. Used to build `outer_bindings` for mutation checks.
pub(super) fn collect_stmt_names(stmts: &[Spanned<ChlStmt>], names: &mut HashSet<String>) {
    for stmt in stmts {
        match &stmt.node {
            ChlStmt::Assign { target, .. }
            | ChlStmt::AnnAssign { target, .. }
            | ChlStmt::AugAssign { target, .. }
            | ChlStmt::MutAssign { target, .. }
            | ChlStmt::Define { target, .. } => {
                if let AssignTarget::Name(id) = &target.node {
                    names.insert(id.as_str().to_string());
                }
            }
            ChlStmt::FunctionDef { name, .. } => {
                names.insert(name.as_str().to_string());
            }
            _ => {}
        }
    }
}

/// Extract a simple variable name from a CHL assignment target.
///
/// Returns the name when the target is an [`AssignTarget::Name`], or
/// [`LoweringError::Unsupported`] for tuple-destructuring patterns (which
/// lowering does not yet support — the `http_serve` 2-tuple case is handled
/// separately via [`extract_http_serve_names`]).
pub(super) fn extract_name_target(
    target: &Spanned<AssignTarget>,
    context: &str,
) -> Result<String, LoweringError> {
    match &target.node {
        AssignTarget::Name(id) => Ok(id.as_str().to_string()),
        AssignTarget::Tuple(_) => Err(LoweringError::unsupported(
            target.span,
            format!("{context}: only simple name targets are supported"),
        )),
    }
}

/// Infallible variant of [`extract_name_target`]: returns the name when
/// `target` is an [`AssignTarget::Name`], or [`None`] for tuple-destructuring
/// patterns.  Used by predicates that want to detect a "simple assignment
/// to a particular name" without producing an error message.
pub(super) fn name_target_as_name(target: &Spanned<AssignTarget>) -> Option<&str> {
    if let AssignTarget::Name(id) = &target.node {
        Some(id.as_str())
    } else {
        None
    }
}

/// Reject a `Mut(V, Txn)` **mutable variable** write that lands *outside* a `with
/// begin():` block — the write-side mirror of the out-of-block read gate in
/// [`super::lower_expr`]. A mutable variable's history is the commit order, so a bare
/// write outside a block would become a plain sequential `let` shadow that
/// silently hides every committed value from subsequent reads; require the
/// write to sit inside a block.
///
/// A name shadowed by an inner local binder is a genuine local (its α-unique
/// binder wins), not the mutable variable, so it is never gated — mirroring the read
/// gate's `is_shadowed` guard against the base-name registry.
///
/// The dual case — an induction `Mut(V)` mutable variable written *inside* a block, which
/// `transact_phase` would silently swallow — is rejected at the block-body write
/// site in [`super::transactions::write_or_let`]; that check needs no induction
/// registry, because inside a block the only legal `:=` / `+=` target is a
/// transactional mutable variable.
pub(super) fn check_mut_write_context(
    name: &str,
    span: Span,
    ctx: &LoweringContext,
) -> Result<(), LoweringError> {
    if ctx.is_shadowed(name) {
        return Ok(());
    }
    if ctx.is_transactional_mut_var(name) && !ctx.in_tx_body {
        return Err(LoweringError::unsupported(
            span,
            format!("write transactional variable `{name}` inside a `with begin():` block"),
        ));
    }
    Ok(())
}

/// Resolve the annotation on a `:=` **introduction** to `(value type, transactional?)`,
/// rejecting the two forms that would have to be reinterpreted to be accepted.
///
/// A `:=` binder's type *is* a `Mut(V, D)`, so that is what an annotation on one
/// names. Two consequences, and the rule is their conjunction — **an annotation on
/// a `:=` binder is exact and is a `Mut(…)`**:
///
/// - A plain value type names the wrong thing. `x: Int := e` binds `x` at
///   `Mut(Int, D)`, not at `Int`, so reading it as the value type would make `:`
///   mean something here it means nowhere else.
/// - `<:` claims nothing `:` does not. [`Type::History`] is invariant in both
///   payloads (`solver::constrain`), so the only type below `Mut(V, D)` is
///   `Mut(V, D)`.
///
/// Both are rejected rather than reinterpreted, and both have the same remedy, so
/// they share one diagnostic. This leaves "a mutable whose value type is inferred
/// under a ceiling" unspellable, which is the honest position: under invariance it
/// is not a bound on the binder's type at all, and no syntax for a bound in the
/// *value* position exists (`<:` does not appear inside a type literal — see
/// `docs/chl-spec.md`, "Two annotation forms: exact and bounded").
pub(super) fn check_mut_decl_annotation(
    name: &str,
    ann: &TypeAnnotation,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<(Type, bool), LoweringError> {
    let parts = mut_annotation_parts(&ann.ty, ctx).transpose()?;
    if let (AnnotationMode::Exact, Some(parts)) = (ann.mode, parts.clone()) {
        return Ok(parts);
    }
    // Not accepted. Render what was written — lowering a non-`Mut` annotation
    // here so an annotation that is not a type at all reports *that* instead.
    let (value, is_txn, is_mut) = match parts {
        Some((value, is_txn)) => (value, is_txn, true),
        None => (lower_type_expr(&ann.ty, ctx)?, false, false),
    };
    let op = match ann.mode {
        AnnotationMode::Exact => ":",
        AnnotationMode::Bounded => "<:",
    };
    let written = if is_mut {
        format!("{}", MutForm(&value, is_txn))
    } else {
        value.to_string()
    };
    let remedy = MutForm(&value, is_txn);
    Err(LoweringError::unsupported(
        span,
        format!(
            "`{name} {op} {written} := …` is not a valid mutable-variable annotation: a \
             `:=` binder's type is `Mut(V, D)`, and `Mut` is invariant in `V`, so the \
             annotation names the whole variable and is always exact. Write \
             `{name}: {remedy} := init`, or drop the annotation to infer the value type \
             (`{name} := init`)"
        ),
    ))
}

/// Renders a value type back as the `Mut(…)` annotation that declares it.
struct MutForm<'a>(&'a Type, bool);

impl std::fmt::Display for MutForm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(value, is_txn) = self;
        if *is_txn {
            write!(f, "Mut({value}, Txn)")
        } else {
            write!(f, "Mut({value})")
        }
    }
}

/// If `annotation` is a `Mut(…)` form, extract its declared *value* type and
/// whether it is **transactional** (`Mut(V, Txn)`).
///
/// - `Mut(V)` / `Mut(_)` → `(V, false)` — an induction-domain accumulator whose
///   sequencing domain is inferred from its writing loop (`Mut(_)` → `(Hole,
///   false)`, value type inferred).
/// - `Mut(V, Txn)` → `(V, true)` — a transactional mutable variable over the commit
///   order.
///
/// `Txn` is the only explicit sequencing domain supported; any other second
/// slot is a lowering error. Returns `None` for a non-`Mut` annotation.
pub(super) fn mut_annotation_parts(
    annotation: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Option<Result<(Type, bool), LoweringError>> {
    // `Mut(…)` is type application — a call with a bare-name head (application
    // is parenthesised at both levels; see `lower_type_annotation`).
    let ChlExpr::Call { func, args } = &annotation.node else {
        return None;
    };
    let ChlExpr::Name(head) = &func.node else {
        return None;
    };
    if head.as_str() != "Mut" {
        return None;
    }
    match args.as_slice() {
        [value] => Some(lower_type_expr(value, ctx).map(|t| (t, false))),
        [value, domain] => {
            let value_ty = match lower_type_expr(value, ctx) {
                Ok(t) => t,
                Err(e) => return Some(Err(e)),
            };
            Some(match &domain.node {
                ChlExpr::Name(d) if d.as_str() == "Txn" => Ok((value_ty, true)),
                _ => Err(LoweringError::unsupported(
                    domain.span,
                    "the only explicit `Mut` sequencing domain is `Txn` (`Mut(V, Txn)`); \
                     omit it (`Mut(V)`) to infer a loop's induction domain",
                )),
            })
        }
        _ => Some(Err(LoweringError::unsupported(
            annotation.span,
            "`Mut` takes one or two arguments: `Mut(V)` or `Mut(V, Txn)`",
        ))),
    }
}

/// Pre-register every `x: Mut(V, Txn) := e` transactional-variable introduction
/// (and every pass-by-reference-`Mut` `def`) in `stmts` with the lowering
/// context.
///
/// for-loop is lowered *before* the `:=` introduction that precedes it
/// textually; pre-registering per block makes a transactional mutable variable visible
/// (for the read/write gate) when the loop that writes it inside a `with
/// begin():` block is lowered. Induction accumulators carry no lowering registry —
/// their mutability is the `Type::History` on the binding, checked post-inference —
/// so only transactional mutable variables and `Mut`-parameter `def`s are pre-registered
/// here.
///
/// The `Mut`-param `def` registration is per-name and **last definition wins**:
/// a later non-`Mut` `def` shadowing an earlier `Mut`-param one of the same name
/// *clears* the registration, so its calls lower with the ordinary tupled shape
/// (matching CHL's redefinition-shadows semantics). The caller
/// ([`lower_stmts_inner`]) scopes the whole set to the block, so this only
/// resolves same-name definitions *within* one block, never across scopes.
pub(super) fn pre_register_txn_decls(stmts: &[Spanned<ChlStmt>], ctx: &mut LoweringContext) {
    for stmt in stmts {
        match &stmt.node {
            // `x: Mut(V, Txn) := e` — a transactional-variable introduction.
            // Register `x` so a following loop's `with begin(): x := …` write is
            // recognised as a commit and a bare read of `x` is gated. A bare
            // `:=`, `x: T := e`, or `x: Mut(V) := e` is an induction accumulator and is
            // intentionally *not* registered (its mutability is checked
            // post-inference).
            ChlStmt::MutAssign {
                target,
                annotation: Some(annotation),
                ..
            } => {
                let AssignTarget::Name(id) = &target.node else {
                    continue;
                };
                // A malformed `Mut(…)` annotation (`Err`) surfaces its real error
                // when the `MutAssign` itself is lowered; not registering it here
                // is harmless.
                if matches!(
                    mut_annotation_parts(&annotation.ty, ctx),
                    Some(Ok((_, true)))
                ) {
                    ctx.register_transactional(id.as_str());
                }
            }
            // A `def` with a pass-by-reference `Mut` parameter is lowered and
            // applied curried. Blocks lower right-to-left, so a call site is
            // lowered *before* the `def` preceding it textually — pre-register
            // the name here so [`lower_call`] picks the curried shape. Mutable variable
            // or unregister per the definition's mut-ness so the last `def` of a
            // name in the block wins (a non-`Mut` redefinition clears an earlier
            // `Mut` one, so its calls lower tupled).
            ChlStmt::FunctionDef { name, params, .. } => {
                let has_mut_param = params.iter().any(|p| {
                    p.annotation
                        .as_ref()
                        .is_some_and(|a| is_mut_annotation(a, ctx))
                });
                if has_mut_param {
                    ctx.register_mut_param_fn(name.as_str());
                } else {
                    ctx.unregister_mut_param_fn(name.as_str());
                }
            }
            _ => {}
        }
    }
}

/// Whether a binder annotation is a pass-by-reference `Mut(…)` form.
///
/// Reads the annotation's *type* only. This runs during pre-registration, before
/// the mode is validated, so a bounded `Mut(…)` still answers `true` here and is
/// rejected where the parameter is lowered
/// (`lower::functions::mut_param_history_type`) — registering it either way is
/// harmless, since the rejection is what the program sees.
fn is_mut_annotation(annotation: &TypeAnnotation, ctx: &mut LoweringContext) -> bool {
    mut_annotation_parts(&annotation.ty, ctx).is_some()
}

/// Lower a binder's type annotation, applying its [`AnnotationMode`].
///
/// `x: T` lowers to `T`; `x <: T` lowers to [`Type::BoundedHole`], the marker
/// `normalize_annotation` turns into an inference variable bounded above by `T`.
/// The mode is a property of the *binder*, not of a type: `<:` is grammatical only
/// where a binder is introduced, so nested positions inside `T` are always exact
/// and [`lower_type_expr`] needs no mode parameter. (Design:
/// `src/ccl/design/type-inference.md`, "Annotation kinds: exact and bounded".)
pub(super) fn lower_type_annotation(
    annotation: &TypeAnnotation,
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    let ty = lower_type_expr(&annotation.ty, ctx)?;
    Ok(match annotation.mode {
        AnnotationMode::Exact => ty,
        AnnotationMode::Bounded => Type::BoundedHole(Box::new(ty)),
    })
}

/// Lower a CHL type *expression* to a CCL [`Type`].
///
/// Recognised forms:
/// - Capitalized primitive names (`Caps` means type — `docs/chl-spec.md`):
///   `Int`, `UInt`, `String`, `Bool` → [`Type::Base`].
/// - The wildcard `_` → [`Type::Hole`] ("infer this slot" — inference
///   normalizes an annotation `Hole` to a fresh variable, so the slot is
///   unconstrained; see `bind_annotation`).
/// - Type application `List(T)` — a type constructor applied to argument types.
///   Application is parenthesised at both the term and type level
///   (`docs/chl-spec.md`).
/// - A record type `{name: T, …}` and a tuple type `{T, U}`
///   (`Expr::BraceGroup`), including the one-element `{T,}` — the trailing
///   comma is what makes it a product, and the parser rejects a comma-free
///   `{T}`.
/// - A variant type `` {`a | `b{Int}} `` — the same brace group, told apart from
///   a tuple type by its arms' backticks.
/// - The empty group `{}` — the unit type, `Unit`.
/// - A function type `T => U` — a [`Type::Fun`] compute function
///   (`docs/chl-spec.md`, "6. Types (informal sketch)").
pub(super) fn lower_type_expr(
    annotation: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    match &annotation.node {
        // A primitive (`Int`) or the wildcard `_`. A lone name is never a variant:
        // a tag is written with its backtick wherever it appears.
        ChlExpr::Name(id) => name_type(id.as_str()).ok_or_else(|| {
            LoweringError::unsupported(annotation.span, format!("unknown type annotation: {id}"))
        }),
        // Type application `List(T)`: a type constructor applied to argument
        // types. Application uses parentheses at both levels
        // (`docs/chl-spec.md`).
        ChlExpr::Call { func, args } => {
            lower_type_application(annotation.span, type_ctor_head(func)?, args, ctx)
        }
        // Record type `{name: T, …}`.
        ChlExpr::BraceRecord(fields) => {
            let mut out = Vec::with_capacity(fields.len());
            for field in fields {
                out.push((
                    field.name.as_str().to_string(),
                    lower_type_expr(&field.value, ctx)?,
                ));
            }
            Ok(Type::Record(out))
        }
        // The **empty** group `{}` is the **unit type** — not a zero-field
        // product, of which there is none: a product with no fields is unit,
        // and `Tuple([])` is not a valid type (see `docs/chl-spec.md`, "6.6 The
        // empty product is unit").
        ChlExpr::BraceGroup(parts) if parts.is_empty() => Ok(Type::Base(BaseType::Unit)),
        // A colon-free brace group is a tuple type `{T, U}` — and `{T,}` for one
        // element, the trailing comma being what makes it a product — unless its
        // content is a `|`-chain of tags, which makes it the variant type
        // `` {`a | `b} ``. The two forms share a bracket and are told apart by
        // the backtick, the same marker that makes a tag a tag everywhere else.
        //
        // `|` lexes as the logical-or operator, so a chain arrives as nested
        // `BinOp` nodes. The readings never collide: in *type* position there is
        // no boolean to disjoin, and the arms are backticked.
        ChlExpr::BraceGroup(parts) => match parts.as_slice() {
            [only] if only.node.is_variant_arms() => lower_variant_type(only, ctx),
            // Arms are `|`-separated; a comma would make this a tuple *of*
            // variant types, which is a different type and almost never meant.
            _ if parts.iter().any(|p| p.node.is_variant_arms()) => Err(LoweringError::unsupported(
                annotation.span,
                "a variant type separates its arms with `|`: `` {`a | `b{Int}} ``",
            )),
            _ => {
                let mut out = Vec::with_capacity(parts.len());
                for part in parts {
                    out.push(lower_type_expr(part, ctx)?);
                }
                Ok(Type::Tuple(out))
            }
        },
        // Refinement type `{T where p}` (`docs/chl-spec.md`, "6.4 Refinement
        // syntax"): the base type refined by a `Bool` predicate over the
        // anonymous subject `_`. The subject lowers to the reserved binder
        // `__elem` (`REFINEMENT_BINDER`), so the stored predicate is a bare
        // `Bool` term with `__elem` free — the same shape a singleton or a
        // `groupby` refinement carries. Discharge of the predicate is the
        // solver's structural refinement subsumption; this only builds the type.
        ChlExpr::BraceRefinement { base, predicate } => {
            let base_ty = lower_type_expr(base, ctx)?;
            let pred = ctx.with_in_refinement_predicate(|ctx| lower_expr(predicate, ctx))?;
            Ok(Type::Refinement(
                Box::new(base_ty),
                crate::ccl::Refinement::born(Rc::new(pred)),
            ))
        }
        // A variant type is delimited, so its arms are never bare: without the
        // braces there is nothing to say where the `|`-chain ends. A `|` in type
        // position has no other reading — CHL has no union *of types* — so the
        // same message serves whether or not the operands are tags.
        ChlExpr::VariantCtor { .. }
        | ChlExpr::BinOp {
            op: ChlBinOp::LogicalOr,
            ..
        } => Err(LoweringError::unsupported(
            annotation.span,
            "a variant type is written in braces, and its arms are backticked tags: \
             `` {`a | `b{Int}} ``",
        )),
        // A function type `T => U` (`docs/chl-spec.md`, "6. Types (informal
        // sketch)"). The surface arrow is the compute arrow `⇒`
        // ([`FunKind::Compute`]) — the kind a `def`/lambda produces — so an
        // annotated binding `f: (Int => Int) = \x -> …` matches its value.
        // `Type::fun` builds the non-dependent form (`name: None`); the surface
        // has no binder to make it a Pi type, and a data collection (`⤇`) is
        // written with its own constructor, never with `=>`.
        ChlExpr::FunctionType { domain, codomain } => Ok(Type::fun(
            lower_type_expr(domain, ctx)?,
            lower_type_expr(codomain, ctx)?,
        )),
        // A parenthesised comma list `(T, U)` is a *term* product; the tuple
        // *type* is written with braces `{T, U}` (`docs/chl-spec.md`).
        ChlExpr::Tuple(_) => Err(LoweringError::unsupported(
            annotation.span,
            "a tuple type is written with braces: `{T, U}`",
        )),
        _ => Err(LoweringError::unsupported(
            annotation.span,
            format!("unsupported type annotation form: {:?}", annotation.node),
        )),
    }
}

/// Lower a variant type — **one arm, or a `|`-chain of them** — into a
/// [`Type::Variant`].
///
/// Arms are canonicalized into **name order**, matching [`Type::option_of`] and the
/// order the solver materializes a coalesced variant in. Without that, a
/// hand-written `` `some{T} | `none `` would be a distinct type from `Option(T)`
/// that merely happens to carry the same arms, and an annotation written in the
/// other order would not compare equal to what inference produced.
fn lower_variant_type(
    ann: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    let mut arms: Vec<(FieldKey, Type)> = Vec::new();
    collect_variant_arms(ann, &mut arms, ctx)?;
    arms.sort_by(|(a, _), (b, _)| a.cmp(b));
    if let Some(dup) = arms.windows(2).find(|w| w[0].0 == w[1].0) {
        return Err(LoweringError::unsupported(
            ann.span,
            format!(
                "variant type names the tag `{}` twice; each tag carries one payload type",
                dup[0].0
            ),
        ));
    }
    Ok(Type::variant(arms))
}

/// Flatten one arm (or a nested `|`) of a variant type into `arms`.
fn collect_variant_arms(
    ann: &Spanned<ChlExpr>,
    arms: &mut Vec<(FieldKey, Type)>,
    ctx: &mut LoweringContext,
) -> Result<(), LoweringError> {
    match &ann.node {
        ChlExpr::BinOp {
            left,
            op: ChlBinOp::LogicalOr,
            right,
        } => {
            collect_variant_arms(left, arms, ctx)?;
            collect_variant_arms(right, arms, ctx)
        }
        ChlExpr::VariantCtor { tag, payload, .. } => {
            let payload = match payload {
                // A bare tag carries no payload, so its payload type is `Unit` —
                // the same type the bare constructor `` `tag `` injects.
                None => Type::Base(BaseType::Unit),
                // The tag's braces are the payload type's own, so the parser has
                // already resolved the elision and this is an ordinary type
                // expression — `Int` from `` `a{Int} ``, the one-tuple `{Int,}`
                // from `` `a{Int,} ``.
                Some(ChlVariantPayload::Fields(ty)) => lower_type_expr(ty, ctx)?,
                // Parens carry a *value*; an arm in a type names the type its
                // tag stores.
                Some(ChlVariantPayload::Term(_)) => {
                    return Err(LoweringError::unsupported(
                        ann.span,
                        format!(
                            "`(…)` after a tag carries a value; a variant arm's payload \
                             is a type in braces: `` `{tag}{{T}} ``"
                        ),
                    ));
                }
            };
            arms.push((FieldKey::Name(tag.as_str().into()), payload));
            Ok(())
        }
        _ => Err(LoweringError::unsupported(
            ann.span,
            "a variant type's arms are backticked tags: `` `some{Int} | `none ``",
        )),
    }
}

/// Resolve a capitalized primitive type name (`Caps` means type —
/// `docs/chl-spec.md`), or the
/// inference wildcard `_`. Returns `None` for any other identifier.
fn name_type(id: &str) -> Option<Type> {
    if let Some(base) = BaseType::from_keyword(id) {
        // The unit type is written `{}` — one spelling per type
        // (`docs/chl-spec.md`, "6.6 The empty product is unit"), so the name
        // `BaseType::from_keyword` accepts for the CCL round-trip is not a CHL
        // annotation.
        if matches!(base, BaseType::Unit) {
            return None;
        }
        return Some(Type::Base(base));
    }
    // `_` is the inference wildcard, not a primitive, so it is not a
    // `BaseType`; handle it alongside the primitive round-trip.
    match id {
        "_" => Some(Type::Hole),
        _ => None,
    }
}

/// Extract the simple-name head of a type application (`List` in `List(T)`).
/// A non-name head is unsupported.
fn type_ctor_head(head: &Spanned<ChlExpr>) -> Result<&str, LoweringError> {
    match &head.node {
        ChlExpr::Name(id) => Ok(id.as_str()),
        _ => Err(LoweringError::unsupported(
            head.span,
            "a type application must have a simple name head (e.g. `List(…)`)",
        )),
    }
}

/// Lower a type constructor `head` applied to `args`.
fn lower_type_application(
    span: Span,
    head: &str,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Type, LoweringError> {
    let arity_err = |want: &str| {
        LoweringError::unsupported(
            span,
            format!("`{head}(…)` type takes {want}, got {}", args.len()),
        )
    };
    match head {
        // `Array(n, T)` = `[0, n) ⤇ T` — a static index range. `n` is an integer
        // literal (the length is known at annotation time).
        "Array" => {
            let [n_arg, elem] = args else {
                return Err(arity_err("a length and an element type"));
            };
            let ChlExpr::Lit(ChlLit::Int(n)) = &n_arg.node else {
                return Err(LoweringError::unsupported(
                    n_arg.span,
                    "`Array(n, T)` needs an integer-literal length `n`",
                ));
            };
            let n = usize::try_from(*n).map_err(|_| {
                LoweringError::unsupported(n_arg.span, "`Array` length must be non-negative")
            })?;
            Ok(Type::data_fun(
                Type::UIntRange(n),
                lower_type_expr(elem, ctx)?,
            ))
        }
        // `List(T)` = `Σ (D: UIntRanges). D ⤇ T` — the sum over every index range.
        // A list literal of extent `k` reaches it as `box(lit)`, whose one-candidate sum
        // is contained by width because `[0, k)` is a member of that kind. The `box` is
        // required: a bare `[0, k) ⤇ T` is not below the sum
        // (`Type::list_of`, `src/ccl/design/collections.md`, "Subtyping").
        "List" => {
            let [elem] = args else {
                return Err(arity_err("one element type"));
            };
            Ok(Type::list_of(lower_type_expr(elem, ctx)?))
        }
        // The **keyed** collections (`Map`/`Set`/`Dict`) are data functions over a
        // keyed extent `𝐸` with keys `{𝑘: 𝐾 | 𝑘 ∈ 𝐸}` (design/collections.md).
        // Deferred: Cambra has no map/set/dict *values* yet, so a keyed Σ would be
        // an uninhabited type. Wired once a keyed-collection value form exists
        // (higher in the stack).
        "Map" | "Dict" | "Set" => Err(LoweringError::unsupported(
            span,
            format!(
                "`{head}(…)` is deferred — Cambra has no {head}/keyed-collection \
                 values yet, so the type would be uninhabited (see \
                 `src/ccl/design/collections.md` \"Status\"); \
                 `Array(n, T)` and `List(T)` are available"
            ),
        )),
        // `Collection(T)` = `Σ (𝐷: Any). 𝐷 ⤇ T` — the whole-domain-witness sum (a
        // `TypeKind::Any` type-witness): an unordered, opaque-extent collection, the ⊤
        // of the kind order (`Type::collection_of`, design/collections.md).
        "Collection" => {
            let [elem] = args else {
                return Err(arity_err("one element type"));
            };
            Ok(Type::collection_of(lower_type_expr(elem, ctx)?))
        }
        // `Option(T)` abbreviates the two-tag variant `{some: T, none: Unit}` —
        // a peer of `List(T)` here, not a distinguished type. Its constructors
        // are the ordinary `` `some(e) `` / `` `none ``, which no pass special-cases.
        "Option" => {
            let [payload] = args else {
                return Err(LoweringError::unsupported(
                    span,
                    "`Option` takes one type argument: `Option(T)`",
                ));
            };
            Ok(Type::option_of(lower_type_expr(payload, ctx)?))
        }
        // `Mut(…)` in a nested position is handled by `mut_annotation_parts`
        // before this function is reached; seeing it here means a `Mut` inside
        // another type, which is not supported yet.
        other => Err(LoweringError::unsupported(
            span,
            format!("unknown type application: `{other}(…)`"),
        )),
    }
}

/// Lower a [`ChlStmt::Match`] to a scrutinee-[`TypedExprNode::Case`].
///
/// Each `` case `tag(binder): `` arm becomes one [`Branch`] carrying a
/// [`Pattern`] — so `match` needs no IR node of its own: the pattern-`Case`
/// that variant elimination already compiles *is* `match`. Every arm's guard is
/// the literal `true`, which is what makes tag dispatch and the guarded
/// `if`/`elif` chain the same first-match rule over one node
/// (see `src/ccl/design/lowering.md`, "Variants and match").
///
/// Exhaustiveness is not checked here and needs no check: inference builds the
/// expected scrutinee type *from* the arm tags and requires the scrutinee to be
/// a subtype of it, so a `match` cannot be non-exhaustive with respect to its
/// own arms. It fails only when the scrutinee's type is pinned independently
/// (an annotation, or a compiler-produced `Option`) and carries a tag no arm
/// handles — reported as an extra-tag subtyping failure.
///
/// The payload binder is shadowed over the arm body, so an arm binder spelled
/// like an outer transactional register is treated as the genuine local it is.
/// A binder-less `case tag:` still binds — to a reserved name the body cannot
/// mention — because [`Pattern`] always names the payload it narrows; only the
/// arm's ability to *read* it differs.
///
/// A `match` whose **only** arm is `case _:` names no tag at all, so it does not
/// dispatch: its value is the default arm's, whatever the scrutinee is. It lowers
/// to that body under an [`TypedExprNode::ExprStmt`] keeping the scrutinee, which
/// is what still *types* the scrutinee (an unbound or ill-typed one is an error
/// here as anywhere) while denoting a value that does not depend on it.
/// `channelize` drops the `ExprStmt` with the rest of them.
pub(super) fn lower_match(
    match_span: Span,
    scrutinee: &Spanned<ChlExpr>,
    arms: &[MatchArm],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // The parser's `.at_least(1)` guarantees this; a zero-arm `match` would
    // lower to a `Case` with no branches, which has no value to denote.
    assert!(
        !arms.is_empty(),
        "lower_match: `match` with no `case` arms (parser invariant violated)"
    );
    if let Some(dup) = first_duplicate_tag(arms) {
        return Err(LoweringError::unsupported(
            match_span,
            format!(
                "`match` has two `case {dup}` arms; each tag is handled by exactly \
                 one arm (the arms partition the scrutinee's tags)"
            ),
        ));
    }
    // The default arm must be last and unique. It matches whatever the tagged arms
    // did not, so an arm after it could never be selected, and two of them would
    // make the second unreachable.
    let defaults = arms.iter().filter(|a| a.pattern.is_none()).count();
    if defaults > 1 {
        return Err(LoweringError::unsupported(
            match_span,
            "`match` has more than one `case _:` arm; the first would match \
             everything the tagged arms did not, leaving the rest unreachable",
        ));
    }
    if defaults == 1 && arms.last().is_some_and(|a| a.pattern.is_some()) {
        return Err(LoweringError::unsupported(
            match_span,
            "`case _:` must be the last arm: it matches whatever the tagged arms \
             did not, so an arm after it could never be selected",
        ));
    }
    let scrutinee_expr = lower_expr(scrutinee, ctx)?;
    // Only a default arm: nothing is dispatched on, so there is no `Case` to
    // build — a tag-less `Branch` is a *fallback*, and with no tagged arm to fall
    // back from it is simply the value. Sequencing it after the scrutinee keeps
    // the scrutinee typed without letting it decide anything.
    if arms.len() == 1 && defaults == 1 {
        let body = lower_stmts_inner(&arms[0].body, outer_bindings, ctx, false)?;
        return Ok(ctx.tag_image(Expr::expr_stmt(scrutinee_expr, body), match_span));
    }
    let mut branches = Vec::with_capacity(arms.len());
    for arm in arms {
        let Some(pat) = &arm.pattern else {
            // The default arm binds nothing — the tags it covers have different
            // payload types, so there is no single thing to bind — and lowers to a
            // tag-less `Branch`, which is what makes it the fallback.
            let body = lower_stmts_inner(&arm.body, outer_bindings, ctx, false)?;
            branches.push(Branch {
                pattern: None,
                // Tag dispatch carries no boolean test, so every arm's guard is
                // manufactured encoding — what makes `match` and the guarded
                // `if`/`elif` chain one first-match rule over one node.
                guard: ctx.tag_machinery(
                    Expr::lit(Lit::Bool(true)),
                    match_span,
                    "lower.match_guard",
                ),
                body,
            });
            continue;
        };
        // An arm that names no payload still needs a payload name for `Pattern`. Use
        // a reserved spelling so the body cannot read what it declined to name — for
        // `_` because that is what `_` means, and for the payload-less form because
        // there is nothing there to read.
        let binder = match &pat.payload {
            PayloadPattern::Named(name) => name.as_str().to_string(),
            PayloadPattern::Ignored | PayloadPattern::Absent => ctx.fresh_ignored_payload(),
        };
        // Whether the arm *claims the tag carries nothing*. `` case `tag: `` is a
        // statement about the type, not an elision of the binder: it matches a
        // payload-less tag, and `emit_case` turns the claim into a constraint on that
        // arm's payload. `_` makes no such claim — it has a payload and declines to
        // read it.
        let empty_payload = matches!(pat.payload, PayloadPattern::Absent);
        let mut arm_scope = outer_bindings.clone();
        arm_scope.insert(binder.clone());
        let body = ctx.with_shadowed(vec![binder.clone()], |ctx| {
            lower_stmts_inner(&arm.body, &arm_scope, ctx, false)
        })?;
        branches.push(Branch {
            pattern: Some(Pattern {
                tag: pat.tag.as_str().to_string(),
                binding: TypedBinding {
                    name: binder.into(),
                    ty: Type::Hole,
                    user_annotation: None,
                },
                empty_payload,
            }),
            guard: ctx.tag_machinery(Expr::lit(Lit::Bool(true)), match_span, "lower.match_guard"),
            body,
        });
    }
    // The `Case` images the `match` statement. A statement is not a
    // `Spanned<ChlExpr>`, so it has no `Source` node — `tag_image` is the image
    // marker at `Nature::Machinery` (`src/ccl/design/provenance.md`, "The seam
    // (`src/ccl/context.rs`)").
    Ok(ctx.tag_image(
        Expr::new(TypedExprNode::Case {
            scrutinee: Some(Box::new(scrutinee_expr)),
            branches,
        }),
        match_span,
    ))
}

/// The first tag appearing on more than one arm, if any.
fn first_duplicate_tag(arms: &[MatchArm]) -> Option<&str> {
    let mut seen = HashSet::new();
    arms.iter()
        .filter_map(|arm| arm.pattern.as_ref())
        .find(|pat| !seen.insert(pat.tag.as_str()))
        .map(|pat| pat.tag.as_str())
}

/// Lower a [`ChlStmt::If`] (a flattened `if`/`elif`/`else` chain) to a
/// [`TypedExprNode::Case`] expression.
///
/// Each [`IfBranch`] becomes one [`Branch`] (with the branch's `cond` as guard
/// and `body` lowered as a nested statement block). A trailing `else_body`
/// becomes the final branch with an always-`true` guard.
///
/// A bare `if` without an `else` clause is not value-returning and is rejected
/// with [`LoweringError::Unsupported`].
pub(super) fn lower_if(
    if_span: Span,
    branches: &[IfBranch],
    else_body: Option<&[Spanned<ChlStmt>]>,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let Some(else_body) = else_body else {
        return Err(LoweringError::unsupported(
            if_span,
            "if without else is not supported as a value-returning expression",
        ));
    };
    // http_serve is not permitted inside if/else arms.
    let mut out_branches = Vec::with_capacity(branches.len() + 1);
    for branch in branches {
        let guard = lower_expr(&branch.cond, ctx)?;
        let body = lower_stmts_inner(&branch.body, outer_bindings, ctx, false)?;
        out_branches.push(Branch {
            pattern: None,
            guard,
            body,
        });
    }
    let else_expr = lower_stmts_inner(else_body, outer_bindings, ctx, false)?;
    // The `else` arm's always-true guard is manufactured encoding; the `Case`
    // itself images the if/else statement.
    out_branches.push(Branch {
        pattern: None,
        guard: ctx.tag_machinery(Expr::lit(Lit::Bool(true)), if_span, "lower.if_else"),
        body: else_expr,
    });
    Ok(ctx.tag_image(
        Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: out_branches,
        }),
        if_span,
    ))
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;

    // -----------------------------------------------------------------------
    // Statement block tests (let bindings)
    // -----------------------------------------------------------------------

    #[rstest]
    #[case(
        "\
x = 2
x",
        "\
let x = 2
in x"
    )]
    #[case(
        "\
x = 2
y = x
y",
        "\
let x = 2
in let y = x
in y"
    )]
    #[case(
        "\
x = 2 + 3
y = x * 4
y",
        "\
let x = 2 + 3
in let y = x * 4
in y"
    )]
    // Note: SSA and ANF disallow this sort of redefinition; our less-normalised
    // representation allows shadowing the same binding name.
    #[case(
        "\
x = 2 + 3
x = x * 4
x",
        "\
let x = 2 + 3
in let x = x * 4
in x"
    )]
    // Augmented assignment: `x op= e` is a mutable write (`MutWrite`) — the target
    // must be introduced mutable with `:=`.
    #[case(
        "\
x := 0
x += 1
x",
        "\
x : Mut(_, _) := 0
in x := x + 1; x"
    )]
    #[case(
        "\
x := 10
x -= 3
x",
        "\
x : Mut(_, _) := 10
in x := x - 3; x"
    )]
    #[case(
        "\
x := 2
x *= 5
x",
        "\
x : Mut(_, _) := 2
in x := x * 5; x"
    )]
    #[case(
        "\
x := 7
x //= 2
x",
        "\
x : Mut(_, _) := 7
in x := x // 2; x"
    )]
    // Chained augmented assignments are a sequence of mutable writes.
    #[case(
        "\
x := 0
x += 1
x += 2
x",
        "\
x : Mut(_, _) := 0
in x := x + 1; x := x + 2; x"
    )]
    // defer() introduces a Defer node.
    #[case(
        "\
x = defer()
x",
        "\
let x = defer
in x"
    )]
    // x <<= expr (AugAssign LShift) lowers to ExprStmt(Define(x, expr), body).
    #[case(
        "\
x = defer()
x <<= 1
x",
        "\
let x = defer
in define(x, 1); x"
    )]
    // x << expr as a middle statement lowers to ExprStmt(Feed(x, expr), body).
    #[case(
        "\
x = defer()
x << 1
x",
        "\
let x = defer
in feed(x, 1); x"
    )]
    // defer with an intervening let binding before the define.
    #[case(
        "\
x = defer()
y = 5
x <<= y + 1
x",
        "\
let x = defer
in let y = 5
in define(x, y + 1); x"
    )]
    // Two independent defers each get their own Let/Defer node.
    #[case(
        "\
x = defer()
y = defer()
x <<= 1
y <<= 2
x",
        "\
let x = defer
in let y = defer
in define(x, 1); define(y, 2); x"
    )]
    fn test_lower_stmts(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Future construct tests — ignored until lowering is implemented.
    //
    // These are CHL expressions that will produce Expr::Let nodes in value
    // position once supported. They must be promoted to end-to-end pipeline
    // tests (CHL → CCL → Operators) at that point, as compile_case and any
    // other new compile_* function must save/restore ctx.scope to uphold the
    // invariant described in compile_ccl::compile_let.
    // -----------------------------------------------------------------------

    /// `if/else` with branch-local variables lowers to
    /// `let result = case cond of { True → let tmp = … in … | False → let tmp = … in … } in result`.
    /// The Case branches each contain a Let, so compile_case must save/restore
    /// ctx.scope for each branch or value_op.subscribe() will panic on the
    /// inner tmp VarRef.
    #[test]
    #[ignore = "if/else as a non-final statement (assignment-binding desugaring) is not yet \
                implemented; if/else as a final value-returning statement is now supported"]
    fn test_lower_if_else_branch_locals() {
        let code = "\
if cond:
    tmp = 1
    result = tmp + 1
else:
    tmp = 2
    result = tmp + 2
result";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        // Non-final if/else with assignment desugaring: this test remains ignored.
        // When implemented, the expected structure is:
        // let result = { cond → let tmp = 1 in tmp + 1; true → let tmp = 2 in tmp + 2 } in result
        assert_eq!(symbolic(&ccl), "");
    }

    /// Walrus operator `(y := expr)` lowers to `Expr::Let` in expression position,
    /// placing a Let directly in the value field of an outer Let:
    /// `let x = (let y = 5 in y) + 1 in x`.
    /// This is the only planned CHL construct that puts a Let directly in
    /// Let.value (not inside a Case branch). compile_let must be fixed to pass
    /// the post-value scope (not parent_scope) to value_op.subscribe() before
    /// this can run end-to-end.
    #[test]
    #[ignore = "walrus operator (:=) not yet in the CHL grammar"]
    fn test_lower_walrus_let_in_value_position() {
        let code = "\
x = (y := 5) + 1
x";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        // Fill in the expected string when `:=` is added to the CHL grammar
        // and lowering. Structure: let x = (let y = 5 in y) + 1 in x.
        assert_eq!(symbolic(&ccl), "");
    }

    // -----------------------------------------------------------------------
    // if/else lowering tests
    //
    // TODO: CHL if/else is currently only supported in *tail position*, where
    // the whole block is treated as an expression. Non-tail if/else statements
    // (where bindings from inside the block are used by subsequent statements)
    // require a statement-level IR pass that doesn't yet exist; see
    // `test_lower_if_else_branch_locals` and `test_lower_non_tail_if` below.
    // -----------------------------------------------------------------------

    #[rstest]
    // Simple if/else as the final statement.
    #[case("if x:\n    1\nelse:\n    0", "{ x → 1; true → 0 }")]
    // Scrutinee from an outer let binding.
    #[case(
        "x = 5\nif x > 3:\n    10\nelse:\n    0",
        "let x = 5\nin { x > 3 → 10; true → 0 }"
    )]
    // elif chain: CHL's flat `Stmt::If { branches, else_body }` lowers to a single Case
    // with one branch per `if`/`elif` plus a true-guard for the `else`.
    #[case(
        "if c1:\n    1\nelif c2:\n    2\nelse:\n    3",
        "{ c1 → 1; c2 → 2; true → 3 }"
    )]
    // Multi-statement arm body: last stmt must be a bare expression.
    #[case(
        "if x:\n    a = 1\n    a\nelse:\n    0",
        "{ x → let a = 1\nin a; true → 0 }"
    )]
    fn test_lower_if(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    /// A bare `if` (no `else`) in non-tail position: rejected today because
    /// CHL has no side effects, so a branch that produces no value on the
    /// false path has no well-typed CCL representation. Requires a
    /// statement-level IR to handle correctly.
    #[test]
    #[ignore = "non-tail if/else requires a statement-level IR pass (not yet implemented)"]
    fn test_lower_non_tail_if() {
        let code = "x = 1\nif x > 0:\n    x = x + 1\nresult = x\nresult";
        let stmts = parse_module(code);
        let _ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        // Expected once implemented:
        // let x = 1 in let x = { x > 0 → x + 1; true → x } in let result = x in result
    }

    #[test]
    fn test_lower_if_without_else_rejected() {
        let stmts = parse_module("if x:\n    1");
        let err = expect_one_lowering_error(&stmts);
        assert!(matches!(err, LoweringError::Unsupported { .. }));
    }

    /// A colon-free brace group `{T, U}` is structural *type* syntax; it has no
    /// term-level value, so it is rejected in value position (it is accepted as
    /// a tuple type in annotation position — see `lower_type_annotation`).
    #[test]
    fn test_brace_group_as_value_rejected() {
        let stmts = parse_module("{1, 2}");
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message, .. } = &err;
        assert!(
            message.contains("type syntax"),
            "expected a type-syntax hint, got: {message}"
        );
    }

    /// A brace record `{name: T}` is a record *type*; a record *value* is
    /// `(name=value)`, so the brace form is rejected in value position.
    #[test]
    fn test_brace_record_as_value_rejected() {
        let stmts = parse_module("{name: 1}");
        let err = expect_one_lowering_error(&stmts);
        let LoweringError::Unsupported { message, .. } = &err;
        assert!(
            message.contains("(name=value)"),
            "expected a paren-record hint, got: {message}"
        );
    }

    /// A refinement type annotation `{T where p}` lowers to a
    /// [`Type::Refinement`], and — the rule that distinguishes it from an
    /// ordinary predicate — the anonymous subject `_` in `p` lowers to the
    /// reserved refinement binder `__elem` (`REFINEMENT_BINDER`), *not* a
    /// variable named `_`. That resolution is what the
    /// `in_refinement_predicate` flag buys: `_` denotes "the value being
    /// refined" only inside a predicate.
    ///
    /// `symbolic` renders only a binding's inferred `ty`, and the annotation
    /// rides `user_annotation` (still `Hole`-typed pre-inference), so the test
    /// reads the annotation back off the `Let` and renders *its* type — one
    /// string that surfaces the base, the predicate, and the resolved subject.
    #[rstest]
    // Flat refinement: the predicate's `_` becomes `__elem`.
    #[case("x: {Int where _ != 0} = 5\nx", "{Int | __elem != 0}")]
    // Nested refinement: both levels' `_` resolve to `__elem`, and the
    // save/restore of `in_refinement_predicate` around the inner annotation
    // keeps the flag from leaking — the outer `_` still lowers to `__elem`
    // after the inner predicate closes.
    #[case(
        "x: { {Int where _ != 1} where _ != 0} = 5\nx",
        "{{Int | __elem != 1} | __elem != 0}"
    )]
    fn test_lower_refinement_annotation(#[case] code: &str, #[case] expected_ty: &str) {
        use crate::ccl::{Type, TypedExprNode};

        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        let TypedExprNode::Let { binding, .. } = &ccl.node else {
            panic!("expected a top-level Let, got {:?}", ccl.node);
        };
        let ann = binding
            .user_annotation
            .as_ref()
            .expect("an annotated assignment must carry a user annotation");
        assert!(
            matches!(ann, Type::Refinement(..)),
            "expected a Type::Refinement, got {ann:?}"
        );
        assert_eq!(format!("{ann}"), expected_ty);
    }

    // -----------------------------------------------------------------------
    // Provenance side-table population (S2b)
    // -----------------------------------------------------------------------

    /// Lowering records a leaf `LoweringStep` per node, so after the fold every
    /// node resolves back to its exact source span — and the `Nature` each node
    /// carries follows the structural rule on `LoweringContext::tag_source`:
    /// `Source` ⟺ the node is the root of a lowered `Spanned<ChlExpr>`.
    ///
    /// This pins both sides of that rule on one program. The root `Let` images
    /// the assignment *statement* `x = 1` — a statement is not a
    /// `Spanned<ChlExpr>`, so it resolves to its span with the `"lower.image"`
    /// label but **not** `Nature::Source`. The final `x + 2` *is* an expression
    /// root, so it is `Source`.
    #[test]
    fn lowering_tags_nodes_with_source_spans() {
        use crate::ccl::TypedExprNode;
        use crate::ccl::lineage::{Nature, RecorderSession, collapse_lowering};
        use crate::ccl::provenance::NodeId;
        use crate::chl_parser::ast::Span;
        use std::collections::HashSet;

        // `x = 1` is the first statement (spans bytes 0..5); `x + 2` is the
        // final bare expression (spans bytes 6..11). The source-byte offsets are
        // load-bearing: the test asserts the exact origin span of each node.
        let src = "x = 1\nx + 2\n";
        let stmts = parse_module(src);
        assert_eq!(stmts[0].span, Span::new(0, 5), "stmt `x = 1` span");
        let final_expr_span = stmts[1].span;
        assert_eq!(final_expr_span, Span::new(6, 11), "expr `x + 2` span");

        // Install the always-on lowering session, lower, then fold the log into
        // the lowering projection — the same handoff `compile_program` runs.
        let mut ctx = LoweringContext::default();
        let session = RecorderSession::lowering();
        let lowered = lower_stmts(&stmts, &mut ctx)
            .into_result()
            .expect("lowering succeeds");
        let log = session.into_lowering_log();
        let mut output_ids: HashSet<NodeId> = HashSet::new();
        fn ids(e: &Expr, acc: &mut HashSet<NodeId>) {
            acc.insert(e.node_id());
            e.walk_children(|c| ids(c, acc));
        }
        ids(&lowered, &mut output_ids);
        let (seed, leaks) = collapse_lowering(&log, &output_ids);
        assert!(leaks.is_empty(), "lowering fold is leak-free: {leaks:?}");

        // Root node is the `let x = 1 in (x + 2)` binding, tagged with the
        // assignment statement's span.
        let TypedExprNode::Let {
            bound_expr, body, ..
        } = &lowered.node
        else {
            panic!("expected a Let at the root, got {:?}", lowered.node);
        };
        let root_attr = seed
            .get(&lowered.node_id())
            .expect("root Let node has a projection entry");
        assert_eq!(
            root_attr.rewritten.nature,
            Nature::Machinery,
            "a statement image is not an expression root, so not Source"
        );
        assert_eq!(
            root_attr.rewritten.label, "lower.image",
            "it is still an image of source text, not manufactured plumbing"
        );
        assert_eq!(root_attr.spans, vec![Span::new(0, 5)]);

        // The bound expression `1` is tagged with the RHS literal's span.
        assert_eq!(
            seed.get(&bound_expr.node_id()).map(|a| a.spans.as_slice()),
            Some(&[Span::new(4, 5)][..]),
            "bound `1` traces to its literal span"
        );

        // The other side of the rule: the final `x + 2` BinOp is the root of a
        // lowered `Spanned<ChlExpr>`, so it carries that expression's span *and*
        // `Nature::Source`.
        let nested_attr = seed
            .get(&body.node_id())
            .expect("nested `x + 2` node has a projection entry");
        assert_eq!(
            nested_attr.rewritten.nature,
            Nature::Source,
            "an expression root is Source"
        );
        assert_eq!(nested_attr.spans, vec![final_expr_span]);
    }
}

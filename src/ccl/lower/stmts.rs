//! Statement-block lowering: `Let` chains, `if`/`else`, the `http_serve`
//! tuple-assign wiring, and mutation-loop dispatch.

use std::{cell::RefCell, collections::HashSet, rc::Rc, sync::Arc};

use super::*;
use crate::{
    ccl::{BaseType, Branch, Expr, Lit, Type, TypedExprNode},
    chl_parser::ast::{AssignTarget, IfBranch, Lit as ChlLit, Span, Spanned, Stmt as ChlStmt},
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
    let body = rest
        .iter()
        .enumerate()
        .rev()
        .fold(final_expr, |acc, (i, stmt)| {
            let backup = acc.clone();
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
    // (sort for determinism — HashMap iteration is unordered).
    let mut sink_names: Vec<String> = ctx.sink_bindings.keys().cloned().collect();
    sink_names.sort();
    let record = Expr::new(TypedExprNode::Record(
        sink_names
            .iter()
            .map(|n| (n.clone(), Expr::var(n)))
            .collect(),
    ));
    // Place ExprStmt(body, record) at the innermost position of the Let* chain
    // so the Record has the sink Var references in scope.
    Some(append_record_at_tail(body, record))
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
/// [`crate::ccl::desugar_defers`] has extracted all `Feed` nodes from the body,
/// leaving a clean `Let* Record{…}` shape that `compile_program` can pattern-match on.
fn append_record_at_tail(expr: Expr, record: Expr) -> Expr {
    match expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_body = append_record_at_tail(*body, record);
            Expr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(new_body),
                },
                ..expr
            }
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            let new_body = append_record_at_tail(*body, record);
            Expr {
                node: TypedExprNode::ExprStmt {
                    expr: effect,
                    body: Box::new(new_body),
                },
                ..expr
            }
        }
        // Terminal continuation: wrap with ExprStmt so simplify can drop it.
        _ => Expr::expr_stmt(expr, record),
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

    let (last, rest) = stmts.split_last().unwrap();

    // The final statement must be a bare expression, an if/else block, or
    // a for-loop that contains a yield chain (generator pattern).
    let final_expr = lower_final_stmt(last, rest, outer_bindings, ctx)?;

    // Wrap preceding assignments and function definitions in Let bindings,
    // innermost-first.
    rest.iter()
        .enumerate()
        .rev()
        .try_fold(final_expr, |acc, (i, stmt)| {
            lower_middle_stmt(stmt, &rest[..i], acc, outer_bindings, ctx, is_top_level)
        })
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
        ChlStmt::For { target, iter, body } => {
            // Build outer bindings: caller's bindings + all names from rest.
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);
            lower_generator_for(target, iter, body, &scope, ctx)
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
            // Create and register the source now; the caller drains new_sources
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
            let requests_expr = Expr::new(TypedExprNode::Source(source_name.clone()));
            // The responses binding is a plain Defer; the sink is registered by
            // binding name so the scheduler can subscribe it independently.
            let responses_expr = Expr::new(TypedExprNode::Defer);
            ctx.register_sink_binding(resp_name.clone(), sink);
            Ok(Expr::let_bind(
                req_name,
                requests_expr,
                Expr::let_bind(resp_name, responses_expr, body),
            ))
        }
        ChlStmt::Assign { target, value } => {
            let name = extract_name_target(target, "assignment")?;
            let val = lower_expr(value, ctx)?;
            Ok(Expr::let_bind(name, val, body))
        }
        ChlStmt::AnnAssign {
            target,
            annotation,
            value,
        } => {
            let name = extract_name_target(target, "annotated assignment")?;
            let annotation_ty = lower_type_annotation(annotation)?;
            let val = lower_expr(value, ctx)?;
            Ok(Expr::let_bind_annotated(name, val, body, annotation_ty))
        }
        // Desugar `x op= e` → `x = x op e` and lower as a Let binding.
        //
        // Only simple name targets are supported; tuple-destructuring
        // augmented assignment (e.g. `(a, b) += ...`) returns Unsupported.
        ChlStmt::AugAssign { target, op, value } => {
            let name = extract_name_target(target, "augmented assignment")?;
            let val = lower_aug_binop(&name, *op, value, ctx)?;
            Ok(Expr::let_bind(name, val, body))
        }
        // `x <<= e` — defer-define statement, distinct from AugAssign.
        ChlStmt::Define { target, value } => {
            Ok(Expr::expr_stmt(lower_define(target, value, ctx)?, body))
        }
        // Function definition → Let binding with curried lambda body.
        ChlStmt::FunctionDef {
            name,
            params,
            body: fn_body,
        } => {
            let func_expr = lower_function_body(stmt.span, params, fn_body, ctx)?;
            Ok(Expr::let_bind(name.as_str().to_string(), func_expr, body))
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

            // Detect a mutation loop: at least one top-level assignment to
            // a variable from the outer scope.  Yields are not a barrier
            // — a generator with loop-carried state (brainstorm §4b's
            // `running_totals` shape) is just a mutation loop whose body
            // also feeds an auto-generated defer.  The surrounding `body`
            // (the continuation) is threaded into `lower_mutation_loop`
            // so it can lift post-mutation feeds outside the loop and
            // wrap the continuation in the right sequence of `Let` /
            // `ExprStmt(Feed(...))` nodes.
            let acc_names = find_mutation_loop_vars(for_body, &scope);
            if !acc_names.is_empty() {
                return lower_generator_or_mutation_loop(
                    target, iter, for_body, &acc_names, body, ctx,
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
                        "mutation of `{nested}` is nested inside an `if` or \
                     inner `for` in this for-loop body; only top-level \
                     mutations of outer-scope variables are supported \
                     today.  Move the mutation to the top of the loop \
                     body, or rewrite using a generator expression."
                    ),
                ));
            }

            // Otherwise treat as a side-effecting for loop.
            Ok(Expr::expr_stmt(
                lower_generator_for(target, iter, for_body, &scope, ctx)?,
                body,
            ))
        }
        ChlStmt::Expr { .. } | ChlStmt::If { .. } => Ok(Expr::expr_stmt(
            lower_final_stmt(stmt, preceding, outer_bindings, ctx)?,
            body,
        )),
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

/// Lower a CHL type annotation expression to a CCL [`Type`].
///
/// Handles the primitive type names: `int` → [`Type::Base`]([`BaseType::Int`]),
/// `str` → `String`, `bool` → `Bool`, and `None` (the constant) → `Unit`.
pub(super) fn lower_type_annotation(annotation: &Spanned<ChlExpr>) -> Result<Type, LoweringError> {
    match &annotation.node {
        ChlExpr::Name(id) => match id.as_str() {
            "int" => Ok(Type::Base(BaseType::Int)),
            "str" => Ok(Type::Base(BaseType::String)),
            "bool" => Ok(Type::Base(BaseType::Bool)),
            _ => Err(LoweringError::unsupported(
                annotation.span,
                format!("unknown type annotation: {id}"),
            )),
        },
        ChlExpr::Lit(ChlLit::None) => Ok(Type::Base(BaseType::Unit)),
        _ => Err(LoweringError::unsupported(
            annotation.span,
            format!("unsupported type annotation form: {:?}", &annotation.node),
        )),
    }
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
    // Augmented assignment: `x op= e` desugars to `x = x op e`.
    #[case(
        "\
x = 0
x += 1
x",
        "\
let x = 0
in let x = x + 1
in x"
    )]
    #[case(
        "\
x = 10
x -= 3
x",
        "\
let x = 10
in let x = x - 3
in x"
    )]
    #[case(
        "\
x = 2
x *= 5
x",
        "\
let x = 2
in let x = x * 5
in x"
    )]
    #[case(
        "\
x = 7
x //= 2
x",
        "\
let x = 7
in let x = x // 2
in x"
    )]
    // Chained augmented assignments shadow in sequence.
    #[case(
        "\
x = 0
x += 1
x += 2
x",
        "\
let x = 0
in let x = x + 1
in let x = x + 2
in x"
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
}

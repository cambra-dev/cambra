//! Python AST → CCL lowering.
//!
//! Translates [`rustpython_parser`] AST nodes into [`crate::ccl::Expr`] trees.
//! This is a structural lowering only — no type inference, no operator-graph
//! construction, and no subscription. The resulting CCL tree can be inspected
//! and tested independently before being type-checked and compiled.
//!
//! # Supported constructs
//!
//! | Python syntax | CCL output |
//! |--------------|-----------|
//! | Integer / string / bool / None literals | [`Expr::Lit`] |
//! | Variable references | [`Expr::Var`] |
//! | Binary arithmetic (`+`, `-`, `*`, `//`) | [`Expr::BinOp`] |
//! | Comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`) | [`Expr::BinOp`] |
//! | Chained comparisons (`a < b < c`) | nested [`Expr::BinOp`] with `and` |
//! | Boolean operators (`and`, `or`) | left-folded [`Expr::BinOp`] chain |
//! | List literals `[e0, e1, ...]` | [`Expr::List`] |
//! | Single-generator list comprehensions (no `if`) | `Lambda`/`Apply` encoding |
//! | 2-gen equality-join comprehensions (`if x.k == y.k`) | hash-join [`crate::ccl::RefinementKind::HashJoin`] |
//! | Multi-gen filtered comprehensions (non-equality or 3+ generators) | loop-join [`crate::ccl::RefinementKind::Predicate`] |
//! | Assignment + expression blocks | nested [`Expr::Let`] |
//! | Augmented assignment `x op= e` | desugared to [`Expr::Let`] via [`Expr::BinOp`] |
//! | `sum(expr)` / `max(expr)` calls | [`Expr::Aggregate`] |
//! | Lambda expressions `lambda x: body`, `lambda x, y: body` | single [`Expr::Lambda`] (tupled param when multi-arg) |
//! | `groupby(collection, key)` calls | [`Expr::GroupBy`] |
//! | Unary negation (`-x`) | [`Expr::UnaryOp`] with [`crate::ccl::UnaryOpKind::Neg`] |
//! | Boolean negation (`not x`) | [`Expr::UnaryOp`] with [`crate::ccl::UnaryOpKind::Not`] |
//! | Unary plus (`+x`) | identity — lowered to `x` directly |
//! | Single-arg call `f(a)` | [`Expr::Apply`] |
//! | Multi-arg call `f(a, b, ...)` | [`Expr::Apply`] with a tupled argument |
//! | Annotated assignment `x: T = expr` | [`Expr::Let`] with [`crate::ccl::TypedBinding::user_annotation`] set |
//! | Generator expressions `(expr for x in xs)` | `Lambda`/`Apply` encoding (same as list comp) |
//! | Generator functions `def f(xs): for x in xs: yield expr` | [`Expr::Let`] + uncurried [`Expr::Lambda`] wrapping `Lambda`/`Apply` encoding |
//! | Nested-for generator functions | same encoding as multi-generator list comprehensions |
//! | Let-bindings in generator bodies `y = f(x); yield y` | [`Expr::Let`] interleaved in the `Lambda`/`Apply` chain |
//! | Pre-loop lets before generator for-loop | [`Expr::Let`] wrapping the generator expression |
//! | Regular functions `def f(x, y, ...): expr` | [`Expr::Let`] + single [`Expr::Lambda`] (tupled param when multi-arg) |
//! | Record literals `{field: expr, ...}` (identifier keys only) | [`TypedExprNode::Record`] |
//! | Field access `r.field` | [`Expr::Apply`] with [`TypedExprNode::Proj`]`(`[`ProjKey::Field`]`)` |
//!
//! Everything else returns [`LoweringError::Unsupported`].
//!
//! # Name uniqueness
//!
//! This pass does not guarantee unique binding names. Python reassignment of the
//! same variable (`x = 1; x = 2`) produces nested [`Expr::Let`] nodes that shadow
//! each other (`let x = 1 in let x = 2 in ...`). The semantics are correct for
//! sequential code — the inner `let` evaluates its value expression in the outer
//! scope before the shadowing takes effect — but the same name may appear at
//! multiple binding sites in the resulting tree.
//!
//! Unlike SSA or ANF form, CCL does not α-rename each assignment to a fresh variable.
//! This is intentional: the less-normalized representation preserves structure
//! needed for optimization passes.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
    sync::Arc,
};

use rustpython_parser::ast as pyast;

use crate::{
    ccl::{
        AggregateKind, ArithmeticKind, BaseType, BinOpKind, Branch, CompareKind, Expr, Lit,
        LogicKind, RefinementKind, Type, TypedExprNode, UnaryOpKind,
    },
    interpreter::{
        DataSink, DataSourceDomainExtentImpl, HttpServerDataSource, http_server::SharedHttpServer,
    },
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during Python → CCL lowering.
#[derive(Debug, Clone, PartialEq)]
pub enum LoweringError {
    /// The AST node or construct is not yet supported by this lowering pass.
    Unsupported(String),
}

// ---------------------------------------------------------------------------
// Lowering context
// ---------------------------------------------------------------------------

/// Context for Python → CCL lowering that carries registered data sources and sinks.
///
/// Zero-argument function calls whose name appears in `sources` are lowered to
/// [`crate::ccl::Expr::Source`] nodes instead of failing with an
/// [`LoweringError::Unsupported`] error.  After `lower_stmts` returns, the
/// caller should call [`take_sources`](Self::take_sources) and
/// [`take_sink_bindings`](Self::take_sink_bindings) to drain both maps and
/// register each entry with the appropriate downstream contexts.
#[derive(Default)]
pub struct LoweringContext {
    /// All sources for this compilation: pre-registered (e.g. stdin, test sources)
    /// plus any discovered during lowering (e.g. from `http_serve`).  Drained by
    /// [`take_sources`](Self::take_sources) after `lower_stmts` returns so every
    /// source is registered with inference and operator-conversion in one pass.
    sources: HashMap<String, Rc<RefCell<dyn DataSourceDomainExtentImpl>>>,

    /// Sink bindings discovered during lowering, keyed by the CCL `Let`-binding name
    /// that holds the deferred responses computation (e.g. `"responses"`).  Each entry
    /// pairs the binding name with the [`DataSink`] that should receive the computed
    /// tiles (e.g. [`HttpServerSharedState`]).  Drained by
    /// [`take_sink_bindings`](Self::take_sink_bindings) after `lower_stmts` returns.
    sink_bindings: HashMap<String, Arc<dyn DataSink>>,

    /// One [`SharedHttpServer`] per TCP port, shared across all `http_serve` calls
    /// that use the same port.  Created lazily on the first `http_serve` for a port
    /// and reused for all subsequent ones, so only a single `tiny_http::Server`
    /// binds each port.
    shared_servers: HashMap<u16, Arc<SharedHttpServer>>,

    /// Monotonic counter for minting unique synthetic names during lowering.
    /// Globally unique across nested scopes so inner binders cannot capture
    /// a reference inserted by an outer substitution.
    next_synthetic_id: usize,
}

impl LoweringContext {
    /// Register a data source so that `name()` lowers to `Source(name)`.
    pub fn register_source(
        &mut self,
        name: impl Into<String>,
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    ) {
        self.sources.insert(name.into(), source);
    }

    /// Drain all sources accumulated for this compilation.
    ///
    /// Returns every source that was either pre-registered (e.g. stdin, test
    /// stubs) or discovered during lowering (e.g. from `http_serve`).  Call
    /// after `lower_stmts` returns and pass each entry to
    /// [`GlobalContext`](crate::ccl::context::GlobalContext) for uniform
    /// registration with inference and operator-conversion.
    pub fn take_sources(&mut self) -> HashMap<String, Rc<RefCell<dyn DataSourceDomainExtentImpl>>> {
        std::mem::take(&mut self.sources)
    }

    /// Register a sink for the CCL binding named `name`.
    ///
    /// Called during `http_serve` lowering: the responses binding is assigned a
    /// plain `Defer` in the CCL tree, and its [`DataSink`] is recorded here by
    /// binding name so that the scheduler can subscribe an
    /// `HttpServerSinkConsumer` to it after operator conversion.
    pub fn register_sink_binding(&mut self, name: impl Into<String>, sink: Arc<dyn DataSink>) {
        self.sink_bindings.insert(name.into(), sink);
    }

    /// Drain all sink bindings accumulated for this compilation.
    ///
    /// Returns every `(binding_name, DataSink)` pair discovered during lowering
    /// (e.g. from `http_serve`).  Call after `lower_stmts` returns and pass
    /// each entry to [`GlobalContext`](crate::ccl::context::GlobalContext) so
    /// it can extract the corresponding expressions and subscribe them.
    pub fn take_sink_bindings(&mut self) -> HashMap<String, Arc<dyn DataSink>> {
        std::mem::take(&mut self.sink_bindings)
    }

    /// Mint a fresh synthetic parameter name for a multi-arg lambda's tupled
    /// domain, e.g. `__arg_tuple_0`, `__arg_tuple_1`, …
    ///
    /// Each multi-arg lambda gets a distinct name so that substitutions
    /// performed in an outer lambda — which insert `Var(outer_name)` into
    /// the body — do not get captured by an inner lambda's binder of the
    /// same name. All minted names share the [`TUPLE_ARG_PREFIX`] prefix,
    /// which user code cannot bind (double-underscore + synthetic suffix),
    /// so the substitution helper can remain non-capture-avoiding.
    fn fresh_tuple_arg(&mut self) -> String {
        let id = self.next_synthetic_id;
        self.next_synthetic_id += 1;
        format!("{TUPLE_ARG_PREFIX}_{id}")
    }
}

/// Prefix for synthetic parameter names representing the tupled domain of a
/// multi-arg lambda. Each multi-arg lambda's name is this prefix followed by
/// a unique id (see [`LoweringContext::fresh_tuple_arg`]).
const TUPLE_ARG_PREFIX: &str = "__arg_tuple";

/// Return the canonical data-source name for the requests side of
/// `http_serve(port, method, path)`.
///
pub fn http_requests_source_name(port: &str, method: &str, path: &str) -> String {
    // Sanitise path for use inside a Rust/CCL identifier.
    let path_id = path.replace(['/', '-', '.'], "_");
    format!("__http_requests_{port}_{method}_{path_id}")
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Lower a single Python expression to a CCL expression.
pub fn lower_expr(
    expr: &pyast::Located<pyast::ExprKind>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    match &expr.node {
        pyast::ExprKind::Constant { value, .. } => lower_constant(value),
        pyast::ExprKind::Name { id, .. } => Ok(Expr::var(id.clone())),
        pyast::ExprKind::BinOp { left, op, right } => lower_binop(left, op, right, ctx),
        pyast::ExprKind::Compare {
            left,
            ops,
            comparators,
        } => lower_compare(left, ops, comparators, ctx),
        pyast::ExprKind::BoolOp { op, values } => lower_boolop(op, values, ctx),
        pyast::ExprKind::List { elts, .. } => {
            let items: Result<Vec<_>, _> = elts.iter().map(|e| lower_expr(e, ctx)).collect();
            Ok(Expr::list(items?))
        }
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(elt, generators, ctx),
        pyast::ExprKind::GeneratorExp { elt, generators } => lower_list_comp(elt, generators, ctx),
        pyast::ExprKind::Call {
            func,
            args,
            keywords,
        } => lower_call(func, args, keywords, ctx),
        pyast::ExprKind::Tuple { elts, .. } => {
            let items: Result<Vec<_>, _> = elts.iter().map(|e| lower_expr(e, ctx)).collect();
            Ok(Expr::tuple(items?))
        }
        pyast::ExprKind::Subscript { value, slice, .. } => match &slice.node {
            pyast::ExprKind::Constant {
                value: pyast::Constant::Int(n),
                ..
            } => {
                let idx: usize = n.try_into().map_err(|_| {
                    LoweringError::Unsupported("Tuple index must be non-negative".into())
                })?;
                Ok(Expr::apply(lower_expr(value, ctx)?, Expr::proj_index(idx)))
            }
            _ => Err(LoweringError::Unsupported(
                "Only integer subscripts are supported".into(),
            )),
        },
        // Dict literal `{field: expr, ...}` — keys must be bare identifiers.
        // Lowered to a `Record` constructor: `{x: 1, y: "foo"}` becomes
        // `Record([("x", Lit(1)), ("y", Lit("foo"))])`.
        pyast::ExprKind::Dict { keys, values } => {
            let mut fields = Vec::with_capacity(keys.len());
            for (key, value) in keys.iter().zip(values.iter()) {
                let field_name = match &key.node {
                    pyast::ExprKind::Name { id, .. } => id.clone(),
                    _ => {
                        return Err(LoweringError::Unsupported(
                            "record literal keys must be bare identifiers".into(),
                        ));
                    }
                };
                if fields.iter().any(|(k, _)| k == &field_name) {
                    return Err(LoweringError::Unsupported(format!(
                        "duplicate key `{field_name}` in record literal"
                    )));
                }
                fields.push((field_name, lower_expr(value, ctx)?));
            }
            Ok(Expr::new(TypedExprNode::Record(fields)))
        }
        // Attribute access `r.field` → `Apply(r, Proj(Field("field")))`.
        pyast::ExprKind::Attribute { value, attr, .. } => {
            Ok(Expr::apply(lower_expr(value, ctx)?, Expr::proj_field(attr)))
        }
        pyast::ExprKind::Lambda { args, body } => lower_lambda(args, body, ctx),
        pyast::ExprKind::UnaryOp { op, operand } => lower_unaryop(op, operand, ctx),
        // Ternary `value if test else orelse` → Case { [guard → value, true → orelse] }
        pyast::ExprKind::IfExp { test, body, orelse } => {
            let guard = lower_expr(test, ctx)?;
            let true_arm = lower_expr(body, ctx)?;
            let false_arm = lower_expr(orelse, ctx)?;
            Ok(Expr::new(TypedExprNode::Case {
                branches: vec![
                    Branch {
                        guard,
                        body: true_arm,
                    },
                    Branch {
                        guard: Expr::lit(Lit::Bool(true)),
                        body: false_arm,
                    },
                ],
            }))
        }
        _ => Err(LoweringError::Unsupported(format!(
            "Expression type not supported: {:?}",
            expr.node
        ))),
    }
}

/// Lower a block of Python statements to a nested CCL expression.
///
/// All statements except the last must be simple name assignments
/// (`x = expr`), annotated assignments (`x: T = expr`), augmented
/// assignments (`x op= expr`), or function definitions (`def f(...): ...`);
/// each becomes an [`Expr::Let`] binding wrapping the rest. Function
/// definitions are lowered via [`lower_function_body`], which detects
/// generator functions (single `for`/`yield` body) and regular functions.
///
/// The last statement must be a bare expression (`StmtKind::Expr`)
/// or an `if`/`else` block.
///
/// When sink bindings are registered during lowering (e.g. from `http_serve`),
/// the final expression is wrapped so the program ends in
/// `ExprStmt(<body>, Record{sink: Var(sink), …})`.  The `Record` is the
/// sink-binding contract; each field is the name that `remove_defers`
/// resolves to the computed response morphism.  After `remove_defers`
/// removes all `Feed` nodes, `simplify` drops the `ExprStmt`, leaving a clean
/// `Let* Record{…}` shape for `compile_program`.
pub fn lower_stmts(
    stmts: &[pyast::Stmt],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let inner = lower_stmts_inner(stmts, &HashSet::new(), ctx, true)?;
    if ctx.sink_bindings.is_empty() {
        return Ok(inner);
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
    Ok(append_record_at_tail(inner, record))
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
/// `remove_defers` has extracted all `Feed` nodes from the body, leaving a
/// clean `Let* Record{…}` shape that `compile_program` can pattern-match on.
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
fn lower_stmts_inner(
    stmts: &[pyast::Stmt],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
    is_top_level: bool,
) -> Result<Expr, LoweringError> {
    if stmts.is_empty() {
        return Err(LoweringError::Unsupported("Empty statement block".into()));
    }

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
fn lower_final_stmt(
    last: &pyast::Stmt,
    preceding: &[pyast::Stmt],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    match &last.node {
        pyast::StmtKind::Expr { value } => lower_expr(value, ctx),
        pyast::StmtKind::If { test, body, orelse } => {
            // Propagate outer bindings + rest names so that generator-fors
            // inside the if branches can check for mutation correctly.
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);
            lower_if(test, body, orelse, &scope, ctx)
        }
        pyast::StmtKind::For {
            target,
            iter,
            body,
            orelse,
            ..
        } => {
            if !orelse.is_empty() {
                return Err(LoweringError::Unsupported(
                    "for/else is not supported".into(),
                ));
            }
            // Build outer bindings: caller's bindings + all names from rest.
            let mut scope = outer_bindings.clone();
            collect_stmt_names(preceding, &mut scope);
            lower_generator_for(target, iter, body, &scope, ctx)
        }
        _ => Err(LoweringError::Unsupported(
            "Last statement must be a bare expression, if/else, or \
                 for/yield generator loop"
                .into(),
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
fn lower_middle_stmt(
    stmt: &pyast::Stmt,
    preceding: &[pyast::Stmt],
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
        pyast::StmtKind::Assign { targets, value, .. }
            if targets.len() == 1 && is_http_serve_tuple_assign(&targets[0], value) =>
        {
            if !is_top_level {
                return Err(LoweringError::Unsupported(
                    "http_serve is only supported at the top level of a program, \
                     not inside an if/else branch or function body"
                        .into(),
                ));
            }
            let (req_name, resp_name) = extract_http_serve_names(&targets[0])?;
            let (port, method, path) = extract_http_serve_args(value)?;
            // Create and register the source now; the caller drains new_sources
            // via take_new_sources() after lower_stmts returns, before type inference.
            let port_u16: u16 = port.parse().map_err(|_| {
                LoweringError::Unsupported(format!("http_serve port must be a u16, got {port:?}"))
            })?;
            // Share one tiny_http::Server per port across all http_serve routes.
            if let std::collections::hash_map::Entry::Vacant(e) = ctx.shared_servers.entry(port_u16)
            {
                let server = SharedHttpServer::new(port_u16).map_err(|e| {
                    LoweringError::Unsupported(format!(
                        "http_serve: failed to bind port {port_u16}: {e}"
                    ))
                })?;
                e.insert(Arc::new(server));
            }
            let server = ctx.shared_servers[&port_u16].clone();
            let source_name = http_requests_source_name(&port, &method, &path);
            if ctx.sources.contains_key(&source_name) {
                return Err(LoweringError::Unsupported(format!(
                    "duplicate http_serve registration: port={port}, method={method}, path={path}"
                )));
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
        pyast::StmtKind::Assign { targets, value, .. } => {
            if targets.len() != 1 {
                return Err(LoweringError::Unsupported(
                    "Multiple assignment targets not supported".into(),
                ));
            }
            let name = extract_name_target(&targets[0], "assignment")?;
            let val = lower_expr(value, ctx)?;
            Ok(Expr::let_bind(name, val, body))
        }
        pyast::StmtKind::AnnAssign {
            target,
            annotation,
            value: Some(value),
            ..
        } => {
            let name = extract_name_target(target, "annotated assignment")?;
            let annotation_ty = lower_type_annotation(annotation)?;
            let val = lower_expr(value, ctx)?;
            Ok(Expr::let_bind_annotated(name, val, body, annotation_ty))
        }
        pyast::StmtKind::AnnAssign { value: None, .. } => Err(LoweringError::Unsupported(
            "Annotated assignment without a value is not supported".into(),
        )),
        // Desugar `x op= e` → `x = x op e` and lower as a Let binding.
        //
        // Only simple name targets are supported; subscript and attribute
        // targets (e.g. `x[0] += 1`, `x.field += 1`) return Unsupported.
        pyast::StmtKind::AugAssign { target, op, value } => {
            if *op == pyast::Operator::LShift {
                return Ok(Expr::expr_stmt(lower_define(target, value, ctx)?, body));
            }
            let name = extract_name_target(target, "augmented assignment")?;
            let val = lower_binop(target, op, value, ctx)?;
            Ok(Expr::let_bind(name, val, body))
        }
        // Function definition → Let binding with curried lambda body.
        pyast::StmtKind::FunctionDef {
            name,
            args,
            body: fn_body,
            decorator_list,
            ..
        } => {
            if !decorator_list.is_empty() {
                return Err(LoweringError::Unsupported(
                    "Function decorators are not supported".into(),
                ));
            }
            let func_expr = lower_function_body(args, fn_body, ctx)?;
            Ok(Expr::let_bind(name.clone(), func_expr, body))
        }
        pyast::StmtKind::Expr { .. } | pyast::StmtKind::If { .. } | pyast::StmtKind::For { .. } => {
            Ok(Expr::expr_stmt(
                lower_final_stmt(stmt, preceding, outer_bindings, ctx)?,
                body,
            ))
        }
        _ => Err(LoweringError::Unsupported(
            "Only assignment and function definition statements are supported \
             before the final expression"
                .into(),
        )),
    }
}

/// Collect simple-name targets from assignment / function-def statements
/// into `names`. Used to build `outer_bindings` for mutation checks.
fn collect_stmt_names(stmts: &[pyast::Stmt], names: &mut HashSet<String>) {
    for stmt in stmts {
        match &stmt.node {
            pyast::StmtKind::Assign { targets, .. } => {
                if let Some(pyast::ExprKind::Name { id, .. }) = targets.first().map(|t| &t.node) {
                    names.insert(id.clone());
                }
            }
            pyast::StmtKind::AnnAssign { target, .. }
            | pyast::StmtKind::AugAssign { target, .. } => {
                if let pyast::ExprKind::Name { id, .. } = &target.node {
                    names.insert(id.clone());
                }
            }
            pyast::StmtKind::FunctionDef { name, .. } => {
                names.insert(name.clone());
            }
            _ => {}
        }
    }
}

/// Extract a simple variable name from a Python assignment target.
///
/// Returns the name as a [`String`] when the target is an [`ExprKind::Name`],
/// or [`LoweringError::Unsupported`] for destructuring, subscript, or attribute
/// targets.
fn extract_name_target(target: &pyast::Expr, context: &str) -> Result<String, LoweringError> {
    match &target.node {
        pyast::ExprKind::Name { id, .. } => Ok(id.clone()),
        _ => Err(LoweringError::Unsupported(format!(
            "{context}: only simple name targets are supported"
        ))),
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Lower a Python type annotation expression to a CCL [`Type`].
///
/// Handles the primitive type names: `int` → [`Type::Base`]([`BaseType::Int`]),
/// `str` → `String`, `bool` → `Bool`, and `None` (the constant) → `Unit`.
fn lower_type_annotation(annotation: &pyast::Expr) -> Result<Type, LoweringError> {
    match &annotation.node {
        pyast::ExprKind::Name { id, .. } => match id.as_str() {
            "int" => Ok(Type::Base(BaseType::Int)),
            "str" => Ok(Type::Base(BaseType::String)),
            "bool" => Ok(Type::Base(BaseType::Bool)),
            _ => Err(LoweringError::Unsupported(format!(
                "Unknown type annotation: {id}"
            ))),
        },
        pyast::ExprKind::Constant {
            value: pyast::Constant::None,
            ..
        } => Ok(Type::Base(BaseType::Unit)),
        _ => Err(LoweringError::Unsupported(format!(
            "Unsupported type annotation form: {:?}",
            &annotation.node
        ))),
    }
}

/// Lower a `StmtKind::If` (or `elif` chain) to a [`TypedExprNode::Case`] expression.
///
/// The condition becomes the first branch guard and the `then` block becomes its
/// body. `elif` chains are **flattened**: when `orelse` lowers to a [`TypedExprNode::Case`],
/// its branches are appended directly rather than nested, producing a single flat
/// `Case` with one [`Branch`] per condition. A plain `else` block becomes the
/// final branch with an always-`true` guard.
///
/// A bare `if` without an `else` clause is not value-returning and is rejected
/// with [`LoweringError::Unsupported`].
fn lower_if(
    test: &pyast::Expr,
    body: &[pyast::Stmt],
    orelse: &[pyast::Stmt],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if orelse.is_empty() {
        return Err(LoweringError::Unsupported(
            "if without else is not supported as a value-returning expression".into(),
        ));
    }
    let guard = lower_expr(test, ctx)?;
    // http_serve is not permitted inside if/else arms.
    let true_arm = lower_stmts_inner(body, outer_bindings, ctx, false)?;
    let false_arm = lower_stmts_inner(orelse, outer_bindings, ctx, false)?;
    // Flatten elif chains: if the else branch is itself a Case, extend our
    // branches with its branches rather than nesting.
    let mut branches = vec![Branch {
        guard,
        body: true_arm,
    }];
    if let TypedExprNode::Case { branches: inner } = false_arm.node {
        branches.extend(inner);
    } else {
        branches.push(Branch {
            guard: Expr::lit(Lit::Bool(true)),
            body: false_arm,
        });
    }
    Ok(Expr::new(TypedExprNode::Case { branches }))
}

fn lower_constant(constant: &pyast::Constant) -> Result<Expr, LoweringError> {
    let lit = match constant {
        pyast::Constant::Int(n) => {
            let n_i64: i64 = n
                .try_into()
                .map_err(|_| LoweringError::Unsupported("Integer too large for i64".into()))?;
            Lit::Int(n_i64)
        }
        pyast::Constant::Str(s) => Lit::String(s.clone()),
        pyast::Constant::Bool(b) => Lit::Bool(*b),
        pyast::Constant::None => Lit::Unit,
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Constant type not supported: {constant:?}"
            )));
        }
    };
    Ok(Expr::lit(lit))
}

/// Lower a Python function call to a CCL built-in expression.
///
/// Supported built-ins:
///
/// | Python call | CCL node | Arity |
/// |---|---|---|
/// | `sum(expr)` | [`Expr::Aggregate`] (`Sum`) | 1 |
/// | `max(expr)` | [`Expr::Aggregate`] (`Max`) | 1 |
/// | `groupby(collection, key)` | [`Expr::GroupBy`] | 2 |
///
/// Keyword arguments and unknown function names return
/// [`LoweringError::Unsupported`].
fn lower_call(
    func: &pyast::Expr,
    args: &[pyast::Expr],
    keywords: &[pyast::Keyword],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if !keywords.is_empty() {
        return Err(LoweringError::Unsupported(
            "Keyword arguments not supported in function calls".into(),
        ));
    }
    let name = match &func.node {
        pyast::ExprKind::Name { id, .. } => id.as_str(),
        _ => {
            return Err(LoweringError::Unsupported(
                "Only named function calls are supported".into(),
            ));
        }
    };

    match name {
        // groupby(c: I -> A, key_fn: A -> K) lowers to
        // λ k → λ i :(I | key_fn(c(i)) == k) → c(i)
        "groupby" => {
            if args.len() != 2 {
                return Err(LoweringError::Unsupported(
                    "groupby requires exactly two arguments".into(),
                ));
            }
            let collection = lower_expr(&args[0], ctx)?;
            let key_fn = lower_expr(&args[1], ctx)?;

            Ok(Expr::lambda(
                "__gb_k",
                Type::Hole,
                Expr::lambda_with_refinement(
                    "__gb_i",
                    Type::Hole,
                    Expr::apply(Expr::var("__gb_i"), collection.clone()),
                    Expr::lambda(
                        "__gb_r",
                        Type::Hole,
                        Expr::binop(
                            Expr::apply(Expr::apply(Expr::var("__gb_r"), collection), key_fn),
                            BinOpKind::Compare(CompareKind::Equals),
                            Expr::var("__gb_k"),
                        ),
                    ),
                    "groupby",
                ),
            ))
        }
        "sum" | "max" => {
            if args.len() != 1 {
                return Err(LoweringError::Unsupported(
                    "Aggregate functions require exactly one argument".into(),
                ));
            }
            let kind = match name {
                "sum" => AggregateKind::Sum,
                "max" => AggregateKind::Max,
                _ => unreachable!(),
            };
            let input = lower_expr(&args[0], ctx)?;
            Ok(Expr::aggregate(input, kind))
        }
        "defer" => Ok(Expr::new(TypedExprNode::Defer)),
        name if ctx.sources.contains_key(name) => {
            Ok(Expr::new(TypedExprNode::Source(name.to_string())))
        }
        _ => {
            // For zero-argument calls, only registered sources are allowed.
            if args.is_empty() {
                return Err(LoweringError::Unsupported(format!(
                    "Unknown zero-argument function: {name}; register it as a data source"
                )));
            }
            // Single-arg call: direct application `f(a)` → `Apply(a, f)`.
            if args.len() == 1 {
                let arg = lower_expr(&args[0], ctx)?;
                return Ok(Expr::apply(arg, Expr::var(name.to_string())));
            }
            // Multi-arg call: tuple the arguments and apply once,
            // `f(a, b, ...)` → `Apply(Tuple([a, b, ...]), f)`. This pairs with
            // the uncurried multi-arg lambda lowering in [`lower_lambda`] so
            // that syntactic multi-arg functions compile without any `curry`
            // combinator appearing in the tree.
            let tupled: Result<Vec<_>, _> = args.iter().map(|a| lower_expr(a, ctx)).collect();
            let arg_tuple = Expr::tuple(tupled?);
            Ok(Expr::apply(arg_tuple, Expr::var(name.to_string())))
        }
    }
}

fn lower_binop(
    left: &pyast::Located<pyast::ExprKind>,
    op: &pyast::Operator,
    right: &pyast::Located<pyast::ExprKind>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if *op == pyast::Operator::LShift {
        return lower_feed(left, right, ctx);
    }
    let left_expr = lower_expr(left, ctx)?;
    let right_expr = lower_expr(right, ctx)?;
    let kind = match op {
        pyast::Operator::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        pyast::Operator::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        pyast::Operator::Mult => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        pyast::Operator::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        pyast::Operator::BitAnd => BinOpKind::BoolLogic(LogicKind::And),
        pyast::Operator::MatMult => BinOpKind::CollectionUnion,
        pyast::Operator::BitOr => BinOpKind::BoolLogic(LogicKind::Or),
        pyast::Operator::BitXor => BinOpKind::BoolLogic(LogicKind::Xor),
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Binary operator not supported: {op:?}"
            )));
        }
    };
    Ok(Expr::binop(left_expr, kind, right_expr))
}

fn lower_feed(
    target: &pyast::Expr,
    value: &pyast::Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let name = extract_name_target(target, "handle binding")?;
    Ok(Expr::feed(name, lower_expr(value, ctx)?))
}

fn lower_define(
    target: &pyast::Expr,
    value: &pyast::Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let name = extract_name_target(target, "handle defining")?;
    Ok(Expr::define(name, lower_expr(value, ctx)?))
}

/// Lower a Python unary expression to a CCL [`Expr::UnaryOp`].
///
/// - `USub` (`-x`) lowers to [`UnaryOpKind::Neg`].
/// - `Not` (`not x`) lowers to [`UnaryOpKind::Not`].
/// - `UAdd` (`+x`) is a no-op identity and unsuppored; returns [`LoweringError::Unsupported`].
/// - `Invert` (`~x`) is unsupported and returns [`LoweringError::Unsupported`].
fn lower_unaryop(
    op: &pyast::Unaryop,
    operand: &pyast::Located<pyast::ExprKind>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let inner = lower_expr(operand, ctx)?;
    let kind = match op {
        pyast::Unaryop::USub => UnaryOpKind::Neg,
        pyast::Unaryop::Not => UnaryOpKind::Not,
        // Unary plus is a no-op identity in Python; we don't support it.
        pyast::Unaryop::UAdd => {
            return Err(LoweringError::Unsupported(
                "Unary Add (+) is not supported".into(),
            ));
        }
        pyast::Unaryop::Invert => {
            return Err(LoweringError::Unsupported(
                "Bitwise invert (~) is not supported".into(),
            ));
        }
    };
    // Constant-fold `-Int(n)` to `Lit(Int(-n))`. Python's parser leaves negative
    // numeric literals as `UnaryOp(USub, Lit(n))`, but downstream stages
    // (`operator_conversion`'s list-literal path in particular) only accept
    // concrete literals as list elements. Folding here keeps
    // `[-1, 2, -3, 4]`-style programs in the supported subset.
    if let UnaryOpKind::Neg = kind
        && let TypedExprNode::Lit(Lit::Int(n)) = &inner.node
    {
        return Ok(Expr::lit(Lit::Int(-*n)));
    }
    Ok(Expr::unary(kind, inner))
}

/// Lower a Python comparison expression to a CCL [`Expr::BinOp`] chain.
///
/// Python comparison expressions may chain multiple operators, e.g. `a < b < c`
/// desugars to `a < b and b < c`. Each consecutive pair of operands is compared
/// with its corresponding operator and the results are combined with logical AND.
///
/// Unsupported operators (`is`, `is not`, `in`, `not in`) return
/// [`LoweringError::Unsupported`].
fn lower_compare(
    left: &pyast::Located<pyast::ExprKind>,
    ops: &[pyast::Cmpop],
    comparators: &[pyast::Located<pyast::ExprKind>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Lower all operands up-front. For a chain of n ops there are n+1 operands:
    // left, comparators[0], comparators[1], …
    let mut operands: Vec<Expr> = Vec::with_capacity(comparators.len() + 1);
    operands.push(lower_expr(left, ctx)?);
    for comp in comparators {
        operands.push(lower_expr(comp, ctx)?);
    }

    // Build one BinOp per (op, adjacent-operand-pair).
    let mut comparisons: Vec<Expr> = Vec::with_capacity(ops.len());
    for (i, op) in ops.iter().enumerate() {
        let kind = match op {
            pyast::Cmpop::Eq => CompareKind::Equals,
            pyast::Cmpop::NotEq => CompareKind::NotEquals,
            pyast::Cmpop::Lt => CompareKind::Less,
            pyast::Cmpop::LtE => CompareKind::LessOrEq,
            pyast::Cmpop::Gt => CompareKind::Greater,
            pyast::Cmpop::GtE => CompareKind::GreaterOrEq,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Comparison operator not supported: {op:?}"
                )));
            }
        };
        // Clone the shared middle operand so both adjacent pairs can own it.
        comparisons.push(Expr::binop(
            operands[i].clone(),
            BinOpKind::Compare(kind),
            operands[i + 1].clone(),
        ));
    }

    // Single comparison: return it directly.
    // Chained comparisons: fold with logical AND (mirrors Python semantics).
    Ok(comparisons
        .into_iter()
        .reduce(|acc, cmp| Expr::binop(acc, BinOpKind::BoolLogic(LogicKind::And), cmp))
        .expect("ops is non-empty"))
}

/// Lower a Python boolean operator expression to a left-folded [`Expr::BinOp`] chain.
///
/// Python `BoolOp` carries a list of two or more operands sharing a single
/// operator (`and` / `or`). For example, `a and b and c` becomes
/// `(a and b) and c` — two nested [`BinOpKind::BoolLogic`] nodes.
fn lower_boolop(
    op: &pyast::Boolop,
    values: &[pyast::Located<pyast::ExprKind>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if values.len() < 2 {
        return Err(LoweringError::Unsupported(
            "Boolean operator must have at least two operands".into(),
        ));
    }
    let kind = match op {
        pyast::Boolop::And => BinOpKind::BoolLogic(LogicKind::And),
        pyast::Boolop::Or => BinOpKind::BoolLogic(LogicKind::Or),
    };
    // Fold left-to-right: `a and b and c` → `(a and b) and c`.
    let mut acc = lower_expr(&values[0], ctx)?;
    for value in &values[1..] {
        acc = Expr::binop(acc, kind, lower_expr(value, ctx)?);
    }
    Ok(acc)
}

/// Validate that function or lambda arguments use only supported features.
///
/// Rejects `*args`, `**kwargs`, keyword-only arguments, default values, and
/// parameterless signatures. Shared between [`lower_lambda`] and
/// [`lower_function_body`].
fn validate_function_args(args: &pyast::Arguments) -> Result<(), LoweringError> {
    if args.vararg.is_some() {
        return Err(LoweringError::Unsupported(
            "Function/lambda *args not supported".into(),
        ));
    }
    if args.kwarg.is_some() {
        return Err(LoweringError::Unsupported(
            "Function/lambda **kwargs not supported".into(),
        ));
    }
    if !args.kwonlyargs.is_empty() {
        return Err(LoweringError::Unsupported(
            "Function/lambda keyword-only arguments not supported".into(),
        ));
    }
    if !args.defaults.is_empty() {
        return Err(LoweringError::Unsupported(
            "Function/lambda default arguments not supported".into(),
        ));
    }
    if args.args.is_empty() {
        return Err(LoweringError::Unsupported(
            "Function/lambda with no parameters not supported".into(),
        ));
    }
    Ok(())
}

/// Wrap `body_expr` in a single uncurried lambda over `args`.
///
/// Single-arg `(x): body` → `λ x → body`.
///
/// Multi-arg `(x, y, ...): body` becomes a single lambda whose parameter is
/// a synthetic tuple `__arg_tuple_<N>`, with each named argument substituted
/// in the body by its projection of that tuple:
///
/// ```text
/// (x, y): body  ⟹  λ __arg_tuple_N → body[x := __arg_tuple_N.0,
///                                          y := __arg_tuple_N.1]
/// ```
///
/// Each multi-arg call mints a fresh `N` via
/// [`LoweringContext::fresh_tuple_arg`] so that nested multi-arg
/// lambdas/defs cannot capture each other's tuple parameter; without the
/// unique suffix, an outer substitution inserting `Var("__arg_tuple")` into
/// an inner lambda's body would be captured by the inner binder of the same
/// name.
///
/// In-place substitution (rather than wrapping the body in `let`-bindings)
/// avoids introducing function-typed `Let` nodes; when `lambda_elim`
/// rewrites a `Let` under a lambda, the bound variable's type is lifted to
/// `ParamTy ⇒ T`, producing `zip(.0, .1)`-shaped morphisms that downstream
/// passes would then need to simplify back to `id` before operator
/// conversion can compile them (simplify has no such rule today).
/// Substitution sidesteps that whole rewrite chain.
///
/// Shared between [`lower_lambda`] and [`lower_function_body`] so that both
/// `lambda x, y: …` and `def f(x, y): …` pair with [`lower_call`]'s
/// tupled-argument shape and never emit a curried `Expr::Lambda` chain that
/// `lambda_elim` would fold into an unsupported `curry(body)`.
fn uncurry_params(args: &pyast::Arguments, body_expr: Expr, ctx: &mut LoweringContext) -> Expr {
    if args.args.len() == 1 {
        return Expr::lambda(&args.args[0].node.arg, Type::Hole, body_expr);
    }
    // Mint the tuple name after `body_expr` is lowered so that inner
    // multi-arg lambdas (which bump the counter during body lowering)
    // receive strictly smaller ids than the outer lambda. Together with
    // the reserved `__arg_tuple_` prefix (user code cannot bind
    // double-underscore names here), this guarantees the outer
    // substitution's inserted `Var(outer_name)` never collides with an
    // inner binder.
    let tuple_name = ctx.fresh_tuple_arg();
    let body_with_subs = args
        .args
        .iter()
        .enumerate()
        .fold(body_expr, |acc, (i, arg)| {
            let proj = Expr::apply(Expr::var(&tuple_name), Expr::proj_index(i));
            substitute_param_in_body(acc, &arg.node.arg, &proj)
        });
    Expr::lambda(&tuple_name, Type::Hole, body_with_subs)
}

/// Lower a Python lambda expression to an [`Expr::Lambda`] via
/// [`uncurry_params`].
///
/// Users who want genuine currying still write it explicitly
/// (`lambda x: lambda y: ...` or an explicit `curry(f)` call); those nest
/// through the general Lambda rule and remain unsupported past operator
/// conversion — tracked as follow-up work.
///
/// Unsupported features (`*args`, `**kwargs`, default values, keyword-only
/// arguments) return [`LoweringError::Unsupported`].
fn lower_lambda(
    args: &pyast::Arguments,
    body: &pyast::Located<pyast::ExprKind>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    validate_function_args(args)?;
    let body_expr = lower_expr(body, ctx)?;
    Ok(uncurry_params(args, body_expr, ctx))
}

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`,
/// respecting binder shadowing introduced by inner `Lambda` and `Let` nodes.
///
/// Used during multi-arg lambda lowering to rewrite named Python parameters
/// as projections of a synthetic pair variable. This is a pre-inference
/// substitution, so unlike [`crate::ccl::lambda_elim::substitute`] it does
/// not invoke `debug_typecheck`; callers can pass `Type::Hole`-typed trees.
///
/// Does **not** perform capture-avoiding renaming — the caller must ensure
/// `replacement` contains no free variables that collide with binders in
/// `expr`. For the [`lower_lambda`] call site this is guaranteed by two
/// invariants: (1) the replacement `Var` uses the `__arg_tuple_` prefix
/// that user code cannot bind, and (2) each multi-arg lambda mints a
/// fresh unique id via [`LoweringContext::fresh_tuple_arg`], so no two
/// nested multi-arg lambdas can share a tuple-parameter name.
fn substitute_param_in_body(expr: Expr, name: &str, replacement: &Expr) -> Expr {
    // Fast path for atoms that need no traversal.
    match &expr.node {
        TypedExprNode::Var(n) if n == name => return replacement.clone(),
        TypedExprNode::Var(_)
        | TypedExprNode::Lit(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_) => return expr,
        _ => {}
    }

    let Expr {
        node,
        ty,
        user_annotation,
    } = expr;

    let recurse = |e: Expr| substitute_param_in_body(e, name, replacement);

    let new_node = match node {
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } if param.name == name => {
            // `name` is shadowed by this lambda's param; leave body and
            // refinement alone (the refinement is in this lambda's scope too).
            TypedExprNode::Lambda {
                param,
                body,
                refinement,
            }
        }
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            // Refinements may reference outer-scope names (e.g. list-comp
            // guards that close over an enclosing function parameter), so
            // substitute through the predicate expression as well. The
            // `Rc<RefCell<>>` is freshly allocated during lowering and not
            // yet shared, so mutating in place is safe.
            if let Some(r) = &refinement {
                let RefinementKind::Predicate(pred) = &r.kind;
                let inner = pred.borrow().clone();
                *pred.borrow_mut() = substitute_param_in_body(inner, name, replacement);
            }
            TypedExprNode::Lambda {
                param,
                body: Box::new(recurse(*body)),
                refinement,
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_bound = recurse(*bound_expr);
            // Shadowing: if the Let rebinds `name`, leave its body alone.
            let new_body = if binding.name == name {
                *body
            } else {
                recurse(*body)
            };
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(new_bound),
                body: Box::new(new_body),
            }
        }
        TypedExprNode::Apply { function, argument } => TypedExprNode::Apply {
            function: Box::new(recurse(*function)),
            argument: Box::new(recurse(*argument)),
        },
        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(recurse(*left)),
            op,
            right: Box::new(recurse(*right)),
        },
        TypedExprNode::UnaryOp(op, inner) => TypedExprNode::UnaryOp(op, Box::new(recurse(*inner))),
        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(elts.into_iter().map(recurse).collect()),
        TypedExprNode::List(elts) => TypedExprNode::List(elts.into_iter().map(recurse).collect()),
        TypedExprNode::Record(fields) => {
            TypedExprNode::Record(fields.into_iter().map(|(k, e)| (k, recurse(e))).collect())
        }
        TypedExprNode::Case { branches } => TypedExprNode::Case {
            branches: branches
                .into_iter()
                .map(|b| Branch {
                    guard: recurse(b.guard),
                    body: recurse(b.body),
                })
                .collect(),
        },
        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(recurse(*input)),
            kind,
        },
        TypedExprNode::Compose(elts) => {
            TypedExprNode::Compose(elts.into_iter().map(recurse).collect())
        }
        TypedExprNode::ExprStmt { expr, body } => TypedExprNode::ExprStmt {
            expr: Box::new(recurse(*expr)),
            body: Box::new(recurse(*body)),
        },
        TypedExprNode::Feed { name: id, value } => TypedExprNode::Feed {
            name: id,
            value: Box::new(recurse(*value)),
        },
        TypedExprNode::Define { name: id, value } => TypedExprNode::Define {
            name: id,
            value: Box::new(recurse(*value)),
        },
        TypedExprNode::Defer => TypedExprNode::Defer,
        // Leaves handled by the fast path above, but enumerate here so the
        // match is exhaustive and future additions are caught at compile time.
        node @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)) => node,
        // Lowering does not produce Join/Jump, so passing through is safe.
        TypedExprNode::Join {
            name: n,
            params,
            loop_body,
            outer_body,
        } => TypedExprNode::Join {
            name: n,
            params,
            loop_body: Box::new(recurse(*loop_body)),
            outer_body: Box::new(recurse(*outer_body)),
        },
        TypedExprNode::Jump { target, args } => TypedExprNode::Jump {
            target,
            args: args.into_iter().map(recurse).collect(),
        },
    };

    Expr {
        node: new_node,
        ty,
        user_annotation,
    }
}

// ---------------------------------------------------------------------------
// Generator lowering — data structures
// ---------------------------------------------------------------------------

/// One generator clause in a flattened generator-function chain.
///
/// Each `for` loop in the chain produces one `GeneratorSpec`. The `steps`
/// list captures let-bindings and if-guards encountered between this `for`
/// and the next `for` (or the terminal `yield`), in source order.
struct GeneratorSpec {
    /// Loop variable name (always a simple `Name` target in supported
    /// programs).
    iter_var: String,
    /// Lowered iterable expression.
    source: Expr,
    /// Interleaved let-bindings and guards, in source order.
    steps: Vec<BodyStep>,
    /// Names introduced at this frame: the iteration variable plus any
    /// let-bound names. Used by the mutation check.
    introduced: HashSet<String>,
}

/// A single step in a generator body between the enclosing `for` and the
/// next nested `for` (or the terminal `yield`).
enum BodyStep {
    /// Let-binding from an Assign, AnnAssign, AugAssign, or FunctionDef
    /// statement. The `value` is already lowered to CCL.
    Let(LetStep),
    /// Guard from `if cond:` (no else). The `cond` is already lowered; the
    /// `desc` is a human-readable string for the refinement annotation.
    Guard { cond: Expr, desc: String },
}

/// A single let-binding produced during generator chain walking.
struct LetStep {
    name: String,
    value: Expr,
    annotation: Option<Type>,
}

// ---------------------------------------------------------------------------
// Generator lowering — chain walker
// ---------------------------------------------------------------------------

/// Walk a chain of nested `for` / `if` / `yield` / `let` statements,
/// appending one [`GeneratorSpec`] per `for` to `chain` and returning a
/// reference to the innermost yield value expression.
///
/// Each for-body is parsed as `chain ::= step* term` where:
/// - `step` ∈ {Assign, AnnAssign, AugAssign, FunctionDef}
/// - `term` ∈ {`yield expr`, `if cond: chain`, `for target in iter: chain`}
///
/// The mutation rule: an assignment `name = expr` is a let-binding iff
/// `name` is either fresh (not previously bound) or in the current for's
/// `introduced` set. If `name` is in an outer for-frame or in
/// `outer_bindings` (function args + pre-loop lets), it's mutation and
/// rejected.
fn collect_chain<'ast>(
    stmts: &'ast [pyast::Stmt],
    chain: &mut Vec<GeneratorSpec>,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<&'ast pyast::Expr, LoweringError> {
    if stmts.is_empty() {
        return Err(LoweringError::Unsupported(
            "Empty generator for-loop body".into(),
        ));
    }

    let (last, rest) = stmts.split_last().unwrap();

    // Process leading statements as let-binding steps.
    for stmt in rest {
        process_chain_step(stmt, chain, outer_bindings, ctx)?;
    }

    // Process the final statement as a chain terminator.
    process_chain_terminator(last, chain, outer_bindings, ctx)
}

/// Process a non-terminal statement in a generator chain as a let-binding.
fn process_chain_step(
    stmt: &pyast::Stmt,
    chain: &mut Vec<GeneratorSpec>,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<(), LoweringError> {
    match &stmt.node {
        pyast::StmtKind::Assign { targets, value, .. } => {
            if targets.len() != 1 {
                return Err(LoweringError::Unsupported(
                    "Multiple assignment targets not supported".into(),
                ));
            }
            let name = extract_name_target(&targets[0], "assignment")?;
            check_generator_mutation(&name, chain, outer_bindings)?;
            let val = lower_expr(value, ctx)?;
            push_generator_let(chain, name, val, None);
            Ok(())
        }
        pyast::StmtKind::AnnAssign {
            target,
            annotation,
            value: Some(value),
            ..
        } => {
            let name = extract_name_target(target, "annotated assignment")?;
            check_generator_mutation(&name, chain, outer_bindings)?;
            let ann = lower_type_annotation(annotation)?;
            let val = lower_expr(value, ctx)?;
            push_generator_let(chain, name, val, Some(ann));
            Ok(())
        }
        pyast::StmtKind::AnnAssign { value: None, .. } => Err(LoweringError::Unsupported(
            "Annotated assignment without a value is not supported".into(),
        )),
        pyast::StmtKind::AugAssign { target, op, value } => {
            if *op == pyast::Operator::LShift {
                todo!();
            }
            let name = extract_name_target(target, "augmented assignment")?;
            // x op= e desugars to x = x op e. The RHS reads the OLD value
            // of x, so x must already be in scope. If it's not in the
            // current frame's introduced set, it's either from an outer
            // scope (= mutation) or undefined.
            let current = &chain.last().expect("chain non-empty").introduced;
            if !current.contains(&name) {
                return Err(LoweringError::Unsupported(format!(
                    "Augmented assignment to `{name}` in generator: `{name}` is \
                     not bound in this for-body. If it's from an outer scope, \
                     this is mutation; if fresh, use `{name} = expr` instead.",
                )));
            }
            let val = lower_binop(target, op, value, ctx)?;
            push_generator_let(chain, name, val, None);
            Ok(())
        }
        // Allow plain expressions as statements, since they may have side effects.
        pyast::StmtKind::Expr { .. } => {
            todo!();
        }
        pyast::StmtKind::FunctionDef {
            name,
            args,
            body: fn_body,
            decorator_list,
            ..
        } => {
            if !decorator_list.is_empty() {
                return Err(LoweringError::Unsupported(
                    "Function decorators are not supported".into(),
                ));
            }
            check_generator_mutation(name, chain, outer_bindings)?;
            let func_expr = lower_function_body(args, fn_body, ctx)?;
            push_generator_let(chain, name.clone(), func_expr, None);
            Ok(())
        }
        _ => Err(LoweringError::Unsupported(
            "Only assignments and function definitions are supported as \
             non-terminal statements in generator for-bodies"
                .into(),
        )),
    }
}

/// Process the terminal statement in a generator chain (yield, nested for,
/// or if-guard continuing the chain).
fn process_chain_terminator<'ast>(
    stmt: &'ast pyast::Stmt,
    chain: &mut Vec<GeneratorSpec>,
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<&'ast pyast::Expr, LoweringError> {
    match &stmt.node {
        pyast::StmtKind::Expr { value } => match &value.node {
            pyast::ExprKind::Yield {
                value: Some(yield_val),
            } => Ok(yield_val.as_ref()),
            pyast::ExprKind::Yield { value: None } => Err(LoweringError::Unsupported(
                "yield without a value is not supported in generators".into(),
            )),
            pyast::ExprKind::BinOp { op, .. } if *op == pyast::Operator::LShift => Ok(value),
            _ => Err(LoweringError::Unsupported(
                "Generator for-body must end in a yield expression, \
                 nested for, or if-guard"
                    .into(),
            )),
        },
        pyast::StmtKind::If { test, body, orelse } => {
            if !orelse.is_empty() {
                return Err(LoweringError::Unsupported(
                    "if/else inside generator for-loop is not supported; \
                     use a list comprehension with an if-filter instead"
                        .into(),
                ));
            }
            let cond = lower_expr(test, ctx)?;
            let desc = format!("{test}");
            chain
                .last_mut()
                .expect("chain non-empty")
                .steps
                .push(BodyStep::Guard { cond, desc });
            collect_chain(body, chain, outer_bindings, ctx)
        }
        pyast::StmtKind::For {
            target,
            iter,
            body,
            orelse,
            ..
        } => {
            if !orelse.is_empty() {
                return Err(LoweringError::Unsupported(
                    "for/else is not supported inside generator functions".into(),
                ));
            }
            let iter_var = extract_name_target(target, "for-loop target")?;
            let source = lower_expr(iter, ctx)?;
            let mut introduced = HashSet::new();
            introduced.insert(iter_var.clone());
            chain.push(GeneratorSpec {
                iter_var,
                source,
                steps: vec![],
                introduced,
            });
            collect_chain(body, chain, outer_bindings, ctx)
        }
        _ => Err(LoweringError::Unsupported(
            "Generator for-body must end in a yield expression, \
             nested for, or if-guard"
                .into(),
        )),
    }
}

/// Check whether assigning `name` inside the current generator chain
/// constitutes mutation (rejectable) or a let-binding (allowed).
///
/// A name is allowed if it's in the current frame's `introduced` set
/// (shadowing) or if it's fresh (not in any frame or outer bindings).
/// Anything else is mutation.
fn check_generator_mutation(
    name: &str,
    chain: &[GeneratorSpec],
    outer_bindings: &HashSet<String>,
) -> Result<(), LoweringError> {
    let current_idx = chain.len() - 1;
    // Shadowing within current frame is always fine.
    if chain[current_idx].introduced.contains(name) {
        return Ok(());
    }
    // Name in an outer for-frame → mutation across iterations.
    for outer_frame in &chain[..current_idx] {
        if outer_frame.introduced.contains(name) {
            return Err(LoweringError::Unsupported(format!(
                "Assignment to `{name}` inside a nested for-body is mutation: \
                 `{name}` was introduced by an enclosing for-loop",
            )));
        }
    }
    // Name in function scope → mutation of function arg or pre-loop let.
    if outer_bindings.contains(name) {
        return Err(LoweringError::Unsupported(format!(
            "Assignment to `{name}` is mutation: `{name}` is bound outside \
             the generator's for-loop (function argument or pre-loop binding)",
        )));
    }
    // Fresh name — will be added to introduced by push_generator_let.
    Ok(())
}

/// Push a let-binding step onto the innermost generator in the chain and
/// record the name as introduced in the current frame.
#[allow(clippy::ptr_arg)] // Vec is needed: callers also push/last_mut.
fn push_generator_let(
    chain: &mut Vec<GeneratorSpec>,
    name: String,
    value: Expr,
    annotation: Option<Type>,
) {
    let frame = chain.last_mut().expect("chain non-empty");
    frame.introduced.insert(name.clone());
    frame.steps.push(BodyStep::Let(LetStep {
        name,
        value,
        annotation,
    }));
}

// ---------------------------------------------------------------------------
// Generator lowering — for-stmt entry point and chain → CCL conversion
// ---------------------------------------------------------------------------

/// Lower a `for` statement that terminates a statement block as a generator
/// pattern: a chain of nested `for` / `if` / `yield` / `let` lowered to
/// the Lambda/Apply encoding used for list comprehensions.
///
/// `outer_bindings` carries names in scope above this for (function args +
/// preceding lets). The mutation check uses this to reject assignments to
/// names from enclosing scopes.
fn lower_generator_for(
    target: &pyast::Located<pyast::ExprKind>,
    iter: &pyast::Located<pyast::ExprKind>,
    body: &[pyast::Stmt],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let iter_var = extract_name_target(target, "for-loop target")?;
    let source = lower_expr(iter, ctx)?;
    let mut introduced = HashSet::new();
    introduced.insert(iter_var.clone());

    let mut chain = vec![GeneratorSpec {
        iter_var,
        source,
        steps: vec![],
        introduced,
    }];
    let yield_expr_ast = collect_chain(body, &mut chain, outer_bindings, ctx)?;
    let yield_expr = lower_expr(yield_expr_ast, ctx)?;

    lower_generator_chain(chain, yield_expr)
}

/// Convert a fully-populated generator chain into a CCL expression.
///
/// Produces the same Lambda/Apply tiling encoding as [`lower_list_comp`]
/// but with `Expr::Let` nodes interleaved for per-generator let-bindings,
/// and a combined refinement closure when any guards are present.
fn lower_generator_chain(
    chain: Vec<GeneratorSpec>,
    yield_expr: Expr,
) -> Result<Expr, LoweringError> {
    let outer_var = "__iter_record";
    let single_gen = chain.len() == 1;

    let make_idx_arg = |var: &str, i: usize| -> Expr {
        let vref = Expr::var(var.to_string());
        if single_gen {
            vref
        } else {
            Expr::apply(vref, Expr::proj_index(i))
        }
    };

    let any_guards = chain
        .iter()
        .any(|g| g.steps.iter().any(|s| matches!(s, BodyStep::Guard { .. })));

    // ---- Build the body expression (innermost-first) ----
    let mut body_expr = yield_expr.clone();
    for (i, generator) in chain.iter().enumerate().rev() {
        // Wrap body in this generator's lets (reverse source order so
        // outermost let wraps everything inside).
        for step in generator.steps.iter().rev() {
            if let BodyStep::Let(ls) = step {
                body_expr = match &ls.annotation {
                    Some(ann) => Expr::let_bind_annotated(
                        ls.name.clone(),
                        ls.value.clone(),
                        body_expr,
                        ann.clone(),
                    ),
                    None => Expr::let_bind(ls.name.clone(), ls.value.clone(), body_expr),
                };
            }
        }
        body_expr = Expr::apply(
            Expr::apply(make_idx_arg(outer_var, i), generator.source.clone()),
            Expr::lambda(&generator.iter_var, Type::Hole, body_expr),
        );
    }

    if !any_guards {
        return Ok(Expr::lambda(outer_var, Type::Hole, body_expr));
    }

    // ---- Build the refinement closure ----
    // Same structure as the body, but the innermost expression is the
    // AND-conjunction of all guards (instead of the yield expression).
    let restr_outer_var = "__iter_record_restr";

    let mut all_guards: Vec<Expr> = Vec::new();
    let mut guard_descs: Vec<String> = Vec::new();
    for generator in &chain {
        for step in &generator.steps {
            if let BodyStep::Guard { cond, desc } = step {
                all_guards.push(cond.clone());
                guard_descs.push(desc.clone());
            }
        }
    }
    let pred_inner = all_guards
        .into_iter()
        .reduce(|acc, g| Expr::binop(acc, BinOpKind::BoolLogic(LogicKind::And), g))
        .expect("any_guards is true");
    let pred_desc = guard_descs.join(" and ");

    let mut pred_expr = pred_inner;
    for (i, generator) in chain.iter().enumerate().rev() {
        for step in generator.steps.iter().rev() {
            if let BodyStep::Let(ls) = step {
                pred_expr = match &ls.annotation {
                    Some(ann) => Expr::let_bind_annotated(
                        ls.name.clone(),
                        ls.value.clone(),
                        pred_expr,
                        ann.clone(),
                    ),
                    None => Expr::let_bind(ls.name.clone(), ls.value.clone(), pred_expr),
                };
            }
        }
        let restr_idx = {
            let vref = Expr::var(restr_outer_var.to_string());
            if single_gen {
                vref
            } else {
                Expr::apply(vref, Expr::proj_index(i))
            }
        };
        pred_expr = Expr::apply(
            Expr::apply(restr_idx, generator.source.clone()),
            Expr::lambda(&generator.iter_var, Type::Hole, pred_expr),
        );
    }

    Ok(Expr::lambda_with_refinement(
        outer_var,
        Type::Hole,
        body_expr,
        Expr::lambda(restr_outer_var, Type::Hole, pred_expr),
        &pred_desc,
    ))
}

/// Lower a Python function definition body to a CCL expression.
///
/// Delegates entirely to [`lower_stmts_inner`] with the function's
/// parameter names as `outer_bindings`. If the function body's final
/// statement is a `for`-loop with a yield chain, it is lowered as a
/// generator; otherwise it's a regular function body.
fn lower_function_body(
    args: &pyast::Arguments,
    body: &[pyast::Stmt],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    validate_function_args(args)?;
    let outer_bindings: HashSet<String> = args.args.iter().map(|a| a.node.arg.clone()).collect();
    // http_serve is not permitted inside function bodies.
    let body_expr = lower_stmts_inner(body, &outer_bindings, ctx, false)?;
    Ok(uncurry_params(args, body_expr, ctx))
}

/// Lower a Python list comprehension to the CCL Lambda/Apply encoding.
///
/// Handles three cases based on the number of generators and predicates:
///
/// **Single generator, no predicate** — identity encoding:
/// ```text
/// λ __iter_record → __iter_record ▷ lower(source) ▷ (λ var → lower(body))
/// ```
///
/// **Multiple generators / non-equality predicates** — loop-join encoding.
/// The outer lambda carries a [`RefinementKind::Predicate`] with the combined
/// guard expression; the runtime filters via a correlation vector:
/// ```text
/// λ __iter_record : {T | Refined(pred)} →
///   __iter_record[0] ▷ lower(source0) ▷ (λ var0 →
///     __iter_record[1] ▷ lower(source1) ▷ (λ var1 → lower(body)))
/// ```
///
/// **Two generators, single equality predicate** — hash-join encoding.
/// Detected by [`try_extract_ccl_equality_join`] on the lowered predicate.
/// The outer lambda carries a [`RefinementKind::HashJoin`]; `compile_ccl`
/// translates it to an O(N+M) hash-join-based restriction:
/// ```text
/// λ __iter_record : {T | Refined(build_var == probe_var)} →
///   __iter_record[0] ▷ lower(source0) ▷ (λ var0 →
///     __iter_record[1] ▷ lower(source1) ▷ (λ var1 → lower(body)))
/// ```
///
/// All lambdas are produced with `param.ty = Type::Hole`; [`crate::ccl::infer`]
/// converts the placeholder to a registered inference variable and fills in the
/// type annotations before compilation.
///
/// TODO this currently has an assumption that all generator variables have distinct names.
/// This might be a reasonable assumption that we should enforce, or we should fix scoping to
/// handle that case.
fn lower_list_comp(
    elt: &pyast::Located<pyast::ExprKind>,
    generators: &[pyast::Comprehension],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // ---- Phase 1: Lower each generator's source and register its loop variable ----
    // We keep the source operators and index extents for later use when building the
    // Apply/Lambda chains.  Each loop variable is pushed onto the lowering scope so
    // that body and predicate expressions can reference it.
    let mut gen_sources: Vec<Expr> = Vec::new();
    let mut gen_iter_vars: Vec<String> = Vec::new();

    for generator in generators.iter() {
        if generator.is_async > 0 {
            return Err(LoweringError::Unsupported(
                "Async comprehensions are not supported".into(),
            ));
        }
        let source = lower_expr(&generator.iter, ctx)?;
        let var_name = match &generator.target.node {
            pyast::ExprKind::Name { id, .. } => id,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Only simple variable targets are supported in comprehensions, got {:?}",
                    generator.target.node
                )));
            }
        };
        let iter_var = var_name;
        gen_iter_vars.push(iter_var.to_string());
        gen_sources.push(source);
    }

    // ---- Phase 2: Lower body and all predicates to CCL -------------------------
    let body = lower_expr(elt, ctx)?;

    // Lower every `if` guard from each generator to CCL.  We hold on to the
    // original pyast nodes only to build human-readable description strings;
    // all detection logic operates on the lowered CCL expressions.
    let pyast_preds: Vec<&pyast::Expr> = generators
        .iter()
        .flat_map(|g| g.ifs.iter().map(|e| e as &pyast::Expr))
        .collect();
    let lowered_preds: Vec<Expr> = pyast_preds
        .iter()
        .map(|e| lower_expr(e, ctx))
        .collect::<Result<_, _>>()?;

    // Combine all `if` guards into a single loop-join predicate (used when hash
    // join is not applicable — non-equality, 3+ generators, or multiple predicates).
    // Description strings are built from the original pyast Display output.
    let mut pred_op: Option<Expr> = None;
    let mut pred_desc = String::new();
    for (pyast_pred, lowered) in pyast_preds.iter().zip(lowered_preds) {
        pred_op = Some(match pred_op {
            Some(lhs) => {
                pred_desc.push_str(&format!(" and {pyast_pred}"));
                Expr::binop(lhs, BinOpKind::BoolLogic(LogicKind::And), lowered)
            }
            None => {
                pred_desc = format!("{pyast_pred}");
                lowered
            }
        });
    }

    // Sources for the loop-join restriction lambda are cloned from the
    // already-lowered gen_sources (Phase 5 drains it, so clone here).
    let mut pred_sources: Vec<Expr> = if pred_op.is_some() {
        gen_sources.clone()
    } else {
        Vec::new()
    };

    // ---- Phase 4: Build the outer iteration variable ------------------------------
    // Single generator: iterate directly over that source's index extent.
    // Multiple generators: pack all index extents into a Record so the body can
    // address each one via RecordField and the runtime produces the cartesian
    // product.
    // With a predicate: wrap in Restricted so the runtime filters via a correlation
    // vector computed from the predicate (see Phase 6).
    let single_gen = generators.len() == 1;
    let outer_var = "__iter_record";

    // Helper: build the index argument for generator `i`.
    // Single-gen: a bare VarRef to the outer variable.
    // Multi-gen: a RecordField projection of the i-th field from the outer record.
    let make_idx_arg = |var: &str, i: usize| -> Expr {
        let vref = Expr::var(var.to_string());
        if single_gen {
            vref
        } else {
            Expr::apply(vref, Expr::proj_index(i))
        }
    };

    // ---- Phase 5: Build the body as a nested Apply/Lambda chain ------------------
    // Working innermost-first (reverse order) we wrap the accumulated expression:
    //   body = Apply(Lambda(iter_var_i, body), Apply(source_i, idx_arg_i))
    let mut body_expr: Expr = body;
    for (i, (iter_var, source)) in gen_iter_vars
        .iter()
        .zip(gen_sources.drain(..))
        .enumerate()
        .rev()
    {
        body_expr = Expr::apply(
            Expr::apply(make_idx_arg(outer_var, i), source),
            Expr::lambda(iter_var, Type::Hole, body_expr),
        );
    }

    // ---- Phase 6: Attach restriction ----------
    if let Some(pred_op) = pred_op {
        // Non-equality or multi-predicate: loop-join restriction lambda.
        // Uses an independent "__iter_record_restr" variable so it does not
        // recursively depend on a correlation vector.
        let restr_outer_var = "__iter_record_restr";
        let mut pred_expr: Expr = pred_op;
        for (i, (iter_var, pred_source)) in gen_iter_vars
            .iter()
            .zip(pred_sources.drain(..))
            .enumerate()
            .rev()
        {
            pred_expr = Expr::apply(
                Expr::apply(make_idx_arg(restr_outer_var, i), pred_source),
                Expr::lambda(iter_var, Type::Hole, pred_expr),
            );
        }
        Ok(Expr::lambda_with_refinement(
            outer_var,
            Type::Hole,
            body_expr,
            Expr::lambda(restr_outer_var, Type::Hole, pred_expr),
            &pred_desc,
        ))
    } else {
        Ok(Expr::lambda(outer_var, Type::Hole, body_expr))
    }
}

// ---------------------------------------------------------------------------
// http_serve helpers
// ---------------------------------------------------------------------------

/// Returns `true` when `target` is a 2-element name tuple and `value` is a
/// call to `http_serve` with exactly 3 string-literal arguments.
fn is_http_serve_tuple_assign(target: &pyast::Expr, value: &pyast::Expr) -> bool {
    let pyast::ExprKind::Tuple { elts, .. } = &target.node else {
        return false;
    };
    if elts.len() != 2 {
        return false;
    }
    let all_names = elts
        .iter()
        .all(|e| matches!(e.node, pyast::ExprKind::Name { .. }));
    if !all_names {
        return false;
    }
    let pyast::ExprKind::Call {
        func,
        args,
        keywords,
    } = &value.node
    else {
        return false;
    };
    if !keywords.is_empty() || args.len() != 3 {
        return false;
    }
    matches!(&func.node, pyast::ExprKind::Name { id, .. } if id == "http_serve")
        && args.iter().all(|a| {
            matches!(
                &a.node,
                pyast::ExprKind::Constant {
                    value: pyast::Constant::Str(_),
                    ..
                }
            )
        })
}

/// Extract `(requests_var, responses_var)` from a 2-element name tuple target.
fn extract_http_serve_names(target: &pyast::Expr) -> Result<(String, String), LoweringError> {
    let pyast::ExprKind::Tuple { elts, .. } = &target.node else {
        return Err(LoweringError::Unsupported(
            "http_serve target must be a 2-tuple".into(),
        ));
    };
    let name0 = match &elts[0].node {
        pyast::ExprKind::Name { id, .. } => id.clone(),
        _ => {
            return Err(LoweringError::Unsupported(
                "http_serve tuple elements must be simple names".into(),
            ));
        }
    };
    let name1 = match &elts[1].node {
        pyast::ExprKind::Name { id, .. } => id.clone(),
        _ => {
            return Err(LoweringError::Unsupported(
                "http_serve tuple elements must be simple names".into(),
            ));
        }
    };
    Ok((name0, name1))
}

/// Extract `(port, method, path)` string literals from the `http_serve(...)` call.
fn extract_http_serve_args(value: &pyast::Expr) -> Result<(String, String, String), LoweringError> {
    let pyast::ExprKind::Call { args, .. } = &value.node else {
        return Err(LoweringError::Unsupported(
            "Expected http_serve call".into(),
        ));
    };
    let extract = |expr: &pyast::Expr| match &expr.node {
        pyast::ExprKind::Constant {
            value: pyast::Constant::Str(s),
            ..
        } => Ok(s.clone()),
        _ => Err(LoweringError::Unsupported(
            "http_serve arguments must be string literals".into(),
        )),
    };
    Ok((extract(&args[0])?, extract(&args[1])?, extract(&args[2])?))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;
    use rustpython_parser::parser;

    /// Parse a Python expression and return the AST node.
    fn parse_expr(code: &str) -> pyast::Expr {
        let result = parser::parse(code, parser::Mode::Expression, "<test>")
            .expect("Failed to parse expression");
        match result {
            pyast::Mod::Expression { body } => *body,
            other => panic!("expected Expression, got {other:?}"),
        }
    }

    /// Create a minimal registered source for tests that only care about name recognition.
    fn stub_source(name: &str) -> Rc<RefCell<dyn DataSourceDomainExtentImpl>> {
        use crate::interpreter::{BaseType, Extent, TestDataSource};
        Rc::new(RefCell::new(TestDataSource::new(
            name,
            Type::Base(BaseType::String),
            Extent::Base(BaseType::String),
        )))
    }

    /// Parse a Python module and return the statement list.
    fn parse_module(code: &str) -> Vec<pyast::Stmt> {
        let result =
            parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse module");
        match result {
            pyast::Mod::Module { body, .. } => body,
            other => panic!("expected Module, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Single-expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Literals
    #[case("2", "2")]
    #[case(r#""hi""#, r#""hi""#)]
    #[case("True", "true")]
    #[case("None", "unit")]
    // Variable
    #[case("x", "x")]
    // Arithmetic
    #[case("2 + 3", "2 + 3")]
    #[case("4 * 5", "4 * 5")]
    #[case("4 - 5", "4 - 5")]
    #[case("7 // 2", "7 // 2")]
    // Nested binop: `1 + 2 * 3` parses as `1 + (2 * 3)` — * tighter, no parens needed
    #[case("1 + 2 * 3", "1 + 2 * 3")]
    // List literals
    #[case("[]", "[]")]
    #[case("[1, 2]", "[1, 2]")]
    // Comparisons
    #[case("x == 1", "x == 1")]
    #[case("x != 1", "x != 1")]
    #[case("x < 1", "x < 1")]
    #[case("x <= 1", "x <= 1")]
    #[case("x > 1", "x > 1")]
    #[case("x >= 1", "x >= 1")]
    // Chained comparison: `1 < x < 10` → `(1 < x) and (x < 10)`
    #[case("1 < x < 10", "1 < x and x < 10")]
    // Boolean operators
    #[case("x and y", "x and y")]
    #[case("x or y", "x or y")]
    // Three operands fold left: `a and b and c` → `(a and b) and c`
    #[case("a and b and c", "a and b and c")]
    #[case("a or b or c", "a or b or c")]
    // Mixed: `x == 1 and y == 2`
    #[case("x == 1 and y == 2", "x == 1 and y == 2")]
    // Lambdas — single-arg emits `λ x → body` directly; multi-arg uncurries
    // to a tupled-parameter lambda whose body binds each name to a
    // projection, keeping the tree free of nested `Lambda` chains.
    #[case("lambda x: x + 1", "λ x → x + 1")]
    #[case(
        "lambda x, y: x + y",
        "λ __arg_tuple_0 → __arg_tuple_0.0 + __arg_tuple_0.1"
    )]
    // Nested multi-arg lambdas: the outer lambda's substitution inserts a
    // reference to its tuple parameter into the inner lambda's body.  Each
    // multi-arg lambda mints a fresh `__arg_tuple_<N>` via `fresh_tuple_arg`,
    // so the inserted reference does not collide with the inner binder.  The
    // outer takes id 1 because the inner is lowered first and consumes id 0.
    #[case(
        "lambda x, y: lambda a, b: x + a",
        "λ __arg_tuple_1 → λ __arg_tuple_0 → __arg_tuple_1.0 + __arg_tuple_0.0"
    )]
    fn test_lower_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

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
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // List comprehension tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Identity: element passes through unchanged; lambdas are unannotated (infer fills them in).
    #[case(
        "[x for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)"
    )]
    // Constant body: loop variable unused in body.
    #[case(
        "[42 for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → 42)"
    )]
    // BinOp body: loop variable used in arithmetic.
    #[case(
        "[x + 2 for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 2)"
    )]
    // Outer capture: y is captured from an enclosing let binding.
    #[case(
        "\
y = 5
[x + y for x in [10, 20]]",
        "\
let y = 5
in λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + y)"
    )]
    // Nested comprehension: all lambdas unannotated; infer annotates them in a
    // subsequent pass.
    #[case(
        "[y for y in [x for x in [10, 20]]]",
        "λ __iter_record → __iter_record ▷ (λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)) ▷ (λ y → y)"
    )]
    fn test_lower_list_comp(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Generator expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Generator expression: identical output to equivalent list comp.
    #[case(
        "(x for x in [10, 20])",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)"
    )]
    #[case(
        "(x + 2 for x in [10, 20])",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 2)"
    )]
    fn test_lower_generator_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

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
let doubles : (_ ⇒ (_ ⇒ _)) = λ xs → λ __iter_record → __iter_record ▷ xs ▷ (λ x → x * 2)
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
let add_to : (_ ⇒ (_ ⇒ _)) = λ __arg_tuple_0 → λ __iter_record → __iter_record ▷ (__arg_tuple_0.0) ▷ (λ x → x + __arg_tuple_0.1)
in add_to"
    )]
    // Generator with if-guard: filter pattern.
    #[case(
        "\
def positives(xs):
    for x in xs:
        if x > 0:
            yield x
positives",
        "\
let positives : (_ ⇒ _) = λ xs → λ __iter_record : {??? | Refined((λ __iter_record_restr → __iter_record_restr ▷ xs ▷ (λ x → x > 0)))} → __iter_record ▷ xs ▷ (λ x → x)
in positives"
    )]
    // Nested for-loops: inner iter independent of outer loop variable.
    // Equivalent to `[x + y for x in xs for y in ys]`.
    #[case(
        "\
def cross(xs, ys):
    for x in xs:
        for y in ys:
            yield x + y
cross",
        "\
let cross : (_ ⇒ (_ ⇒ _)) = λ __arg_tuple_0 → λ __iter_record → __iter_record.0 ▷ (__arg_tuple_0.0) ▷ (λ x → __iter_record.1 ▷ (__arg_tuple_0.1) ▷ (λ y → x + y))
in cross"
    )]
    // Three-level cartesian product.
    // Equivalent to `[x + y + z for x in xs for y in ys for z in zs]`.
    #[case(
        "\
def triple(xs, ys, zs):
    for x in xs:
        for y in ys:
            for z in zs:
                yield x + y + z
triple",
        "\
let triple : (_ ⇒ (_ ⇒ _)) = λ __arg_tuple_0 → λ __iter_record → __iter_record.0 ▷ (__arg_tuple_0.0) ▷ (λ x → __iter_record.1 ▷ (__arg_tuple_0.1) ▷ (λ y → __iter_record.2 ▷ (__arg_tuple_0.2) ▷ (λ z → x + y + z)))
in triple"
    )]
    // Guard sits between the outer and inner `for`: filters `x` before
    // entering the inner loop. Equivalent to `[y for x in xs if x > 0 for y in ys]`.
    #[case(
        "\
def cross_filtered(xs, ys):
    for x in xs:
        if x > 0:
            for y in ys:
                yield y
cross_filtered",
        "\
let cross_filtered : (_ ⇒ _) = λ __arg_tuple_0 → λ __iter_record : {??? | Refined((λ __iter_record_restr → __iter_record_restr.0 ▷ (__arg_tuple_0.0) ▷ (λ x → __iter_record_restr.1 ▷ (__arg_tuple_0.1) ▷ (λ y → x > 0))))} → __iter_record.0 ▷ (__arg_tuple_0.0) ▷ (λ x → __iter_record.1 ▷ (__arg_tuple_0.1) ▷ (λ y → y))
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
let with_let : (_ ⇒ (_ ⇒ _)) = λ xs → λ __iter_record → __iter_record ▷ xs ▷ (λ x → let y = x + 1
in y * 2)
in with_let"
    )]
    // Iter-var shadowing: x = x + 1 shadows the iter var.
    #[case(
        "\
def shadow(xs):
    for x in xs:
        x = x + 1
        yield x
shadow",
        "\
let shadow : (_ ⇒ (_ ⇒ _)) = λ xs → λ __iter_record → __iter_record ▷ xs ▷ (λ x → let x = x + 1
in x)
in shadow"
    )]
    // Dependent inner iter: inner iter references outer iter var. Now
    // supported (the inner source is in scope of the outer lambda).
    #[case(
        "\
def dep(xss):
    for xs in xss:
        for x in xs:
            yield x
dep",
        "\
let dep : (_ ⇒ (_ ⇒ _)) = λ xss → λ __iter_record → __iter_record.0 ▷ xss ▷ (λ xs → __iter_record.1 ▷ xs ▷ (λ x → x))
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
let guarded_let : (_ ⇒ _) = λ xs → λ __iter_record : {??? | Refined((λ __iter_record_restr → __iter_record_restr ▷ xs ▷ (λ x → let y = x * 2
in x > 0)))} → __iter_record ▷ xs ▷ (λ x → let y = x * 2
in y)
in guarded_let"
    )]
    fn test_lower_generator_fn(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Regular function definition tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Simple function: body is a single expression.
    #[case(
        "\
def inc(x):
    x + 1
inc",
        "\
let inc : (_ ⇒ _) = λ x → x + 1
in inc"
    )]
    // Multi-param function: uncurried to a single tupled-parameter lambda.
    #[case(
        "\
def add(x, y):
    x + y
add",
        "\
let add : (_ ⇒ _) = λ __arg_tuple_0 → __arg_tuple_0.0 + __arg_tuple_0.1
in add"
    )]
    fn test_lower_function_def(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Generator function negative tests
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
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(matches!(err, LoweringError::Unsupported(_)));
    }

    /// Mutation of a function argument inside a generator is rejected.
    #[test]
    fn test_generator_mutation_of_arg_rejected() {
        let code = "\
def bad(xs, n):
    for x in xs:
        n = n + 1
        yield n
bad";
        let stmts = parse_module(code);
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        match &err {
            LoweringError::Unsupported(msg) => {
                assert!(
                    msg.contains("mutation") && msg.contains("`n`"),
                    "error should mention mutation of `n`: {msg}"
                );
            }
        }
    }

    /// Mutation of a pre-loop let inside a generator is rejected.
    #[test]
    fn test_generator_mutation_of_preloop_let_rejected() {
        let code = "\
def bad(xs):
    total = 0
    for x in xs:
        total = total + x
        yield total
bad";
        let stmts = parse_module(code);
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        match &err {
            LoweringError::Unsupported(msg) => {
                assert!(
                    msg.contains("mutation") && msg.contains("`total`"),
                    "error should mention mutation of `total`: {msg}"
                );
            }
        }
    }

    /// Mutation across nested for boundaries is rejected.
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
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        match &err {
            LoweringError::Unsupported(msg) => {
                assert!(
                    msg.contains("mutation") || msg.contains("enclosing for-loop"),
                    "error should mention mutation across for boundary: {msg}"
                );
            }
        }
    }

    /// `yield` without a value is rejected.
    #[test]
    fn test_generator_yield_without_value_rejected() {
        let code = "\
def bad(xs):
    for x in xs:
        yield
bad";
        let stmts = parse_module(code);
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(matches!(err, LoweringError::Unsupported(_)));
    }

    /// Function decorators are rejected.
    #[test]
    fn test_function_decorators_rejected() {
        let code = "\
@some_decorator
def f(x):
    x + 1
f";
        let stmts = parse_module(code);
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        match &err {
            LoweringError::Unsupported(msg) => {
                assert!(
                    msg.contains("decorator"),
                    "error should mention decorators: {msg}"
                );
            }
        }
    }

    /// `for/else` in a generator function is rejected.
    #[test]
    fn test_generator_for_else_rejected() {
        let code = "\
def bad(xs):
    for x in xs:
        yield x
    else:
        pass
bad";
        let stmts = parse_module(code);
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        match &err {
            LoweringError::Unsupported(msg) => {
                assert!(
                    msg.contains("for/else"),
                    "error should mention for/else: {msg}"
                );
            }
        }
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
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        match &err {
            LoweringError::Unsupported(msg) => {
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
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        let s = symbolic(&ccl);
        assert!(
            s.contains("let a = 5") && s.contains("x + a"),
            "should have pre-loop let and body referencing it: {s}"
        );
    }

    // -----------------------------------------------------------------------
    // Aggregate expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // sum over a list literal
    #[case("sum([1, 2, 3])", "Sum([1, 2, 3])")]
    // max over a list literal
    #[case("max([1, 2])", "Max([1, 2])")]
    // sum over a variable (the input expression is itself a CCL expression)
    #[case("sum(xs)", "Sum(xs)")]
    // max over a variable
    #[case("max(xs)", "Max(xs)")]
    // sum over a list comprehension — input becomes a lambda
    #[case(
        "sum([x for x in [10, 20]])",
        "Sum(λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x))"
    )]
    // max over a list comprehension with a body expression
    #[case(
        "max([x + 1 for x in [10, 20]])",
        "Max(λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 1))"
    )]
    fn test_lower_aggregate(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // GroupBy tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Variable collection and inline key lambda
    #[case(
        "groupby(xs, lambda x: x)",
        "λ __gb_k → λ __gb_i : {??? | Refined((λ __gb_r → __gb_r ▷ xs ▷ (λ x → x) == __gb_k))} → __gb_i ▷ xs"
    )]
    // List literal collection with a more complex key
    #[case(
        "groupby([1, 2, 3], lambda x: x // 2)",
        "λ __gb_k → λ __gb_i : {??? | Refined((λ __gb_r → __gb_r ▷ [1, 2, 3] ▷ (λ x → x // 2) == __gb_k))} → __gb_i ▷ [1, 2, 3]"
    )]
    // Key is a variable reference (pre-defined function)
    #[case(
        "groupby(xs, key_fn)",
        "λ __gb_k → λ __gb_i : {??? | Refined((λ __gb_r → __gb_r ▷ xs ▷ key_fn == __gb_k))} → __gb_i ▷ xs"
    )]
    // Keyed aggregation
    #[case(
        "[sum(x) for x in groupby(xs, key_fn)]",
        "λ __iter_record → __iter_record ▷ (λ __gb_k → λ __gb_i : {??? | Refined((λ __gb_r → __gb_r ▷ xs ▷ key_fn == __gb_k))} → __gb_i ▷ xs) ▷ (λ x → Sum(x))"
    )]
    fn test_lower_groupby(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let mut ctx = LoweringContext::default();
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    /// `groupby` with the wrong number of arguments returns `LoweringError::Unsupported`.
    #[test]
    fn test_lower_groupby_wrong_arity() {
        let one_arg = parse_expr("groupby(xs)");
        assert!(matches!(
            lower_expr(&one_arg, &mut LoweringContext::default()),
            Err(LoweringError::Unsupported(_))
        ));
        let three_args = parse_expr("groupby(xs, f, extra)");
        assert!(matches!(
            lower_expr(&three_args, &mut LoweringContext::default()),
            Err(LoweringError::Unsupported(_))
        ));
    }

    /// A single-argument call to an unknown (non-builtin, non-source) name lowers
    /// to an `Apply` node — general function application.
    #[test]
    fn test_lower_unknown_function_single_arg() {
        let expr = parse_expr("foo(x)");
        let ccl = lower_expr(&expr, &mut LoweringContext::default())
            .expect("expected lowering to succeed");
        // foo(x) == x ▷ foo in pipeline notation
        assert_eq!(symbolic(&ccl), "x ▷ foo");
    }

    /// A zero-argument call to an unknown (non-source) name still fails.
    #[test]
    fn test_lower_unknown_zero_arg_fails() {
        let expr = parse_expr("foo()");
        let err = lower_expr(&expr, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(
            matches!(err, LoweringError::Unsupported(_)),
            "expected Unsupported, got {err:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Source lowering tests
    // -----------------------------------------------------------------------

    /// A zero-argument call whose name is registered lowers to `Expr::Source`.
    #[test]
    fn test_lower_registered_source_becomes_source_node() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("mystream", stub_source("mystream"));
        let expr = parse_expr("mystream()");
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), "source(mystream)");
    }

    /// A zero-argument call whose name is NOT registered still fails.
    #[test]
    fn test_lower_unregistered_zero_arg_call_fails() {
        let expr = parse_expr("unknown_source()");
        let err = lower_expr(&expr, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(matches!(err, LoweringError::Unsupported(_)));
    }

    /// A registered source name used as a non-call expression (plain variable)
    /// lowers to `Expr::Var`, not `Expr::Source` — the call syntax is required.
    #[test]
    fn test_lower_source_name_without_call_is_var() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("mystream", stub_source("mystream"));
        let expr = parse_expr("mystream");
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), "mystream");
    }

    /// A source call nested inside a larger expression lowers correctly.
    #[test]
    fn test_lower_source_in_list_comp() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("src", stub_source("src"));
        let stmts = parse_module("[x for x in src()]");
        let ccl = lower_stmts(&stmts, &mut ctx).expect("lowering failed");
        // The source node should appear in the symbolic output.
        assert!(
            symbolic(&ccl).contains("source(src)"),
            "expected source(src) in output, got: {}",
            symbolic(&ccl)
        );
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
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
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
    #[ignore = "walrus operator (:=) not yet implemented (ExprKind::NamedExpr unsupported)"]
    fn test_lower_walrus_let_in_value_position() {
        let code = "\
x = (y := 5) + 1
x";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        // Fill in the expected string when ExprKind::NamedExpr lowering is added.
        // Structure: let x = (let y = 5 in y) + 1 in x
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
    // elif chain: orelse is itself a StmtKind::If; branches are flattened into a single Case.
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
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    #[rstest]
    // Ternary: `body if test else orelse` → `{ test → body; true → orelse }`
    #[case("1 if x else 0", "{ x → 1; true → 0 }")]
    #[case("\"yes\" if flag else \"no\"", "{ flag → \"yes\"; true → \"no\" }")]
    fn test_lower_if_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
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
        let _ccl = lower_stmts(&stmts, &mut LoweringContext::default()).expect("lowering failed");
        // Expected once implemented:
        // let x = 1 in let x = { x > 0 → x + 1; true → x } in let result = x in result
    }

    #[test]
    fn test_lower_if_without_else_rejected() {
        let stmts = parse_module("if x:\n    1");
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(matches!(err, LoweringError::Unsupported(_)));
    }

    #[rstest]
    #[case("x = [1]\nx[0] += 1\nx")]
    #[case("x = 0\nx.field += 1\nx")]
    fn test_augassign_non_name_target_rejected(#[case] code: &str) {
        let stmts = parse_module(code);
        let err = lower_stmts(&stmts, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(matches!(err, LoweringError::Unsupported(_)));
    }
}

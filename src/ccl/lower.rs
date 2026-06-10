//! CHL AST → CCL lowering.
//!
//! Translates [`crate::chl_parser::ast`] nodes into [`crate::ccl::Expr`] trees.
//! This is a structural lowering only — no type inference, no operator-graph
//! construction, and no subscription. The resulting CCL tree can be inspected
//! and tested independently before being type-checked and compiled.
//!
//! # Supported constructs
//!
//! | CHL syntax | CCL output |
//! |--------------|-----------|
//! | Integer / string / bool / None literals | [`TypedExprNode::Lit`] |
//! | Variable references | [`TypedExprNode::Var`] |
//! | Binary arithmetic (`+`, `-`, `*`, `//`) | [`TypedExprNode::BinOp`] |
//! | Comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`) | [`TypedExprNode::BinOp`] |
//! | Chained comparisons (`a < b < c`) | nested [`TypedExprNode::BinOp`] with `and` |
//! | Boolean operators (`and`, `or`) | left-folded [`TypedExprNode::BinOp`] chain |
//! | List literals `[e0, e1, ...]` | [`TypedExprNode::List`] |
//! | Single-generator list comprehensions (no `if`) | `Lambda`/`Apply` encoding |
//! | 2-gen equality-join comprehensions (`if x.k == y.k`) | hash-join [`crate::ccl::Refinement`] predicate |
//! | Multi-gen filtered comprehensions (non-equality or 3+ generators) | loop-join [`crate::ccl::Refinement`] predicate |
//! | Assignment + expression blocks | nested [`TypedExprNode::Let`] |
//! | Augmented assignment `x op= e` | desugared to [`TypedExprNode::Let`] via [`TypedExprNode::BinOp`] |
//! | `sum(expr)` / `max(expr)` calls | [`TypedExprNode::Aggregate`] |
//! | Lambda expressions `lambda x: body`, `lambda x, y: body` | single [`TypedExprNode::Lambda`] (tupled param when multi-arg) |
//! | `groupby(collection, key)` calls | `Lambda`/`Apply` encoding with a refinement predicate |
//! | Unary negation (`-x`) | [`TypedExprNode::UnaryOp`] with [`crate::ccl::UnaryOpKind::Neg`] |
//! | Boolean negation (`not x`) | [`TypedExprNode::UnaryOp`] with [`crate::ccl::UnaryOpKind::Not`] |
//! | Unary plus (`+x`) | identity — lowered to `x` directly |
//! | Single-arg call `f(a)` | [`TypedExprNode::Apply`] |
//! | Multi-arg call `f(a, b, ...)` | [`TypedExprNode::Apply`] with a tupled argument |
//! | Annotated assignment `x: T = expr` | [`TypedExprNode::Let`] with [`crate::ccl::TypedBinding::user_annotation`] set |
//! | Generator expressions `(expr for x in xs)` | `Lambda`/`Apply` encoding (same as list comp) |
//! | Generator functions `def f(xs): for x in xs: yield expr` | [`TypedExprNode::Let`] + uncurried [`TypedExprNode::Lambda`] wrapping `Lambda`/`Apply` encoding |
//! | Nested-for generator functions | same encoding as multi-generator list comprehensions |
//! | Let-bindings in generator bodies `y = f(x); yield y` | [`TypedExprNode::Let`] interleaved in the `Lambda`/`Apply` chain |
//! | Pre-loop lets before generator for-loop | [`TypedExprNode::Let`] wrapping the generator expression |
//! | Regular functions `def f(x, y, ...): expr` | [`TypedExprNode::Let`] + single [`TypedExprNode::Lambda`] (tupled param when multi-arg) |
//! | Record literals `{field: expr, ...}` (identifier keys only) | [`TypedExprNode::Record`] |
//! | Field access `r.field` | [`TypedExprNode::Apply`] with [`TypedExprNode::Proj`]`(`[`crate::ccl::ProjKey::Field`]`)` |
//!
//! Everything else returns [`LoweringError::Unsupported`].
//!
//! # Name uniqueness
//!
//! This pass does not guarantee unique binding names. Reassignment of the
//! same variable (`x = 1; x = 2`) produces nested [`TypedExprNode::Let`] nodes that shadow
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

use crate::{
    ccl::{
        AggregateKind, ArithmeticKind, BaseType, BinOpKind, Branch, Builtin, CompareKind, Expr,
        Lit, LogicKind, Type, TypedExprNode, UnaryOpKind,
        ccl_utils::{make_cast, refined_fn_type},
    },
    chl_parser::ast::{
        AssignTarget, AugOp, BinOp as ChlBinOp, BoolOp, CmpOp, CompClause, Comprehension,
        Expr as ChlExpr, IfBranch, Lit as ChlLit, Param, RecordField, Span, Spanned,
        Stmt as ChlStmt, UnaryOp,
    },
    interpreter::{
        DataSink, DataSourceDomainExtentImpl, HttpServerDataSource, http_server::SharedHttpServer,
    },
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during CHL → CCL lowering.
///
/// Carries the source span of the offending construct so the error can be
/// rendered with ariadne via [`LoweringError::to_report`] / the
/// [`crate::ccl::context::CompileError::Lower`] dispatch in
/// [`crate::ccl::context::CompileError::render`].
#[derive(Debug, Clone, PartialEq)]
pub enum LoweringError {
    /// The AST node or construct is not yet supported by this lowering pass.
    Unsupported {
        /// Span of the offending construct (the [`Spanned<ChlExpr>`] /
        /// [`Spanned<ChlStmt>`] / sub-node that triggered the rejection).
        span: Span,
        /// Human-readable description of why the construct is unsupported.
        message: String,
    },
}

impl LoweringError {
    /// Construct an `Unsupported` lowering error at the given span.
    ///
    /// Convenience over the struct-init form so call sites read
    /// `LoweringError::unsupported(span, "...")` rather than the verbose
    /// `LoweringError::Unsupported { span, message: "...".into() }`.
    pub fn unsupported(span: Span, message: impl Into<String>) -> Self {
        LoweringError::Unsupported {
            span,
            message: message.into(),
        }
    }

    /// Primary source span of this error.
    pub fn span(&self) -> Span {
        match self {
            LoweringError::Unsupported { span, .. } => *span,
        }
    }

    /// Build an ariadne [`Report`](ariadne::Report) with default (colour-on)
    /// configuration.
    pub fn to_report<'a>(
        &self,
        src_name: &'a str,
    ) -> ariadne::Report<'a, (&'a str, std::ops::Range<usize>)> {
        self.to_report_with_config(src_name, ariadne::Config::default())
    }

    /// Build an ariadne [`Report`](ariadne::Report) using the supplied
    /// [`Config`](ariadne::Config). Use this to disable colour for snapshot
    /// or log output; interactive callers should use [`Self::to_report`].
    pub fn to_report_with_config<'a>(
        &self,
        src_name: &'a str,
        config: ariadne::Config,
    ) -> ariadne::Report<'a, (&'a str, std::ops::Range<usize>)> {
        use ariadne::{Color, Label, Report, ReportKind};
        match self {
            LoweringError::Unsupported { span, message } => {
                Report::build(ReportKind::Error, src_name, span.start)
                    .with_config(config)
                    .with_message("lowering error")
                    .with_label(
                        Label::new((src_name, (*span).into()))
                            .with_message(message)
                            .with_color(Color::Red),
                    )
                    .finish()
            }
        }
    }
}

/// Output of [`lower_stmts`].
///
/// Mirrors the shape of [`crate::chl_parser::parser::ParseResult`]: a (possibly
/// partial) lowered expression is returned alongside every error encountered,
/// so callers can surface every diagnostic in one pass.  Failed sub-trees are
/// filled with [`TypedExprNode::Error`] placeholders — these are only valid
/// while `errors` is non-empty; callers must check `errors` before passing the
/// tree to inference or any downstream stage.
#[derive(Debug, Clone, PartialEq)]
pub struct LoweringResult {
    /// The lowered expression. `Some` even on error if recovery produced
    /// anything usable; `None` only when there is nothing structural to
    /// return at all (e.g. an empty top-level statement list).
    pub value: Option<Expr>,
    /// Errors collected during lowering.  Non-empty implies `value` (if
    /// `Some`) contains [`TypedExprNode::Error`] placeholders.
    pub errors: Vec<LoweringError>,
}

impl LoweringResult {
    /// `true` iff lowering succeeded with no errors at all.
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty() && self.value.is_some()
    }

    /// Collapse into a `Result`, treating any errors as failure. Convenient
    /// for call sites that don't care about partial output (e.g. tests).
    ///
    /// Panics if the invariant `value.is_some() || !errors.is_empty()` is
    /// violated. [`lower_stmts`] guarantees that invariant — either it
    /// produces an `Expr` (possibly with `Error` placeholders) or it records
    /// at least one error. The panic only fires on manually-constructed
    /// `LoweringResult { value: None, errors: vec![] }`.
    pub fn into_result(self) -> Result<Expr, Vec<LoweringError>> {
        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            Ok(self
                .value
                .expect("LoweringResult: empty errors but no value (invariant violation)"))
        }
    }
}

// ---------------------------------------------------------------------------
// Lowering context
// ---------------------------------------------------------------------------

/// Context for CHL → CCL lowering that carries registered data sources and sinks.
///
/// Zero-argument function calls whose name appears in `sources` are lowered to
/// [`TypedExprNode::Source`] nodes instead of failing with an
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

    /// Mint a unique `__result_N` name for the defer handle in generator functions.
    ///
    /// Counter-minted to avoid collisions when user code contains a binding
    /// named `__result` inside the same generator body.
    fn fresh_result_name(&mut self) -> String {
        let id = self.next_synthetic_id;
        self.next_synthetic_id += 1;
        format!("__result_{id}")
    }

    /// Mint a unique `__acc_stream_N` binding name for the
    /// Record-bodied Join's stream output in a feed-containing mutation
    /// loop.  The surrounding let-binding projects `.step ▷ Last` for
    /// the scalar accumulator and `.to_<defer>` for each per-feed
    /// stream from this one Join (the multi-feed-per-defer subcase
    /// suffixes those as `.to_<defer>_<k>`).
    fn fresh_acc_stream_name(&mut self) -> String {
        let id = self.next_synthetic_id;
        self.next_synthetic_id += 1;
        format!("__acc_stream_{id}")
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

/// Lower a single CHL expression to a CCL expression.
pub fn lower_expr(
    expr: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    match &expr.node {
        ChlExpr::Lit(lit) => lower_constant(lit),
        ChlExpr::Name(id) => Ok(Expr::var(id.as_str().to_string())),
        ChlExpr::BinOp { left, op, right } => lower_binop(left, *op, right, ctx),
        ChlExpr::Compare {
            left,
            ops,
            comparators,
        } => lower_compare(left, ops, comparators, ctx),
        ChlExpr::BoolOp { op, operands } => lower_boolop(expr.span, *op, operands, ctx),
        ChlExpr::List(elts) => {
            let items: Result<Vec<_>, _> = elts.iter().map(|e| lower_expr(e, ctx)).collect();
            Ok(Expr::list(items?))
        }
        ChlExpr::ListComp(comp) => lower_list_comp(comp, ctx),
        ChlExpr::GenExp(comp) => lower_list_comp(comp, ctx),
        ChlExpr::Call { func, args } => lower_call(func, args, ctx),
        ChlExpr::Tuple(elts) => {
            let items: Result<Vec<_>, _> = elts.iter().map(|e| lower_expr(e, ctx)).collect();
            Ok(Expr::tuple(items?))
        }
        ChlExpr::Subscript { target, index } => match &index.node {
            ChlExpr::Lit(ChlLit::Int(n)) => {
                let idx: usize = (*n).try_into().map_err(|_| {
                    LoweringError::unsupported(index.span, "tuple index must be non-negative")
                })?;
                Ok(Expr::apply(lower_expr(target, ctx)?, Expr::proj_index(idx)))
            }
            _ => Err(LoweringError::unsupported(
                index.span,
                "only integer subscripts are supported",
            )),
        },
        // Record literal `{field: expr, ...}` — keys are bare identifiers.
        // Lowered to a `Record` constructor: `{x: 1, y: "foo"}` becomes
        // `Record([("x", Lit(1)), ("y", Lit("foo"))])`.
        ChlExpr::Record(fields) => {
            let mut out = Vec::with_capacity(fields.len());
            for RecordField {
                name,
                name_span,
                value,
            } in fields
            {
                let field_name = name.as_str().to_string();
                if out.iter().any(|(k, _)| k == &field_name) {
                    return Err(LoweringError::unsupported(
                        *name_span,
                        format!("duplicate key `{field_name}` in record literal"),
                    ));
                }
                out.push((field_name, lower_expr(value, ctx)?));
            }
            Ok(Expr::new(TypedExprNode::Record(out)))
        }
        // Dict literal with expression keys is not supported as a record.
        ChlExpr::Dict(_) => Err(LoweringError::unsupported(
            expr.span,
            "dict literals (with non-identifier keys) are not yet supported",
        )),
        // Attribute access `r.field` → `Apply(r, Proj(Field("field")))`.
        ChlExpr::Attribute { target, attr, .. } => Ok(Expr::apply(
            lower_expr(target, ctx)?,
            Expr::proj_field(attr.as_str()),
        )),
        ChlExpr::Lambda { params, body } => lower_lambda(expr.span, params, body, ctx),
        ChlExpr::UnaryOp { op, operand } => lower_unaryop(*op, operand, ctx),
        // Ternary `then_expr if cond else else_expr` → Case { [guard → value, true → orelse] }
        ChlExpr::IfExp {
            cond,
            then_expr,
            else_expr,
        } => {
            let guard = lower_expr(cond, ctx)?;
            let true_arm = lower_expr(then_expr, ctx)?;
            let false_arm = lower_expr(else_expr, ctx)?;
            Ok(Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: vec![
                    Branch {
                        pattern: None,
                        guard,
                        body: true_arm,
                    },
                    Branch {
                        pattern: None,
                        guard: Expr::lit(Lit::Bool(true)),
                        body: false_arm,
                    },
                ],
            }))
        }
        // `target << value` — feed into a deferred output.
        ChlExpr::Feed { target, value } => lower_feed(target, value, ctx),
        // `yield e` is only valid in a generator-for body; reject elsewhere.
        ChlExpr::Yield(_) => Err(LoweringError::unsupported(
            expr.span,
            "yield outside a generator for-loop context",
        )),
        // Parse-recovery placeholder: silently substitute a CCL placeholder so
        // we keep lowering the rest of the tree. The parse error itself has
        // already been reported via [`crate::chl_parser::ParseResult::errors`];
        // adding a redundant lowering error would just clutter the diagnostic
        // output. [`crate::ccl::context::compile_program`] guards against this
        // placeholder ever reaching inference.
        ChlExpr::Error => Ok(Expr::error()),
    }
}

/// Lower a block of CHL statements to a nested CCL expression.
///
/// All statements except the last must be simple name assignments
/// (`x = expr`), annotated assignments (`x: T = expr`), augmented
/// assignments (`x op= expr`), or function definitions (`def f(...): ...`);
/// each becomes an [`TypedExprNode::Let`] binding wrapping the rest. Function
/// definitions are lowered via [`lower_function_body`], which detects
/// generator functions (single `for`/`yield` body) and regular functions.
///
/// The last statement must be a bare expression ([`ChlStmt::Expr`])
/// or an `if`/`else` block.
///
/// When sink bindings are registered during lowering (e.g. from `http_serve`),
/// the final expression is wrapped so the program ends in
/// `ExprStmt(<body>, Record{sink: Var(sink), …})`.  The `Record` is the
/// sink-binding contract; each field is the name that [`crate::ccl::desugar_defers`]
/// resolves to the computed response morphism.  After `desugar_defers` removes
/// all `Feed` nodes, `simplify` drops the `ExprStmt`, leaving a clean
/// `Let* Record{…}` shape for `compile_program`.
pub fn lower_stmts(stmts: &[Spanned<ChlStmt>], ctx: &mut LoweringContext) -> LoweringResult {
    let mut errors: Vec<LoweringError> = Vec::new();
    let value = lower_stmts_recovering(stmts, ctx, &mut errors);
    LoweringResult { value, errors }
}

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
fn lower_stmts_recovering(
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
fn lower_stmts_inner(
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
fn lower_final_stmt(
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
fn lower_middle_stmt(
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
fn collect_stmt_names(stmts: &[Spanned<ChlStmt>], names: &mut HashSet<String>) {
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
fn extract_name_target(
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
fn name_target_as_name(target: &Spanned<AssignTarget>) -> Option<&str> {
    if let AssignTarget::Name(id) = &target.node {
        Some(id.as_str())
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Lower a CHL type annotation expression to a CCL [`Type`].
///
/// Handles the primitive type names: `int` → [`Type::Base`]([`BaseType::Int`]),
/// `str` → `String`, `bool` → `Bool`, and `None` (the constant) → `Unit`.
fn lower_type_annotation(annotation: &Spanned<ChlExpr>) -> Result<Type, LoweringError> {
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
fn lower_if(
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

fn lower_constant(constant: &ChlLit) -> Result<Expr, LoweringError> {
    let lit = match constant {
        ChlLit::Int(n) => Lit::Int(*n),
        ChlLit::String(s) => Lit::String(s.clone()),
        ChlLit::Bool(b) => Lit::Bool(*b),
        ChlLit::None => Lit::Unit,
    };
    Ok(Expr::lit(lit))
}

/// Lower a CHL function call to a CCL built-in expression.
///
/// Supported built-ins:
///
/// | CHL call | CCL node | Arity |
/// |---|---|---|
/// | `sum(expr)` | [`TypedExprNode::Aggregate`] (`Sum`) | 1 |
/// | `max(expr)` | [`TypedExprNode::Aggregate`] (`Max`) | 1 |
/// | `groupby(collection, key)` | `Lambda`/`Apply` encoding with refinement | 2 |
///
/// Unknown function names return [`LoweringError::Unsupported`]. (CHL has no
/// keyword-argument syntax, so the parser already rejects those.)
fn lower_call(
    func: &Spanned<ChlExpr>,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let name = match &func.node {
        ChlExpr::Name(id) => id.as_str(),
        _ => {
            return Err(LoweringError::unsupported(
                func.span,
                "only named function calls are supported",
            ));
        }
    };

    match name {
        // groupby(c: I -> A, key_fn: A -> K) lowers to
        //   λ k → cast({I | λ r → key_fn(c(r)) == k} ⇒ A, λ i → c(i))
        //
        // The cast wraps the (unrefined) inner λ i → c(i) under a function
        // type whose domain carries the partition predicate.  The
        // predicate captures `k` from the outer lambda's scope —
        // surfacing this as the canonical "dependent refinement" site
        // without a dedicated AST shape.
        "groupby" => {
            if args.len() != 2 {
                return Err(LoweringError::unsupported(
                    func.span,
                    "groupby requires exactly two arguments",
                ));
            }
            let collection = lower_expr(&args[0], ctx)?;
            let key_fn = lower_expr(&args[1], ctx)?;

            let pred_lambda = Expr::lambda(
                "__gb_r",
                Type::Hole,
                Expr::binop(
                    Expr::apply(Expr::apply(Expr::var("__gb_r"), collection.clone()), key_fn),
                    BinOpKind::Compare(CompareKind::Equals),
                    Expr::var("__gb_k"),
                ),
            );
            let inner_body = Expr::apply(Expr::var("__gb_i"), collection);
            let unrefined_inner = Expr::lambda("__gb_i", Type::Hole, inner_body);
            let target_ty = refined_fn_type(Type::Hole, pred_lambda, Type::Hole, "groupby");
            Ok(Expr::lambda(
                "__gb_k",
                Type::Hole,
                make_cast(unrefined_inner, target_ty),
            ))
        }
        "sum" | "max" => {
            if args.len() != 1 {
                return Err(LoweringError::unsupported(
                    func.span,
                    "aggregate functions require exactly one argument",
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
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("unknown zero-argument function: {name}; register it as a data source"),
                ));
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
    left: &Spanned<ChlExpr>,
    op: ChlBinOp,
    right: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let left_expr = lower_expr(left, ctx)?;
    let right_expr = lower_expr(right, ctx)?;
    // CollectionUnion lowers to a dedicated N-ary CCL node — it denotes a
    // value-level collection merge rather than a scalar binary op.
    // The parser produces 2-ary trees; `simplify` flattens nested
    // `a ++ b ++ c` into a single N-ary `CollectionUnion` later.
    if op == ChlBinOp::CollectionUnion {
        return Ok(Expr::collection_union(vec![left_expr, right_expr]));
    }
    let kind = chl_binop_to_ccl(op);
    Ok(Expr::binop(left_expr, kind, right_expr))
}

/// Map a CHL [`ChlBinOp`] to its CCL [`BinOpKind`] counterpart.
///
/// The mapping mirrors the variant set on `chl_ast::BinOp`, which only
/// enumerates the operators CHL accepts (`/`, `%`, `**`, `>>`, `~` are
/// rejected at parse time and never appear here). `LogicalAnd/Or/Xor` map
/// to CCL boolean logic — CHL reuses the `&`/`|`/`^` tokens for logical
/// (not bitwise) operations. `CollectionUnion` is excluded: it lowers
/// to a dedicated [`TypedExprNode::CollectionUnion`] node, not a
/// [`BinOpKind`], and is handled directly in [`lower_binop`].
fn chl_binop_to_ccl(op: ChlBinOp) -> BinOpKind {
    match op {
        ChlBinOp::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        ChlBinOp::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        ChlBinOp::Mul => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        ChlBinOp::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        ChlBinOp::LogicalAnd => BinOpKind::BoolLogic(LogicKind::And),
        ChlBinOp::LogicalOr => BinOpKind::BoolLogic(LogicKind::Or),
        ChlBinOp::LogicalXor => BinOpKind::BoolLogic(LogicKind::Xor),
        ChlBinOp::CollectionUnion => unreachable!(
            "ChlBinOp::CollectionUnion is handled directly in lower_binop and never reaches this function"
        ),
    }
}

/// Lower an augmented assignment `name op= value` to the equivalent
/// `name op value` binary operation. The caller has already extracted the
/// target name via [`extract_name_target`].
fn lower_aug_binop(
    target_name: &str,
    op: AugOp,
    value: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let left_expr = Expr::var(target_name.to_string());
    let right_expr = lower_expr(value, ctx)?;
    let kind = match op {
        AugOp::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        AugOp::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        AugOp::Mul => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        AugOp::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
    };
    Ok(Expr::binop(left_expr, kind, right_expr))
}

fn lower_feed(
    target: &Spanned<ChlExpr>,
    value: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // `x << v` is an expression form, so the LHS is parsed as an `Expr`
    // rather than an `AssignTarget`. Semantically we still require a bare
    // identifier here.
    let name = match &target.node {
        ChlExpr::Name(id) => id.as_str().to_string(),
        _ => {
            return Err(LoweringError::unsupported(
                target.span,
                "handle binding: only simple name targets are supported",
            ));
        }
    };
    Ok(Expr::feed(name, lower_expr(value, ctx)?))
}

fn lower_define(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let name = extract_name_target(target, "handle defining")?;
    Ok(Expr::define(name, lower_expr(value, ctx)?))
}

/// Lower a CHL unary expression to a CCL [`Expr::UnaryOp`].
///
/// - `Neg` (`-x`) lowers to [`UnaryOpKind::Neg`].
/// - `Not` (`not x`) lowers to [`UnaryOpKind::Not`].
///
/// The CHL parser already rejects `+x` and `~x`, so they need no special
/// handling here.
fn lower_unaryop(
    op: UnaryOp,
    operand: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let inner = lower_expr(operand, ctx)?;
    let kind = match op {
        UnaryOp::Neg => UnaryOpKind::Neg,
        UnaryOp::Not => UnaryOpKind::Not,
    };
    // Constant-fold `-Int(n)` to `Lit(Int(-n))`. Downstream stages
    // (`operator_conversion`'s list-literal path in particular) only accept
    // concrete literals as list elements; without this fold, programs like
    // `[-1, 2, -3, 4]` fall out of the supported subset.
    if let UnaryOpKind::Neg = kind
        && let TypedExprNode::Lit(Lit::Int(n)) = &inner.node
    {
        return Ok(Expr::lit(Lit::Int(-*n)));
    }
    Ok(Expr::unary(kind, inner))
}

/// Lower a CHL comparison expression to a CCL [`Expr::BinOp`] chain.
///
/// CHL comparison expressions may chain multiple operators, e.g. `a < b < c`
/// desugars to `a < b and b < c`. Each consecutive pair of operands is compared
/// with its corresponding operator and the results are combined with logical AND.
fn lower_compare(
    left: &Spanned<ChlExpr>,
    ops: &[CmpOp],
    comparators: &[Spanned<ChlExpr>],
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
            CmpOp::Eq => CompareKind::Equals,
            CmpOp::NotEq => CompareKind::NotEquals,
            CmpOp::Lt => CompareKind::Less,
            CmpOp::LtE => CompareKind::LessOrEq,
            CmpOp::Gt => CompareKind::Greater,
            CmpOp::GtE => CompareKind::GreaterOrEq,
        };
        // Clone the shared middle operand so both adjacent pairs can own it.
        comparisons.push(Expr::binop(
            operands[i].clone(),
            BinOpKind::Compare(kind),
            operands[i + 1].clone(),
        ));
    }

    // Single comparison: return it directly.
    // Chained comparisons: fold with logical AND. CHL's chained-comparison
    // semantics match Python's (`a < b < c` ≡ `a < b and b < c`).
    Ok(comparisons
        .into_iter()
        .reduce(|acc, cmp| Expr::binop(acc, BinOpKind::BoolLogic(LogicKind::And), cmp))
        .expect("ops is non-empty"))
}

/// Lower a CHL boolean operator expression to a left-folded [`Expr::BinOp`] chain.
///
/// `BoolOp` carries a list of two or more operands sharing a single
/// operator (`and` / `or`). For example, `a and b and c` becomes
/// `(a and b) and c` — two nested [`BinOpKind::BoolLogic`] nodes.
fn lower_boolop(
    bool_span: Span,
    op: BoolOp,
    operands: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if operands.len() < 2 {
        return Err(LoweringError::unsupported(
            bool_span,
            "boolean operator must have at least two operands",
        ));
    }
    let kind = match op {
        BoolOp::And => BinOpKind::BoolLogic(LogicKind::And),
        BoolOp::Or => BinOpKind::BoolLogic(LogicKind::Or),
    };
    // Fold left-to-right: `a and b and c` → `(a and b) and c`.
    let mut acc = lower_expr(&operands[0], ctx)?;
    for value in &operands[1..] {
        acc = Expr::binop(acc, kind, lower_expr(value, ctx)?);
    }
    Ok(acc)
}

/// Validate that the function or lambda has at least one parameter.
///
/// The CHL parser already rejects `*args`, `**kwargs`, keyword-only and
/// default arguments at the syntactic level, so the only remaining check
/// is that there is at least one positional parameter. Shared between
/// [`lower_lambda`] and [`lower_function_body`].
fn validate_function_params(fn_span: Span, params: &[Param]) -> Result<(), LoweringError> {
    if params.is_empty() {
        return Err(LoweringError::unsupported(
            fn_span,
            "function/lambda with no parameters not supported",
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
fn uncurry_params(params: &[Param], body_expr: Expr, ctx: &mut LoweringContext) -> Expr {
    if params.len() == 1 {
        return Expr::lambda(params[0].name.as_str(), Type::Hole, body_expr);
    }
    // Mint the tuple name after `body_expr` is lowered so that inner
    // multi-arg lambdas (which bump the counter during body lowering)
    // receive strictly smaller ids than the outer lambda. Together with
    // the reserved `__arg_tuple_` prefix (user code cannot bind
    // double-underscore names here), this guarantees the outer
    // substitution's inserted `Var(outer_name)` never collides with an
    // inner binder.
    let tuple_name = ctx.fresh_tuple_arg();
    let body_with_subs = params.iter().enumerate().fold(body_expr, |acc, (i, arg)| {
        let proj = Expr::apply(Expr::var(&tuple_name), Expr::proj_index(i));
        substitute_param_in_body(acc, arg.name.as_str(), &proj)
    });
    Expr::lambda(&tuple_name, Type::Hole, body_with_subs)
}

/// Lower a CHL lambda expression to an [`Expr::Lambda`] via
/// [`uncurry_params`].
///
/// Users who want genuine currying still write it explicitly
/// (`lambda x: lambda y: ...` or an explicit `curry(f)` call); those nest
/// through the general Lambda rule and remain unsupported past operator
/// conversion — tracked as follow-up work.
///
/// `validate_function_params` only checks for at least one parameter; the
/// CHL parser already rejects `*args`, `**kwargs`, defaults, and keyword-only
/// arguments at parse time.
fn lower_lambda(
    lambda_span: Span,
    params: &[Param],
    body: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    validate_function_params(lambda_span, params)?;
    let body_expr = lower_expr(body, ctx)?;
    Ok(uncurry_params(params, body_expr, ctx))
}

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`,
/// respecting binder shadowing introduced by inner `Lambda` and `Let` nodes.
///
/// Used during multi-arg lambda lowering to rewrite named CHL parameters
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
    // Fast path: substitute Var hits, return atoms unchanged without traversal.
    match &expr.node {
        TypedExprNode::Var(n) if n == name => return replacement.clone(),
        TypedExprNode::Var(_)
        | TypedExprNode::Lit(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer => return expr,
        _ => {}
    }

    let Expr {
        node,
        ty,
        user_annotation,
    } = expr;

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
                let pred = &r.predicate;
                let inner = pred.borrow().clone();
                *pred.borrow_mut() = substitute_param_in_body(inner, name, replacement);
            }
            TypedExprNode::Lambda {
                param,
                body: Box::new(substitute_param_in_body(*body, name, replacement)),
                refinement,
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_bound = substitute_param_in_body(*bound_expr, name, replacement);
            // Shadowing: if the Let rebinds `name`, leave its body alone.
            let new_body = if binding.name == name {
                *body
            } else {
                substitute_param_in_body(*body, name, replacement)
            };
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(new_bound),
                body: Box::new(new_body),
            }
        }
        // Loop params shadow `name` inside `loop_body`, so we can't fall
        // through to the generic structural recursion below.  Delegate to
        // the shared shadowing-aware helper.
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => {
            crate::ccl::walk_loop_children(params, init_args, source, loop_body, Some(name), |e| {
                substitute_param_in_body(e, name, replacement)
            })
        }

        // All remaining variants (including the lowering-recovery `Error`
        // placeholder, which has no children): pure structural recursion.
        node => {
            let mut expr = Expr {
                node,
                ty,
                user_annotation,
            };
            expr.map_children(|child| substitute_param_in_body(child, name, replacement));
            return expr;
        }
    };

    Expr {
        node: new_node,
        ty,
        user_annotation,
    }
}

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
fn lower_generator_for(
    target: &Spanned<AssignTarget>,
    iter: &Spanned<ChlExpr>,
    body: &[Spanned<ChlStmt>],
    outer_bindings: &HashSet<String>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let iter_var = extract_name_target(target, "for-loop target")?;

    if for_body_has_yield(body) {
        // A generator with loop-carried state (brainstorm §4b) — yield
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
fn find_mutation_loop_vars(
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
fn find_nested_mutation_var(
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
/// brainstorm §4b `running_totals` shape: `total += item; yield total`).
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
fn lower_generator_or_mutation_loop(
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
    let loop_expr = Expr::loop_node(acc_names.to_vec(), init_args, source, step_lambda);

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
///   with loop-carried state (brainstorm §4b's `running_totals`) reuse
///   the same `Loop` lowering as a plain mutation loop — the yield's
///   defer is collected by `desugar_defers` as another `to_<defer>`
///   field on the body Record.
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

/// Lower a Python function definition body to a CCL expression.
///
/// Delegates entirely to [`lower_stmts_inner`] with the function's
/// parameter names as `outer_bindings`. If the function body's final
/// statement is a `for`-loop with a yield chain, it is lowered as a
/// generator; otherwise it's a regular function body.
fn lower_function_body(
    fn_span: Span,
    params: &[Param],
    body: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    validate_function_params(fn_span, params)?;
    let outer_bindings: HashSet<String> =
        params.iter().map(|p| p.name.as_str().to_string()).collect();
    // http_serve is not permitted inside function bodies.
    let body_expr = lower_stmts_inner(body, &outer_bindings, ctx, false)?;
    Ok(uncurry_params(params, body_expr, ctx))
}

/// Lower a CHL list comprehension to the CCL Lambda/Apply encoding.
///
/// Handles three cases based on the number of generators and predicates:
///
/// **Single generator, no predicate** — identity encoding:
/// ```text
/// λ __iter_record → __iter_record ▷ lower(source) ▷ (λ var → lower(body))
/// ```
///
/// **Multiple generators / non-equality predicates** — loop-join encoding.
/// The outer lambda carries a [`Refinement`](crate::ccl::Refinement) predicate
/// with the combined guard expression; the runtime filters via a correlation vector:
/// ```text
/// λ __iter_record : {T | pred} →
///   __iter_record[0] ▷ lower(source0) ▷ (λ var0 →
///     __iter_record[1] ▷ lower(source1) ▷ (λ var1 → lower(body)))
/// ```
///
/// **Two generators, single equality predicate** — hash-join encoding.
/// Detected by [`try_extract_ccl_equality_join`] on the lowered predicate.
/// The outer lambda carries the same [`Refinement`](crate::ccl::Refinement)
/// predicate (an equality `build_var == probe_var`); join planning
/// (`crate::ccl::join_plan`) recognises the equality shape and translates it to
/// an O(N+M) hash-join-based restriction:
/// ```text
/// λ __iter_record : {T | build_var == probe_var} →
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
fn lower_list_comp(comp: &Comprehension, ctx: &mut LoweringContext) -> Result<Expr, LoweringError> {
    // CHL's comprehension stores clauses (`for ... in ...` and `if ...`) in a
    // single flat list, interleaved in source order. Regroup into one
    // generator per `for`, each followed by any adjacent `if`s, so the rest
    // of this routine can operate on (target, iter, [guards]) triples.
    let generators = group_comp_clauses(&comp.clauses)?;

    // ---- Phase 1: Lower each generator's source and register its loop variable ----
    // We keep the source operators and index extents for later use when building the
    // Apply/Lambda chains.  Each loop variable is pushed onto the lowering scope so
    // that body and predicate expressions can reference it.
    let mut gen_sources: Vec<Expr> = Vec::new();
    let mut gen_iter_vars: Vec<String> = Vec::new();

    for (target, iter, _) in generators.iter() {
        let source = lower_expr(iter, ctx)?;
        let var_name = extract_name_target(target, "comprehension target")?;
        gen_iter_vars.push(var_name);
        gen_sources.push(source);
    }

    // ---- Phase 2: Lower body and all predicates to CCL -------------------------
    let body = lower_expr(&comp.element, ctx)?;

    // Lower every `if` guard from each generator to CCL.  We hold on to the
    // original CHL nodes only to build human-readable description strings;
    // all detection logic operates on the lowered CCL expressions.
    let chl_preds: Vec<&Spanned<ChlExpr>> = generators
        .iter()
        .flat_map(|(_, _, ifs)| ifs.iter().copied())
        .collect();
    let lowered_preds: Vec<Expr> = chl_preds
        .iter()
        .map(|e| lower_expr(e, ctx))
        .collect::<Result<_, _>>()?;

    // Combine all `if` guards into a single loop-join predicate (used when hash
    // join is not applicable — non-equality, 3+ generators, or multiple predicates).
    // Description strings come from `chl_expr_to_string`; the format is a
    // pretty-printed-ish rendering used downstream for refinement labels.
    let mut pred_op: Option<Expr> = None;
    let mut pred_desc = String::new();
    for (chl_pred, lowered) in chl_preds.iter().zip(lowered_preds) {
        let pred_str = chl_expr_to_string(&chl_pred.node);
        pred_op = Some(match pred_op {
            Some(lhs) => {
                pred_desc.push_str(&format!(" and {pred_str}"));
                Expr::binop(lhs, BinOpKind::BoolLogic(LogicKind::And), lowered)
            }
            None => {
                pred_desc = pred_str;
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
        // Lowering emits a `cast(refined_fn_type, λ outer_var → body_expr)`
        // here — a pure type-level assertion of the predicate-refined
        // domain.  The refinement is carried by the cast's target type; the
        // Cast Apply arm in `infer_simple_sub` constructs the refined result
        // from it, and the generic annotation handler infers the predicate's
        // sub-expressions.
        let pred_lambda = Expr::lambda(restr_outer_var, Type::Hole, pred_expr);
        let unrefined_lambda = Expr::lambda(outer_var, Type::Hole, body_expr);
        let target_ty = refined_fn_type(Type::Hole, pred_lambda, Type::Hole, &pred_desc);
        Ok(make_cast(unrefined_lambda, target_ty))
    } else {
        Ok(Expr::lambda(outer_var, Type::Hole, body_expr))
    }
}

// ---------------------------------------------------------------------------
// Comprehension regrouping
// ---------------------------------------------------------------------------

/// One generator clause regrouped from a CHL comprehension's flat clause list:
/// `(target, iter, ifs)`, where `ifs` is the sequence of `if`-guards that
/// followed this `for` in source order before the next `for`.
type CompGenerator<'a> = (
    &'a Spanned<AssignTarget>,
    &'a Spanned<ChlExpr>,
    Vec<&'a Spanned<ChlExpr>>,
);

/// Regroup the flat CHL comprehension clause list into one [`CompGenerator`]
/// per `for` clause.
///
/// CHL stores comprehension clauses (`for ... in ...` and `if ...`) in a
/// single list in source order; the downstream lowering logic expects each
/// generator's guards bundled with it, so we walk the clauses and attach each
/// `If` to its most recent `For`. A leading `If` (before any `For`) is a
/// parse-level error category but is defensively rejected here too.
fn group_comp_clauses(clauses: &[CompClause]) -> Result<Vec<CompGenerator<'_>>, LoweringError> {
    let mut out: Vec<CompGenerator<'_>> = Vec::new();
    for clause in clauses {
        match clause {
            CompClause::For { target, iter } => out.push((target, iter, Vec::new())),
            CompClause::If(guard) => {
                let Some(last) = out.last_mut() else {
                    return Err(LoweringError::unsupported(
                        guard.span,
                        "comprehension `if` clause must follow a `for` clause",
                    ));
                };
                last.2.push(guard);
            }
        }
    }
    // The CHL `comp_clauses` parser uses `.at_least(1)`, so the input list is
    // never empty in a parsed comprehension.
    assert!(
        !out.is_empty(),
        "group_comp_clauses: empty clause list (parser invariant violated)"
    );
    Ok(out)
}

/// Render a CHL expression to roughly source-like text.
///
/// Downstream lowering uses this string only as a label embedded in
/// refinement descriptions; precise formatting does not affect correctness,
/// just readability of generated names. Only the operator and literal forms
/// that actually appear inside comprehension guards are handled in detail;
/// anything else falls through to a `{:?}` debug dump.
fn chl_expr_to_string(expr: &ChlExpr) -> String {
    match expr {
        ChlExpr::Lit(ChlLit::Int(n)) => n.to_string(),
        ChlExpr::Lit(ChlLit::String(s)) => format!("{s:?}"),
        ChlExpr::Lit(ChlLit::Bool(true)) => "True".into(),
        ChlExpr::Lit(ChlLit::Bool(false)) => "False".into(),
        ChlExpr::Lit(ChlLit::None) => "None".into(),
        ChlExpr::Name(id) => id.as_str().to_string(),
        ChlExpr::Attribute { target, attr, .. } => {
            format!("{}.{}", chl_expr_to_string(&target.node), attr)
        }
        ChlExpr::Compare {
            left,
            ops,
            comparators,
        } => {
            let mut s = chl_expr_to_string(&left.node);
            for (op, comp) in ops.iter().zip(comparators.iter()) {
                let op_str = match op {
                    CmpOp::Eq => "==",
                    CmpOp::NotEq => "!=",
                    CmpOp::Lt => "<",
                    CmpOp::LtE => "<=",
                    CmpOp::Gt => ">",
                    CmpOp::GtE => ">=",
                };
                s.push(' ');
                s.push_str(op_str);
                s.push(' ');
                s.push_str(&chl_expr_to_string(&comp.node));
            }
            s
        }
        ChlExpr::BinOp { left, op, right } => {
            let op_str = match op {
                ChlBinOp::Add => "+",
                ChlBinOp::Sub => "-",
                ChlBinOp::Mul => "*",
                ChlBinOp::FloorDiv => "//",
                ChlBinOp::LogicalAnd => "&",
                ChlBinOp::LogicalOr => "|",
                ChlBinOp::LogicalXor => "^",
                ChlBinOp::CollectionUnion => "++",
            };
            format!(
                "{} {} {}",
                chl_expr_to_string(&left.node),
                op_str,
                chl_expr_to_string(&right.node)
            )
        }
        ChlExpr::BoolOp { op, operands } => {
            let sep = match op {
                BoolOp::And => " and ",
                BoolOp::Or => " or ",
            };
            operands
                .iter()
                .map(|e| chl_expr_to_string(&e.node))
                .collect::<Vec<_>>()
                .join(sep)
        }
        ChlExpr::UnaryOp { op, operand } => {
            let op_str = match op {
                UnaryOp::Neg => "-",
                UnaryOp::Not => "not ",
            };
            format!("{}{}", op_str, chl_expr_to_string(&operand.node))
        }
        ChlExpr::Call { func, args } => {
            let args_str = args
                .iter()
                .map(|a| chl_expr_to_string(&a.node))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}({})", chl_expr_to_string(&func.node), args_str)
        }
        ChlExpr::Subscript { target, index } => format!(
            "{}[{}]",
            chl_expr_to_string(&target.node),
            chl_expr_to_string(&index.node)
        ),
        other => format!("{other:?}"),
    }
}

// ---------------------------------------------------------------------------
// http_serve helpers
// ---------------------------------------------------------------------------

/// Returns `true` when `target` is a 2-element name tuple and `value` is a
/// call to `http_serve` with exactly 3 string-literal arguments.
fn is_http_serve_tuple_assign(target: &Spanned<AssignTarget>, value: &Spanned<ChlExpr>) -> bool {
    let AssignTarget::Tuple(elts) = &target.node else {
        return false;
    };
    if elts.len() != 2 {
        return false;
    }
    if !elts.iter().all(|e| matches!(e.node, AssignTarget::Name(_))) {
        return false;
    }
    let ChlExpr::Call { func, args } = &value.node else {
        return false;
    };
    if args.len() != 3 {
        return false;
    }
    matches!(&func.node, ChlExpr::Name(id) if id == "http_serve")
        && args
            .iter()
            .all(|a| matches!(&a.node, ChlExpr::Lit(ChlLit::String(_))))
}

/// Extract `(requests_var, responses_var)` from a 2-element name tuple target.
fn extract_http_serve_names(
    target: &Spanned<AssignTarget>,
) -> Result<(String, String), LoweringError> {
    let AssignTarget::Tuple(elts) = &target.node else {
        return Err(LoweringError::unsupported(
            target.span,
            "http_serve target must be a 2-tuple",
        ));
    };
    let extract = |t: &Spanned<AssignTarget>| match &t.node {
        AssignTarget::Name(id) => Ok(id.as_str().to_string()),
        _ => Err(LoweringError::unsupported(
            t.span,
            "http_serve tuple elements must be simple names",
        )),
    };
    Ok((extract(&elts[0])?, extract(&elts[1])?))
}

/// Extract `(port, method, path)` string literals from the `http_serve(...)` call.
fn extract_http_serve_args(
    value: &Spanned<ChlExpr>,
) -> Result<(String, String, String), LoweringError> {
    let ChlExpr::Call { args, .. } = &value.node else {
        return Err(LoweringError::unsupported(
            value.span,
            "expected http_serve call",
        ));
    };
    let extract = |expr: &Spanned<ChlExpr>| match &expr.node {
        ChlExpr::Lit(ChlLit::String(s)) => Ok(s.clone()),
        _ => Err(LoweringError::unsupported(
            expr.span,
            "http_serve arguments must be string literals",
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

    /// Parse a CHL expression and return the AST node.
    fn parse_expr(code: &str) -> Spanned<ChlExpr> {
        crate::chl_parser::parse_expression(code)
            .into_result()
            .expect("Failed to parse expression")
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

    /// Parse a CHL module and return the statement list.
    fn parse_module(code: &str) -> Vec<Spanned<ChlStmt>> {
        crate::chl_parser::parse_module(code)
            .into_result()
            .expect("Failed to parse module")
            .body
    }

    /// Lower `stmts`, expect exactly one lowering error, and return it.
    ///
    /// Test-only convenience: most negative-path tests want to check the
    /// single error they expect against a pattern, so we unpack the `Vec`
    /// here once instead of at every call site.
    fn expect_one_lowering_error(stmts: &[Spanned<ChlStmt>]) -> LoweringError {
        let errs = lower_stmts(stmts, &mut LoweringContext::default())
            .into_result()
            .expect_err("expected lowering error");
        assert_eq!(
            errs.len(),
            1,
            "expected exactly one lowering error, got {}: {errs:?}",
            errs.len()
        );
        errs.into_iter().next().unwrap()
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
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
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
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
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
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
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
        let err = expect_one_lowering_error(&stmts);
        assert!(matches!(err, LoweringError::Unsupported { .. }));
    }

    /// Brainstorm §4b — a generator with loop-carried state lowers to a
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

    /// `yield` without a value is rejected.
    /// Constructs that CHL deliberately doesn't support. Each used to be
    /// rejected by lowering (since `rustpython_parser` accepted them all);
    /// the new CHL parser rejects them at parse time — bare `yield`,
    /// decorators, and `for/else` because they aren't in the grammar, and
    /// subscript / attribute assignment targets because `AssignTarget` is
    /// restricted to bare names and tuple patterns.
    #[test]
    fn parser_rejects_constructs_outside_chl_grammar() {
        let cases: &[&str] = &[
            // Bare `yield` (no value).
            "def bad(xs):\n    for x in xs:\n        yield\nbad",
            // Function decorators.
            "@some_decorator\ndef f(x):\n    x + 1\nf",
            // `for/else`.
            "def bad(xs):\n    for x in xs:\n        yield x\n    else:\n        pass\nbad",
            // Subscript augmented-assignment target.
            "x = [1]\nx[0] += 1\nx",
            // Attribute augmented-assignment target.
            "x = 0\nx.field += 1\nx",
        ];
        for code in cases {
            let result = crate::chl_parser::parse_module(code);
            assert!(
                !result.errors.is_empty(),
                "expected parse error for:\n{code}"
            );
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
        "λ __gb_k → cast(({_ | λ __gb_r → __gb_r ▷ xs ▷ (λ x → x) == __gb_k} ⇒ _), λ __gb_i → __gb_i ▷ xs)"
    )]
    // List literal collection with a more complex key
    #[case(
        "groupby([1, 2, 3], lambda x: x // 2)",
        "λ __gb_k → cast(({_ | λ __gb_r → __gb_r ▷ [1, 2, 3] ▷ (λ x → x // 2) == __gb_k} ⇒ _), λ __gb_i → __gb_i ▷ [1, 2, 3])"
    )]
    // Key is a variable reference (pre-defined function)
    #[case(
        "groupby(xs, key_fn)",
        "λ __gb_k → cast(({_ | λ __gb_r → __gb_r ▷ xs ▷ key_fn == __gb_k} ⇒ _), λ __gb_i → __gb_i ▷ xs)"
    )]
    // Keyed aggregation
    #[case(
        "[sum(x) for x in groupby(xs, key_fn)]",
        "λ __iter_record → __iter_record ▷ (λ __gb_k → cast(({_ | λ __gb_r → __gb_r ▷ xs ▷ key_fn == __gb_k} ⇒ _), λ __gb_i → __gb_i ▷ xs)) ▷ (λ x → Sum(x))"
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
            Err(LoweringError::Unsupported { .. })
        ));
        let three_args = parse_expr("groupby(xs, f, extra)");
        assert!(matches!(
            lower_expr(&three_args, &mut LoweringContext::default()),
            Err(LoweringError::Unsupported { .. })
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
            matches!(err, LoweringError::Unsupported { .. }),
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
        assert!(matches!(err, LoweringError::Unsupported { .. }));
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
        let ccl = lower_stmts(&stmts, &mut ctx)
            .into_result()
            .expect("lowering failed");
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

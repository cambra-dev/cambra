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
//! | Lambda expressions `\x -> body`, `\x, y -> body` | single [`TypedExprNode::Lambda`] (tupled param when multi-arg) |
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
//! | Positional access `t.0` | [`TypedExprNode::Apply`] with [`TypedExprNode::Proj`]`(`[`crate::ccl::ProjKey::Index`]`)` |
//! | Collection lookup `c[k]` | [`TypedExprNode::Apply`] — the same node as the call `c(k)` |
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
//! Lowering itself does not α-rename — unlike SSA or ANF conversion it keeps
//! the tree shape un-normalized, preserving structure for optimization passes.
//! Binder *identity* is handled immediately afterwards by
//! [`crate::ccl::uniquify`], which mints a fresh [`crate::ccl::Name`] uid per
//! binding site without touching the tree shape.
//!
//! # Module layout
//!
//! This pass is split across several submodules, all re-exported here so that
//! the historical `crate::ccl::lower::…` paths continue to resolve:
//!
//! - [`stmts`] — statement-block lowering (`Let` chains, `if`/`else`, the
//!   `http_serve` tuple-assign wiring, mutation-loop dispatch).
//! - [`exprs`] — per-[`ChlExpr`] expression lowering (binops, comparisons,
//!   boolean ops, calls, unary ops, feeds, defines, constants).
//! - [`functions`] — lambda / `def` / parameter lowering (uncurrying).
//! - [`loops`] — `for`-loop, generator, and mutation-accumulation-loop lowering.
//! - [`comprehension`] — list-comprehension and generator-expression lowering.
//! - [`http`] — `http_serve` recognition predicates.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
    sync::Arc,
};

use crate::{
    ccl::{
        Branch, Expr, Lit, Type, TypedExprNode,
        provenance::{Nature, RewriteLabel},
    },
    chl_parser::ast::{
        Expr as ChlExpr, RecordField, Span, Spanned, Stmt as ChlStmt,
        VariantPayload as ChlVariantPayload,
    },
    interpreter::{DataSink, DataSourceDomainExtentImpl, http_server::SharedHttpServer},
};

mod comprehension;
mod exprs;
mod functions;
mod http;
mod loops;
mod stmts;
mod transactions;

// Pull every submodule's `pub(super)` helpers into the `lower` namespace so
// that sibling submodules can reach them via `use super::*`. The external
// `crate::ccl::lower::…` surface (`LoweringContext`, `LoweringError`,
// `LoweringResult`, `lower_expr`, `lower_stmts`, `http_requests_source_name`)
// is defined directly in this module as `pub`, so these imports stay private
// — there is nothing public left to re-export onward.
use comprehension::*;
use exprs::*;
use functions::*;
use http::*;
use loops::*;
use stmts::*;
use transactions::*;

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

impl std::fmt::Display for LoweringError {
    /// The error's own message, with no span or variant name — a single line, for
    /// a caller that renders the span itself (an ariadne report, a JSON
    /// diagnostic).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoweringError::Unsupported { message, .. } => f.write_str(message),
        }
    }
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

/// One `http_serve` route as lowering knows it: its reply sink and the address
/// it serves.
#[derive(Clone)]
pub struct LoweredRoute {
    pub(super) sink: Arc<dyn DataSink>,
    pub(super) port: u16,
    pub(super) method: String,
    pub(super) path: String,
}

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
    ///
    /// `pub(super)` so the statement (`http_serve` wiring) and expression
    /// (registered-source recognition) submodules can read and mutate the map
    /// directly; external callers go through the `register_source` /
    /// `take_sources` methods.
    pub(super) sources: HashMap<String, Rc<RefCell<dyn DataSourceDomainExtentImpl>>>,

    /// Sink bindings discovered during lowering, keyed by the CCL `Let`-binding name
    /// that holds the deferred responses computation (e.g. `"responses"`).  Each entry
    /// pairs the binding name with the [`DataSink`] that should receive the computed
    /// tiles (e.g. [`HttpServerSharedState`]).  Drained by
    /// [`take_sink_bindings`](Self::take_sink_bindings) after `lower_stmts` returns.
    ///
    /// `pub(super)` so the statement submodule can inspect it when deciding
    /// whether to wrap the program tail in the sink-binding `Record`.
    pub(super) sink_bindings: HashMap<String, Arc<dyn DataSink>>,

    /// One [`SharedHttpServer`] per TCP port, shared across all `http_serve` calls
    /// that use the same port.  Created lazily on the first `http_serve` for a port
    /// and reused for all subsequent ones, so only a single `tiny_http::Server`
    /// binds each port.
    ///
    /// `pub(super)` so the statement submodule's `http_serve` wiring can create
    /// and reuse the per-port server.
    pub(super) shared_servers: HashMap<u16, Arc<SharedHttpServer>>,

    /// Every `http_serve` route this context knows: those seeded from the
    /// registry and those this pass opened, by the route's source name.
    ///
    /// Keyed by *route* rather than by binding name, unlike
    /// [`sink_bindings`](Self::sink_bindings): the response binding is a name the
    /// program chooses and a new version may spell differently, whereas the route
    /// is the address's identity. Carries the address as well as the sink,
    /// because `sink()` is inherent on `HttpServerDataSource` and cannot be read
    /// back off the erased `dyn DataSourceDomainExtentImpl` in
    /// [`sources`](Self::sources), and because retiring a route needs the method
    /// and path to unregister.
    pub(super) http_routes: HashMap<String, LoweredRoute>,

    /// Every `http_serve` route lowered *in this pass*, by source name.
    ///
    /// Separate from [`sources`](Self::sources) because that map is seeded with
    /// the endpoints a previous version of the program opened
    /// ([`SourceSinkRegistry`](crate::ccl::context::SourceSinkRegistry)), so a name
    /// being present there means "already open", not "already lowered". Two
    /// `http_serve` calls on one route within a single program remain an error;
    /// re-lowering the same route in a later version is the reuse path.
    pub(super) http_routes_this_pass: HashSet<String>,

    /// Monotonic counter for minting unique synthetic names during lowering.
    /// Globally unique across nested scopes so inner binders cannot capture
    /// a reference inserted by an outer substitution.
    next_synthetic_id: usize,

    /// Names declared **transactional** via a `Mut(V, Txn)` annotation. A write
    /// to such a variable is only legal inside
    /// a `with begin():` block, and so is a *read*: a transactional mutable variable may
    /// be read only inside a `with begin():` block, which pins a
    /// snapshot-consistent view (a bare read outside one is rejected — the
    /// scope-aware read gate in [`lower_expr`], which skips a name a local binder
    /// shadows via `shadow_depth`).
    ///
    /// Base-name keyed, and used *only* at lowering time: it decides the `with
    /// begin():` variable-write shape (a `MutWrite` marker) and the out-of-block
    /// read diagnostic. Downstream mutable variable *identity* — which mutable variables
    /// `transact_phase` folds — is instead the `Mut(_, Txn)` type on the
    /// α-unique binding (see [`crate::ccl::transact_phase::collect_txn_mut_vars`]),
    /// so this set is no longer handed to the phase.
    pub(super) transactional_vars: HashSet<String>,

    /// Whether lowering is currently inside a `with begin():` transaction block.
    /// Inside one, a bare read of a transactional mutable variable is a snapshot read (fine)
    /// and an assignment to one is a `MutWrite`; outside one, a bare read is a
    /// lowering error (reads must happen inside a `with begin():` block). Nested
    /// transactions are rejected by checking this flag before entering a block.
    pub(super) in_tx_body: bool,

    /// Shadow-depth counter keyed by surface spelling: how many enclosing local
    /// binders — loop targets, comprehension generators, lambda/`def` params —
    /// currently bind each name. The `transactional_vars` set is keyed by base
    /// name, so a local variable merely *spelled* like a mutable variable would wrongly
    /// trip the out-of-block read gate (`for x in xs: … x …`); a name
    /// with a positive shadow depth is a genuine local, not the mutable variable, so the
    /// gate skips it. Mirrors `uniquify`'s env stack — push a binder's spelling
    /// on entering its body scope, pop on exit (see [`LoweringContext::with_shadowed`]).
    pub(super) shadow_depth: HashMap<String, usize>,

    /// Names of `def`s that carry a pass-by-reference `Mut` parameter. Such a
    /// function is lowered as a **curried** chain of named lambdas rather than
    /// the usual single tupled-parameter lambda, because a `Mut` parameter must
    /// stay a named binder for inlining to rename the callee's `MutWrite` target
    /// to the caller's mutable variable (a tuple projection cannot be a write target). Its
    /// call sites must apply curried to match — recorded here (the `def` lowers
    /// before its calls) so [`lower_call`] can pick the matching shape.
    ///
    /// **Block-scoped.** Keyed on the surface name (lowering precedes uniquify,
    /// so no α-unique name exists yet), the set is snapshot/restored around every
    /// nested block ([`lower_stmts_inner`]) so a `Mut`-param `def` local to one
    /// scope cannot leak its curried shape onto a same-named `def`/call in an
    /// enclosing or sibling scope. Within a block, the *last* definition of a name
    /// wins (see [`pre_register_mut_param_fns`]).
    pub(super) mut_param_fns: HashSet<String>,

    /// Whether lowering is currently inside a refinement predicate `{T where p}`
    /// (§6.4). The predicate's anonymous subject is written `_`, and while this
    /// flag is set a bare `_` in *term* position lowers to the reserved
    /// refinement binder [`crate::ccl::REFINEMENT_BINDER`] (`Name::elem()`)
    /// rather than an ordinary variable named `_`. Set only around the predicate
    /// (save/restore, so a nested annotation cannot leak it), it is what makes
    /// "`_` is the value being refined" a local rule of the predicate rather than
    /// a global meaning of `_`.
    pub(super) in_refinement_predicate: bool,

    /// Counter behind [`fresh_shared_hole`](Self::fresh_shared_hole).
    next_shared_hole: u32,
}

impl LoweringContext {
    /// A fresh [`Type::SharedHole`] id, unique within this lowering.
    ///
    /// Use one id per *relation* a desugaring wants to state, and stamp it on
    /// every position that relation covers: inference normalizes equal ids to one
    /// variable, so two positions carrying the same id are held to the same type.
    /// Ids are meaningless outside the tree they were minted for.
    pub(super) fn fresh_shared_hole(&mut self) -> Type {
        let id = self.next_shared_hole;
        self.next_shared_hole += 1;
        Type::SharedHole(id)
    }
    /// Register a data source so that `name()` lowers to `Source(name)`.
    pub fn register_source(
        &mut self,
        name: impl Into<String>,
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    ) {
        self.sources.insert(name.into(), source);
    }

    /// Perfom some action on the context with
    /// `in_refinement_predicate` set to true, then return that field
    /// to its previous value.
    pub fn with_in_refinement_predicate<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let old = self.in_refinement_predicate;
        self.in_refinement_predicate = true;
        let out = f(self);
        self.in_refinement_predicate = old;
        out
    }

    /// Every source registered in this context, for folding into the
    /// [`SourceSinkRegistry`](crate::ccl::context::SourceSinkRegistry) that outlives
    /// the compilation. Unlike [`take_sources`](Self::take_sources) this leaves
    /// the map in place, so it may be called before the drain.
    pub fn registered_sources(
        &self,
    ) -> impl Iterator<Item = (&str, &Rc<RefCell<dyn DataSourceDomainExtentImpl>>)> {
        self.sources.iter().map(|(n, s)| (n.as_str(), s))
    }

    /// Every `http_serve` route this context knows, by source name.
    pub fn registered_routes(&self) -> impl Iterator<Item = (&str, &LoweredRoute)> {
        self.http_routes.iter().map(|(n, r)| (n.as_str(), r))
    }

    /// The routes this pass bound — every address the version being lowered
    /// serves. A route the registry holds and this set omits is one the version
    /// stopped serving.
    pub fn routes_bound_this_pass(&self) -> &HashSet<String> {
        &self.http_routes_this_pass
    }

    /// Every bound TCP port's listener.
    pub fn registered_servers(&self) -> impl Iterator<Item = (&u16, &Arc<SharedHttpServer>)> {
        self.shared_servers.iter()
    }

    /// Seed this context with the sources and sinks a program already holds.
    ///
    /// A call naming one of these binds it; a call naming anything else opens
    /// it. Both are allowed in every version — a replacement inherits what the
    /// running program has and may add to it.
    pub fn adopt_sources_and_sinks(
        &mut self,
        sources: impl IntoIterator<Item = (String, Rc<RefCell<dyn DataSourceDomainExtentImpl>>)>,
        routes: impl IntoIterator<Item = (String, LoweredRoute)>,
        servers: impl IntoIterator<Item = (u16, Arc<SharedHttpServer>)>,
    ) {
        self.sources.extend(sources);
        self.http_routes.extend(routes);
        self.shared_servers.extend(servers);
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

    /// Record `expr` as a source construct's image — a single-node leaf
    /// [`LoweringStep`](crate::ccl::provenance::LoweringStep) (`"lower.image"`,
    /// anchored at `span`) appended to the always-on lowering log — and return it,
    /// for chaining at construction sites.
    ///
    /// # The rule for `Nature::Source`
    ///
    /// **`Source` ⟺ the node is the root of a lowered [`Spanned<ChlExpr>`].**
    ///
    /// It is a *positional* fact, so it is decided in exactly one place — the
    /// [`lower_expr`] wrapper, which re-tags every lowered expression's root
    /// (last tag wins, via the fold's re-image path). No arm calls this; an arm
    /// records its own nodes with [`tag_image`](Self::tag_image) for a node that
    /// images source text and [`tag_machinery`](Self::tag_machinery) for
    /// manufactured plumbing, and whichever of them ends up at the root is
    /// re-tagged here.
    ///
    /// The rule is deliberately structural rather than semantic, and the cost is
    /// real: nodes that *are* one-to-one images of something the user wrote but
    /// are not an expression root do not get `Source`. That includes a call's
    /// callee `Var`, each comparison of a chained `a < b < c`, the projection node
    /// of `x[i]` / `x.attr`, and every statement-level image (a `Let` for an
    /// assignment, a `MutWrite` for `x := e`) — statements are not
    /// `Spanned<ChlExpr>`s, so a statement has no `Source` node at all. The
    /// converse also holds: a comprehension's root is a `Cast` wrapper the user
    /// never wrote, and under this rule it *is* `Source`.
    ///
    /// That information is not lost, only moved: every such node carries the
    /// `"lower.image"` label, which is the datum consumers read (see
    /// [`tag_machinery`](Self::tag_machinery) on nature being a coarse
    /// projection). A label-keyed remap can recover a finer taxonomy if one earns
    /// a consumer; the structural rule is what makes "is this `Source`?" answerable
    /// without reading the fold.
    ///
    /// A no-op when no lowering session is installed (the `lower` submodules' unit
    /// tests, which only inspect the tree shape).
    pub(super) fn tag_source(&mut self, expr: Expr, span: Span) -> Expr {
        crate::ccl::provenance::lowering_leaf(expr.node_id(), span, Nature::Source, "lower.image");
        expr
    }

    /// Record `expr` as an **image of source text** at `span` — a node that is a
    /// one-to-one translation of something the user wrote, but is not the root of
    /// a lowered expression and so is not `Nature::Source` under the rule on
    /// [`tag_source`](Self::tag_source).
    ///
    /// It carries the same `"lower.image"` label as a root image, so the two are
    /// distinguishable from plumbing ([`tag_machinery`](Self::tag_machinery)'s
    /// per-rule labels) even though both are `Nature::Machinery`.
    ///
    /// # `label` is per-rule judgment, and carries no cross-site guarantee
    ///
    /// Unlike `Nature::Source`, which is structural and decidable (see
    /// [`tag_source`](Self::tag_source)), the choice between this and
    /// `tag_machinery` is **the lowering author's judgment about their own rule**.
    /// There is no rule to apply, and the codebase does not agree with itself: the
    /// same node kind at the same span role is tagged both ways — an `ExprStmt` at
    /// a statement's span is `"lower.image"` at several sites and
    /// `"lower.stmt_seq"` at nine.
    ///
    /// So the guarantee is deliberately weak, and stating it is the point:
    /// **`"lower.image"` means "the rule that minted this node considered it an
    /// image", nothing more.** No consumer may treat it as a cross-site
    /// classification — not "every image has a 1:1 source construct", not "a
    /// non-image is machinery". A consumer that needs one of those needs a datum
    /// that guarantees it, and none exists yet.
    ///
    /// The whole nature/label taxonomy is **provisional**. It has no consumer that
    /// branches on it today, which is exactly why it has drifted; expect it to
    /// move — most likely to collapse or be recomputed by a label-keyed remap —
    /// once real consumption tells us what distinction is actually load-bearing.
    /// Do not build on the current shape.
    pub(super) fn tag_image(&mut self, expr: Expr, span: Span) -> Expr {
        crate::ccl::provenance::lowering_leaf(
            expr.node_id(),
            span,
            Nature::Machinery,
            "lower.image",
        );
        expr
    }

    /// Record `expr` as **manufactured by lowering** — a single-node leaf
    /// [`LoweringStep`](crate::ccl::provenance::LoweringStep) (`Nature::Machinery`,
    /// `label`, anchored at `span`) appended to the always-on lowering log — and
    /// return it, for chaining at construction sites. The dual of
    /// [`tag_image`](Self::tag_image): a node lowering *manufactured* — encoding
    /// plumbing and faithful expansions alike — rather than one that translates
    /// something the user wrote. `span` is the nearest real source span (the
    /// enclosing statement for statement-level mints, the expression otherwise),
    /// never a fabricated empty one.
    ///
    /// All manufactured nodes get the uniform `Nature::Machinery`: no consumer
    /// behaves differently on the expansion-vs-plumbing bit today, and the
    /// per-site `label` (one label per lowering rule, `lower.<rule>`) is the
    /// primary datum — nature is a coarse projection that a label-keyed remap
    /// can recompute later if a finer taxonomy ever earns a consumer.
    ///
    /// Nature alone therefore does **not** separate manufactured from imaged: an
    /// image that is not an expression root is `Machinery` too (see
    /// [`tag_source`](Self::tag_source) for the rule). The `label` is what
    /// distinguishes them — `"lower.image"` versus a `lower.<rule>` name.
    pub(super) fn tag_machinery(&mut self, expr: Expr, span: Span, label: RewriteLabel) -> Expr {
        crate::ccl::provenance::lowering_leaf(expr.node_id(), span, Nature::Machinery, label);
        expr
    }

    /// Record every node of a finished **refinement predicate** that nothing
    /// else has explained.
    ///
    /// A predicate is assembled from sub-expressions that were lowered — and so
    /// recorded — in the main tree, plus the nodes minted and copied to join them
    /// up. Sealed into a `Refinement` it lives in a *type slot*, outside the
    /// `walk_children` domain, so those assembly nodes have no leaf of their own
    /// and the widened `collect_tree_ids` would report them `Unrecorded`.
    ///
    /// Call this on the predicate **immediately before** handing it to
    /// `ccl_utils::refined_data_fun`, which is the single point a lowering
    /// predicate is born. Nodes already recorded keep their own precise
    /// attribution — see [`lowering_predicate_leaf`].
    ///
    /// [`lowering_predicate_leaf`]: crate::ccl::provenance::lowering_predicate_leaf
    pub(super) fn tag_predicate(&mut self, pred: &Expr, span: Span, label: RewriteLabel) {
        fn go(e: &Expr, span: Span, label: RewriteLabel) {
            crate::ccl::provenance::lowering_predicate_leaf(
                e.node_id(),
                span,
                Nature::Machinery,
                label,
            );
            e.walk_children(|c| go(c, span, label));
        }
        go(pred, span, label);
    }

    /// Mint a fresh `{prefix}_{id}` name from the monotonic synthetic-id
    /// counter, bumping it so every minted name is distinct within a lowering.
    /// The `fresh_*` methods below wrap this, each fixing its own `prefix`.
    fn mint_synthetic_id(&mut self, prefix: &str) -> String {
        let id = self.next_synthetic_id;
        self.next_synthetic_id += 1;
        format!("{prefix}_{id}")
    }

    /// Snapshot the transactional registry on entering a nested binding scope
    /// (a function/lambda body or a nested statement block).
    ///
    /// Within the scope a `Mut(V, Txn)` introduction adds to the set;
    /// [`restore_transactional`] reverts it on exit, giving the name-keyed set
    /// the lexical-scope discipline it otherwise lacks — mirroring how `uniquify`
    /// threads its env stack so a shadowed name reverts to its outer meaning. A
    /// `Mut(V, Txn)` local declared inside a `def` body would otherwise leak into
    /// the transactional set and falsely gate a like-spelled outer local. Needed
    /// because the set is keyed by pre-uniquify base name (a pre-inference
    /// tracker: the `with begin():` block structure it gates is erased by
    /// lowering, so unlike induction mutability it cannot be deferred to the
    /// post-inference `Type::History` check).
    ///
    /// [`restore_transactional`]: Self::restore_transactional
    pub(super) fn snapshot_transactional(&self) -> HashSet<String> {
        self.transactional_vars.clone()
    }

    /// Restore the transactional registry to a [`snapshot_transactional`]
    /// checkpoint, discarding any introductions made in the scope.
    ///
    /// [`snapshot_transactional`]: Self::snapshot_transactional
    pub(super) fn restore_transactional(&mut self, snapshot: HashSet<String>) {
        self.transactional_vars = snapshot;
    }

    /// Declare `name` transactional (introduced by a `Mut(V, Txn)` annotation).
    pub(super) fn register_transactional(&mut self, name: impl Into<String>) {
        self.transactional_vars.insert(name.into());
    }

    /// Whether `name` was declared transactional via a `Mut(V, Txn)` annotation.
    pub(super) fn is_transactional_mut_var(&self, name: &str) -> bool {
        self.transactional_vars.contains(name)
    }

    /// Record that `def name` carries a pass-by-reference `Mut` parameter, so it
    /// is lowered — and applied — curried (see [`mut_param_fns`](Self::mut_param_fns)).
    pub(super) fn register_mut_param_fn(&mut self, name: impl Into<String>) {
        self.mut_param_fns.insert(name.into());
    }

    /// Undo a [`register_mut_param_fn`](Self::register_mut_param_fn): `name`'s
    /// calls lower with the ordinary (tupled) shape. Used when a later `def` in a
    /// block redefines an earlier `Mut`-param `def` with a non-`Mut` signature
    /// (last definition wins, matching CHL's shadowing).
    pub(super) fn unregister_mut_param_fn(&mut self, name: &str) {
        self.mut_param_fns.remove(name);
    }

    /// Whether `name` is a `def` with a pass-by-reference `Mut` parameter (so
    /// its calls must be lowered as curried applications).
    pub(super) fn is_mut_param_fn(&self, name: &str) -> bool {
        self.mut_param_fns.contains(name)
    }

    /// Run `f` with each name in `binders` pushed onto the shadow-depth stack
    /// for the duration — the scope of a binder's body. Balanced: every pushed
    /// name is popped before returning, including when `f` short-circuits with an
    /// error, so the map stays scope-accurate. Used at every binder-introduction
    /// site (loop targets, comprehension generators, lambda/`def` params) so a
    /// local spelled like a transactional mutable variable shadows it inside its body.
    pub(super) fn with_shadowed<T>(
        &mut self,
        binders: impl IntoIterator<Item = String>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let pushed: Vec<String> = binders.into_iter().collect();
        for name in &pushed {
            *self.shadow_depth.entry(name.clone()).or_insert(0) += 1;
        }
        let out = f(self);
        for name in &pushed {
            if let Some(depth) = self.shadow_depth.get_mut(name) {
                *depth -= 1;
                if *depth == 0 {
                    self.shadow_depth.remove(name);
                }
            }
        }
        out
    }

    /// Whether `name` is currently shadowed by an enclosing local binder — so a
    /// reference to it denotes that local, not a like-named transactional mutable variable.
    pub(super) fn is_shadowed(&self, name: &str) -> bool {
        self.shadow_depth.get(name).is_some_and(|&depth| depth > 0)
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
    pub(super) fn fresh_tuple_arg(&mut self) -> String {
        self.mint_synthetic_id(TUPLE_ARG_PREFIX)
    }

    /// Mint a unique `__result_N` name for the defer handle in generator functions.
    ///
    /// Counter-minted to avoid collisions when user code contains a binding
    /// named `__result` inside the same generator body.
    pub(super) fn fresh_result_name(&mut self) -> String {
        self.mint_synthetic_id("__result")
    }

    /// Mint a unique `__txn_item_N` name for a standalone transaction's synthetic
    /// singleton-source binder. The item is never read (the block reads only
    /// stores), so the name only needs to be collision-free.
    pub(super) fn fresh_txn_item(&mut self) -> String {
        self.mint_synthetic_id("__txn_item")
    }

    /// Mint a unique `__match_payload_N` name for a binder-less `case tag:` arm.
    ///
    /// A [`crate::ccl::expr::Pattern`] always names the payload it narrows, so an
    /// arm that declines to bind still needs *a* name; minting one the user
    /// cannot spell is what makes "does not bind" and "binds something
    /// unreadable" the same thing downstream, so variant elimination needs no
    /// separate no-binder case.
    pub(super) fn fresh_ignored_payload(&mut self) -> String {
        self.mint_synthetic_id("__match_payload")
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

/// Lower a single CHL expression to a CCL expression, tagging the root of the
/// lowered subtree with the source span it came from.
///
/// The recursion proper lives in [`lower_expr_inner`]; this thin wrapper is the
/// **sole** emitter of `Nature::Source`, and so the one place the rule is applied:
/// `Source` ⟺ the node is the root of a lowered `Spanned<ChlExpr>`. It re-tags the
/// returned node via [`LoweringContext::tag_source`], overwriting any interim tag
/// an arm put on its own root (last tag wins, through the fold's re-image path).
/// The rule is positional, so no lowering arm ever decides it — see
/// [`LoweringContext::tag_source`] for the rule and its costs.
///
/// Interior nodes an arm builds are each tagged at their mint site with
/// [`LoweringContext::tag_image`] for a node that images source text or
/// [`LoweringContext::tag_machinery`] for manufactured plumbing. **That choice is
/// per-rule judgment, not a rule** — `tag_image`'s docs state what it does and
/// does not guarantee. Whichever of them lands at the root is re-tagged here.
/// [`fold_lowering`](crate::ccl::provenance::fold_lowering)'s leak taxonomy
/// enforces full coverage of the lowered tree either way.
pub fn lower_expr(
    expr: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let lowered = lower_expr_inner(expr, ctx)?;
    Ok(ctx.tag_source(lowered, expr.span))
}

fn lower_expr_inner(
    expr: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    match &expr.node {
        ChlExpr::Lit(lit) => lower_constant(lit),
        ChlExpr::Name(id) => {
            let name = id.as_str();
            // Inside a refinement predicate (`{T where p}`), `_` is the anonymous
            // subject — the value being refined — which is the reserved binder
            // `__elem` (`docs/chl-spec.md`, "6.4 Refinement syntax").
            if ctx.in_refinement_predicate && name == "_" {
                return Ok(Expr::var(crate::ccl::Name::elem()));
            }
            // A transactional mutable variable may be read only inside a `with begin():`
            // block, which pins a snapshot-consistent view (all txn reads in one
            // block observe one commit snapshot). Inside a transaction
            // (`in_tx_body`) a bare read is that snapshot and is fine; outside
            // one it is rejected with a hint to wrap the read in a block.
            //
            // `is_shadowed` guards the base-name registry against a false match:
            // a loop/comprehension/lambda binder spelled like a mutable variable (`for
            // x in xs: … x …`) is a genuine local, not the mutable variable, so
            // it is not gated (its α-unique binder wins).
            if ctx.is_transactional_mut_var(name) && !ctx.in_tx_body && !ctx.is_shadowed(name) {
                return Err(LoweringError::unsupported(
                    expr.span,
                    format!(
                        "read transactional variable `{name}` inside a `with begin():` block (or \
                         `await_final({name})` for its final committed value)"
                    ),
                ));
            }
            Ok(Expr::var(name.to_string()))
        }
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
        // `()` is the **unit value**, and CHL's only spelling for it
        // (`docs/chl-spec.md`, "6.6 The empty product is unit"). It lowers to
        // the CCL unit literal rather than a zero-element `Tuple` node, so the
        // one unit value has one term representation, just as it has one type. Collapsed here, at the surface boundary, rather
        // than in `Expr::tuple`: internal passes build tuples from
        // variable-length collections and a silent arity-0 reinterpretation
        // there would reach code this decision is not about.
        ChlExpr::Tuple(elts) if elts.is_empty() => Ok(Expr::lit(Lit::Unit)),
        ChlExpr::Tuple(elts) => {
            let items: Result<Vec<_>, _> = elts.iter().map(|e| lower_expr(e, ctx)).collect();
            Ok(Expr::tuple(items?))
        }
        ChlExpr::Subscript { target, index } => lower_subscript(target, index, ctx),
        // Record value `(name=expr, ...)`. Lowered to a `Record` constructor:
        // `(x=1, y="foo")` becomes `Record([("x", Lit(1)), ("y", Lit("foo"))])`.
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
        // A colon-free brace group `{T, U}` is structural *type* syntax; it
        // has no term-level value. (It is accepted in annotation position as a
        // tuple type — see `lower_type_annotation`.)
        ChlExpr::BraceGroup(_) => Err(LoweringError::unsupported(
            expr.span,
            "`{…}` is type syntax (a tuple type `{T, U}`); \
             use `[…]` for a collection or `(…)` for a tuple value",
        )),
        // A brace record `{name: T}` is structural *type* syntax (a record
        // type); a record *value* is written with parentheses. (Accepted in
        // annotation position — see `lower_type_annotation`.)
        ChlExpr::BraceRecord(_) => Err(LoweringError::unsupported(
            expr.span,
            "`{…}` is type syntax (a record type `{name: T}`); \
             a record value is written `(name=value)`",
        )),
        // A refinement `{T where p}` is structural *type* syntax; it names a
        // type, not a value. (Accepted in annotation position — see
        // `lower_type_annotation`.)
        ChlExpr::BraceRefinement { .. } => Err(LoweringError::unsupported(
            expr.span,
            "`{T where p}` is a refinement *type*; it is written in annotation \
             position, not as a value",
        )),
        // A function type `T => U` is structural *type* syntax; it names a type,
        // not a value. (Accepted in annotation position — see `lower_type_expr`.)
        ChlExpr::FunctionType { .. } => Err(LoweringError::unsupported(
            expr.span,
            "`T => U` is a function *type*; it is written in annotation \
             position, not as a value",
        )),
        // Attribute access `target.attr` → `Apply(target, Proj(k))`. The `Proj` images
        // the `.attr` access the user wrote.
        //
        // This is the one place a projection key's two spellings are resolved: digits
        // are a tuple **position**, anything else a record field **name**. The two are
        // disjoint because an identifier cannot begin with a digit, so `starts_with` a
        // digit *is* the discriminator — no guessing and no ambiguity.
        ChlExpr::Attribute {
            target,
            attr,
            attr_span,
        } => {
            let key = if attr.starts_with(|c: char| c.is_ascii_digit()) {
                // Only magnitude can fail here: the parser admits an integer literal,
                // so the digits are a non-negative number, but not necessarily one a
                // `usize` position can hold.
                let index: usize = attr.parse().map_err(|_| {
                    LoweringError::unsupported(
                        *attr_span,
                        format!("tuple position `.{attr}` is too large to be an index"),
                    )
                })?;
                Expr::proj_index(index)
            } else {
                Expr::proj_field(attr.as_str())
            };
            let target_expr = lower_expr(target, ctx)?;
            let proj = ctx.tag_image(key, expr.span);
            Ok(Expr::apply(target_expr, proj))
        }
        // Variant constructor `` `tag(payload) `` → `VariantCtor`. The bare form
        // `` `tag `` carries a `Unit` payload: a tag that names no payload still
        // injects *something*, and `Unit` is the value that carries no
        // information. So there is one constructor shape, not a nullary/unary
        // pair. The `VariantCtor` itself is this expression's root, so
        // `lower_expr` re-tags it `Source`; only the synthesized payload is
        // manufactured and tagged here.
        ChlExpr::VariantCtor { tag, payload, .. } => {
            let payload = match payload {
                Some(ChlVariantPayload::Term(p)) => lower_expr(p, ctx)?,
                // Braces are a *type*'s field list; in a term the payload is
                // the value itself, in parens.
                Some(ChlVariantPayload::Fields(_)) => {
                    return Err(LoweringError::unsupported(
                        expr.span,
                        format!(
                            "`{{…}}` after a tag is a type's field list; a constructor's \
                             payload is a value in parens: `` `{tag}(𝑒) ``"
                        ),
                    ));
                }
                None => {
                    ctx.tag_machinery(Expr::lit(Lit::Unit), expr.span, "lower.variant_ctor_unit")
                }
            };
            Ok(Expr::variant_ctor(tag.as_str(), payload))
        }
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
            // The ternary has no written else-guard; its always-true guard is
            // manufactured encoding.
            let else_guard =
                ctx.tag_machinery(Expr::lit(Lit::Bool(true)), expr.span, "lower.ternary_else");
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
                        guard: else_guard,
                        body: false_arm,
                    },
                ],
            }))
        }
        // `target << value` — feed into a deferred output.
        ChlExpr::Feed { target, value } => lower_feed(target, value, ctx),
        // The one-line `match` (`match v { case `a: … }`), the only block value
        // that reaches an expression position. Every block *statement* value is
        // an assignment's right-hand side and routes through
        // `lower_assigned_value`, which carries the scope its position binds.
        //
        // The empty scope passed here is the one-line form's own: its arms are
        // expressions (`docs/chl-spec.md`, "The one-line form"), so no
        // statement — and so no name — can be bound inside it for the scope to
        // disambiguate.
        ChlExpr::Block(stmt) => lower_block_value(stmt, &[], &HashSet::new(), ctx),
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
/// sink-binding contract; each field is the name that [`crate::ccl::channelize`]
/// resolves to the computed response morphism.  After `channelize` removes
/// all `Feed` nodes, `simplify` drops the `ExprStmt`, leaving a clean
/// `Let* Record{…}` shape for `compile_program`.
pub fn lower_stmts(stmts: &[Spanned<ChlStmt>], ctx: &mut LoweringContext) -> LoweringResult {
    let mut errors: Vec<LoweringError> = Vec::new();
    let value = lower_stmts_recovering(stmts, ctx, &mut errors);
    LoweringResult { value, errors }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    //! Shared test fixtures for the `lower` submodules' inline `mod tests`.
    use std::{cell::RefCell, rc::Rc};

    use crate::{
        ccl::{
            Type,
            lower::{LoweringContext, LoweringError, lower_stmts},
        },
        chl_parser::ast::{Expr as ChlExpr, Spanned, Stmt as ChlStmt},
        interpreter::DataSourceDomainExtentImpl,
    };

    /// Parse a CHL expression and return the AST node.
    pub(crate) fn parse_expr(code: &str) -> Spanned<ChlExpr> {
        crate::chl_parser::parse_expression(code)
            .into_result()
            .expect("Failed to parse expression")
    }

    /// Create a minimal registered source for tests that only care about name recognition.
    pub(crate) fn stub_source(name: &str) -> Rc<RefCell<dyn DataSourceDomainExtentImpl>> {
        use crate::interpreter::{BaseType, Extent, TestDataSource};
        Rc::new(RefCell::new(TestDataSource::new(
            name,
            Type::Base(BaseType::String),
            Extent::Base(BaseType::String),
        )))
    }

    /// Parse a CHL module and return the statement list.
    pub(crate) fn parse_module(code: &str) -> Vec<Spanned<ChlStmt>> {
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
    pub(crate) fn expect_one_lowering_error(stmts: &[Spanned<ChlStmt>]) -> LoweringError {
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
}

#[cfg(test)]
mod tests {
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
}

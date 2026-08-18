// ---------------------------------------------------------------------------
// Context object for state shared across all phases of compilation like
// builtins
// ---------------------------------------------------------------------------

use std::{cell::RefCell, rc::Rc};

use crate::chl_parser;
use crate::chl_parser::parser::ParseError;
use log::debug;

use crate::{
    ccl::{
        Expr, channelize,
        infer::{
            InferError, TypeInferenceContext, check_mut_discipline, check_mut_write_targets,
            check_pre_desugar, infer, typecheck,
        },
        inline, lambda_elim,
        lineage::{Leak, RecorderSession, SourceProjection, collapse_lowering},
        lower::{LoweringContext, LoweringError, lower_stmts},
        mut_elim, planning,
        provenance::NodeId,
        symbolic::{symbolic, symbolic_typed},
        transact_phase, uniquify,
    },
    interpreter::{
        Consumer, DataSourceDomainExtentImpl, Scheduler, StdinDataSource,
        operator_conversion::{
            ConversionError, OpConversionContext, convert_record_fields_to_operators,
            convert_to_operators,
        },
        sinks::{DoneNotifier, SinkConsumer},
        tile_operators::{TileOperator, TileProducer},
    },
    pretty_graph::{VizOptions, pretty_tile_producer_with},
};

// ---------------------------------------------------------------------------
// CompileError
// ---------------------------------------------------------------------------

/// One error a user can hit when compiling a CHL program.
///
/// Variants are tagged by the pipeline stage that produced them — parsing,
/// lowering (unsupported construct), type inference, lambda elimination,
/// defer/feed resolution, or operator-graph conversion. Stage-internal
/// consistency checks (`typecheck`, `check_fully_typed` between passes,
/// lambda-elim of a typed tree) are invariants — they panic with `.expect`
/// because firing them indicates a compiler bug, not user error.
///
/// [`compile_program`] returns `Result<_, Vec<CompileError>>`: when multiple
/// stages produce errors (e.g. parse errors plus a lowering error in a
/// statement unaffected by the parse hole), every error is returned in one
/// pass instead of giving up at the first failing stage. Each entry is
/// single-stage; the parser's multi-error output is flattened into one
/// [`CompileError::Parse`] per [`ParseError`].
///
/// Use [`eprint_errors`] for source-context rendering: parse, lowering, and
/// span-carrying inference errors get ariadne reports with underlines; the
/// remaining variants render as plain `error: …` lines. Lambda-elim/conversion
/// spans remain future work; the enum is shaped so they migrate without
/// changing the list-of-errors return contract.
#[derive(Debug)]
pub enum CompileError {
    /// The parser rejected one token / token sequence.
    Parse(ParseError),
    /// The (parseable) AST uses a construct the lowering pass does not
    /// support yet.
    Lower(LoweringError),
    /// Defer/Feed/Define desugaring rejected the program (e.g. a defer
    /// binding with no feeds, mixed `<<`/`<<=` on the same handle, or a
    /// `<<=` inside a non-top-level scope).
    ///
    /// Desugaring runs *after* inference (so type errors report against
    /// the user's program shape); a program with both a type error and a
    /// structural defer error therefore surfaces only the type error
    /// first.
    DesugarDefers(channelize::DeferError),
    /// Type inference rejected one expression.
    ///
    /// `span` is the offending source range, resolved at the `compile_program`
    /// boundary via the `lowering_projection` one-hop lookup. `None` when no
    /// precise node was known (coalesce/scope errors, or a caller without the table) —
    /// the error then renders as a plain `error: …` line instead of an ariadne
    /// report with source context.
    Infer {
        /// The underlying inference error (its `Debug` impl is the human message).
        error: InferError,
        /// The resolved source span, when known.
        span: Option<chl_parser::ast::Span>,
    },
    /// Lambda elimination failed.
    LambdaElim(lambda_elim::LambdaElimError),
    /// Operator-graph conversion failed.
    Conversion(ConversionError),
    /// A post-inference phase rejected the program for a semantic reason that
    /// only becomes visible after inlining / type inference — e.g. a nested
    /// transaction reaching a `with begin():` block via a function call, or an
    /// induction-only / guarded-write transaction block. These run on a
    /// lambda-free / inlined tree whose nodes carry no source span, so they
    /// render as a plain `error: …` line rather than an ariadne report.
    Unsupported(String),
}

impl CompileError {
    /// Render this single error as a plain-ASCII string with source-code context.
    ///
    /// - [`CompileError::Parse`], [`CompileError::Lower`], and a
    ///   span-carrying [`CompileError::Infer`] are rendered via ariadne with
    ///   colour disabled (gutter, source line, underlines, labels — all in
    ///   Unicode box-drawing). Suitable for panic messages, log files,
    ///   snapshots, or piping through grep.
    /// - The remaining variants (and a spanless `Infer`) render as plain
    ///   `error: …` lines.
    ///
    /// To render a whole [`Vec<CompileError>`] from `compile_program`, use
    /// [`render_errors`].
    pub fn render(&self, src_name: &str, src: &str) -> String {
        let mut buf: Vec<u8> = Vec::new();
        match self {
            CompileError::Parse(e) => {
                e.to_report_with_config(src_name, ariadne::Config::default().with_color(false))
                    .write((src_name, ariadne::Source::from(src)), &mut buf)
                    .expect("ariadne write should not fail on Vec<u8>");
            }
            CompileError::Lower(e) => {
                e.to_report_with_config(src_name, ariadne::Config::default().with_color(false))
                    .write((src_name, ariadne::Source::from(src)), &mut buf)
                    .expect("ariadne write should not fail on Vec<u8>");
            }
            CompileError::DesugarDefers(e) => {
                buf.extend_from_slice(format!("error: deferred collection: {e}\n").as_bytes());
            }
            CompileError::Infer {
                error,
                span: Some(span),
            } => {
                infer_report(
                    error,
                    *span,
                    src_name,
                    ariadne::Config::default().with_color(false),
                )
                .write((src_name, ariadne::Source::from(src)), &mut buf)
                .expect("ariadne write should not fail on Vec<u8>");
            }
            CompileError::Infer { error, span: None } => {
                buf.extend_from_slice(format!("error: type inference: {error:?}\n").as_bytes());
            }
            CompileError::LambdaElim(e) => {
                buf.extend_from_slice(format!("error: lambda elimination: {e:?}\n").as_bytes());
            }
            CompileError::Conversion(e) => {
                buf.extend_from_slice(
                    format!("error: operator-graph conversion: {e:?}\n").as_bytes(),
                );
            }
            CompileError::Unsupported(msg) => {
                buf.extend_from_slice(format!("error: {msg}\n").as_bytes());
            }
        }
        String::from_utf8_lossy(&buf).into_owned()
    }

    /// Print this single error to stderr.
    ///
    /// [`CompileError::Parse`] and [`CompileError::Lower`] use ariadne's
    /// coloured `eprint`; the other variants emit a plain `error: …` line
    /// via [`Self::render`].
    pub fn eprint(&self, src_name: &str, src: &str) {
        match self {
            CompileError::Parse(e) => {
                e.to_report(src_name)
                    .eprint((src_name, ariadne::Source::from(src)))
                    .expect("ariadne eprint should not fail on stderr");
            }
            CompileError::Lower(e) => {
                e.to_report(src_name)
                    .eprint((src_name, ariadne::Source::from(src)))
                    .expect("ariadne eprint should not fail on stderr");
            }
            CompileError::Infer {
                error,
                span: Some(span),
            } => {
                infer_report(error, *span, src_name, ariadne::Config::default())
                    .eprint((src_name, ariadne::Source::from(src)))
                    .expect("ariadne eprint should not fail on stderr");
            }
            other => eprint!("{}", other.render(src_name, src)),
        }
    }
}

/// Build an ariadne report for an inference error pinned to a source span.
///
/// Mirrors the parse/lower report builders: the `Debug` impl of [`InferError`]
/// is already the human-readable message, used as both the report title and the
/// label. Colour is governed by `config` (off for [`CompileError::render`], on
/// for [`CompileError::eprint`]), matching the other arms' conventions.
fn infer_report<'a>(
    error: &InferError,
    span: chl_parser::ast::Span,
    src_name: &'a str,
    config: ariadne::Config,
) -> ariadne::Report<'a, (&'a str, std::ops::Range<usize>)> {
    use ariadne::{Color, Label, Report, ReportKind};
    let message = format!("{error:?}");
    Report::build(ReportKind::Error, src_name, span.start)
        .with_config(config)
        .with_message("type inference error")
        .with_label(
            Label::new((src_name, span.into()))
                .with_message(message)
                .with_color(Color::Red),
        )
        .finish()
}

/// Render every error in `errs` and concatenate the output.
pub fn render_errors(errs: &[CompileError], src_name: &str, src: &str) -> String {
    let mut s = String::new();
    for e in errs {
        s.push_str(&e.render(src_name, src));
    }
    s
}

/// Print every error in `errs` to stderr (coloured ariadne output for parse
/// errors, plain `error: …` lines for the rest).
pub fn eprint_errors(errs: &[CompileError], src_name: &str, src: &str) {
    for e in errs {
        e.eprint(src_name, src);
    }
}

impl From<LoweringError> for CompileError {
    fn from(e: LoweringError) -> Self {
        Self::Lower(e)
    }
}

impl From<lambda_elim::LambdaElimError> for CompileError {
    fn from(e: lambda_elim::LambdaElimError) -> Self {
        Self::LambdaElim(e)
    }
}

impl From<channelize::DeferError> for CompileError {
    fn from(e: channelize::DeferError) -> Self {
        Self::DesugarDefers(e)
    }
}

impl From<ConversionError> for CompileError {
    fn from(e: ConversionError) -> Self {
        Self::Conversion(e)
    }
}

/// Lift a stage-specific error (or `Vec` of them) into the
/// [`Vec<CompileError>`] channel used by [`compile_program`].
///
/// The orphan rule prevents `From<X> for Vec<CompileError>` impls, so we go
/// through a trait. Single-error stages produce a one-element list; the
/// inference stage flattens its `Vec<InferError>` into one `CompileError`
/// per inference error.
pub trait IntoCompileErrors {
    fn into_compile_errors(self) -> Vec<CompileError>;
}

impl IntoCompileErrors for Vec<InferError> {
    fn into_compile_errors(self) -> Vec<CompileError> {
        // Fallback for callers without the `lowering_projection` (i.e. not
        // `compile_program`): no span resolution, so `span: None`. The
        // `compile_program` path resolves spans explicitly and constructs the
        // `Infer` variant itself rather than going through `.errs()`.
        self.into_iter()
            .map(|error| CompileError::Infer { error, span: None })
            .collect()
    }
}

impl IntoCompileErrors for lambda_elim::LambdaElimError {
    fn into_compile_errors(self) -> Vec<CompileError> {
        vec![CompileError::LambdaElim(self)]
    }
}

impl IntoCompileErrors for channelize::DeferError {
    fn into_compile_errors(self) -> Vec<CompileError> {
        vec![CompileError::DesugarDefers(self)]
    }
}

impl IntoCompileErrors for ConversionError {
    fn into_compile_errors(self) -> Vec<CompileError> {
        vec![CompileError::Conversion(self)]
    }
}

/// Extension on `Result` whose `Err` knows how to become a
/// `Vec<CompileError>`. Lets the rest of the compile pipeline write
/// `stage(...).errs()?` instead of an inline `.map_err(...)` per call site.
pub trait CompileErrsExt<T> {
    fn errs(self) -> Result<T, Vec<CompileError>>;
}

impl<T, E: IntoCompileErrors> CompileErrsExt<T> for Result<T, E> {
    fn errs(self) -> Result<T, Vec<CompileError>> {
        self.map_err(IntoCompileErrors::into_compile_errors)
    }
}

/// Extension trait for `Result<T, Vec<CompileError>>`.
///
/// Lets test code (or any non-prod caller) collapse the
/// `compile_program` result to its `T` while still getting ariadne-rendered
/// error output on failure. Use sparingly outside tests — production code
/// should match on the error list and decide what to do.
///
/// ```ignore
/// use cambra::ccl::context::{compile_program, CompileResultExt};
/// let compiled = compile_program(&mut ctx, code, consumer)
///     .unwrap_or_render("<test>", code);
/// ```
pub trait CompileResultExt<T> {
    /// Return `Ok` payload, or render every error via [`render_errors`] and
    /// panic with the rendering bundled into the panic message (so the
    /// output is captured by cargo test alongside the failing test).
    fn unwrap_or_render(self, src_name: &str, src: &str) -> T;
}

impl<T> CompileResultExt<T> for Result<T, Vec<CompileError>> {
    fn unwrap_or_render(self, src_name: &str, src: &str) -> T {
        self.unwrap_or_else(|errs| {
            // Bundle the rendered output into the panic message rather than
            // writing to stderr directly: ariadne's `eprint` writes raw to
            // file-descriptor 2, which bypasses cargo test's per-test output
            // capture, so the errors would show up *outside* the failing
            // test's output block. Putting them in the panic message means
            // cargo test groups them with the test's `---- TEST stdout ----`
            // section as expected.
            panic!(
                "compilation failed:\n{}",
                render_errors(&errs, src_name, src)
            )
        })
    }
}

/// Bundles the per-stage registries needed to thread externally-managed data
/// sources through the full CCL pipeline (lowering → type inference → compilation).
pub struct GlobalContext {
    /// Lowering-stage registry: maps source names to their implementations.
    lowering: LoweringContext,
    /// Inference-stage registry: supplies the CCL function type for each source.
    inference: TypeInferenceContext,
    /// Operator Conversion context.
    conversion: OpConversionContext,
    /// Scheduler for triggering notifications.
    scheduler: Scheduler,
}

impl GlobalContext {
    /// Create a new context with stdin pre-registered in the lowering stage.
    ///
    /// Inference and operator-conversion registration for stdin (and all other
    /// sources) happens in [`compile_program`] after lowering completes via
    /// [`LoweringContext::take_sources`].
    pub fn new() -> Self {
        let mut result = Self {
            lowering: LoweringContext::default(),
            inference: TypeInferenceContext::new(),
            conversion: OpConversionContext::new(),
            scheduler: Scheduler::new(),
        };
        let stdin = Rc::new(RefCell::new(StdinDataSource::new()));
        result.register_source(stdin);
        result
    }

    /// Returns the context for lowering
    pub fn lowering_ctx(&mut self) -> &mut LoweringContext {
        &mut self.lowering
    }

    /// Returns the context for type inference
    pub fn inference_ctx(&mut self) -> &mut TypeInferenceContext {
        &mut self.inference
    }

    /// Returns the context for operator conversion
    pub fn conversion_ctx(&mut self) -> &mut OpConversionContext {
        &mut self.conversion
    }

    pub fn scheduler(&mut self) -> &mut Scheduler {
        &mut self.scheduler
    }

    /// Pre-register a data source so that `name()` is a valid call during lowering.
    ///
    /// This adds the source to the lowering-stage registry only.  Inference and
    /// operator-conversion registration happen later in [`compile_program`] when
    /// [`LoweringContext::take_sources`] is called and every accumulated source
    /// (pre-registered and discovered) is registered in one uniform pass.
    pub fn register_source(&mut self, source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>) {
        let name = source.borrow().get_id().to_string();
        self.lowering.register_source(name, source);
    }
}

impl Default for GlobalContext {
    fn default() -> Self {
        Self::new()
    }
}

/// The compiled output for one field of the program's trailing record.
///
/// A program's trailing record always has zero or one `main` fields plus zero
/// or more sink fields.  The `main` field carries the program's primary output
/// (the value of its trailing expression for pure programs); sink fields
/// correspond to externally-managed [`DataSink`](crate::interpreter::DataSink)s
/// such as `http_serve`'s response channel.
pub struct CompiledOutput {
    /// Field name from the trailing record.  `"main"` for the program's
    /// primary output; otherwise the name of a registered sink binding.
    pub name: String,
    /// The compiled tile operator producing this field's stream.
    pub op: Box<dyn TileOperator>,
    /// `Some` for `main` outputs — the producer the caller drives via
    /// [`TileProducer::get`] to consume primary-output values.  `None` for
    /// sink outputs, whose producer is owned by the [`SinkConsumer`].
    pub producer: Option<Box<dyn TileProducer>>,
    /// `Some` for sink outputs — the [`SinkConsumer`] subscribed to the
    /// operator that dispatches to the registered [`crate::interpreter::DataSink`].
    pub sink_consumer: Option<Rc<RefCell<SinkConsumer>>>,
}

impl CompiledOutput {
    /// Returns `true` if this is the program's `main` (primary) output.
    pub fn is_main(&self) -> bool {
        self.name == "main"
    }
}

/// A compiled CHL program ready for the scheduler to drive.
///
/// Holds the join-planned AST, one [`CompiledOutput`] per trailing-record
/// field, and a `done` receiver that fires when every sink output has reached
/// a terminal tile.  Programs without sinks get an immediately-dropped sender,
/// so `done.try_recv()` never returns `Ok`; pure programs are driven entirely
/// by the `main` output's producer.
pub struct CompiledProgram {
    /// Join-planned CCL expression.  For sink programs this is `Let* Record{…}`;
    /// for pure programs it is the bare lowered expression at the tail of the
    /// `Let*` chain (no synthetic `Record` wrapper).
    pub ast: Expr,
    /// One subscribed output per program output (`main` for pure programs;
    /// one entry per record field for sink programs, in declaration order).
    pub outputs: Vec<CompiledOutput>,
    /// Fires once every sink consumer has received a terminal tile.  For pure
    /// programs the sender is dropped immediately, so `try_recv` never returns
    /// `Ok` — pure programs are driven entirely by the `main` producer.
    pub done: std::sync::mpsc::Receiver<()>,
    /// The always-on **lowering projection**: **every** lowered node's
    /// [`NodeId`](crate::ccl::provenance::NodeId) mapped to the
    /// [`SourceAttribution`](crate::ccl::lineage::SourceAttribution) folded from
    /// lowering's [`LoweringLog`](crate::ccl::lineage::LoweringLog). Every entry
    /// is `via: Lower`; the tag is one of **three** shapes, not two:
    ///
    /// - `Nature::Source` + `"lower.image"` — the root of a lowered
    ///   `Spanned<ChlExpr>`. Structural and decidable; emitted only by
    ///   `lower_expr` (see `LoweringContext::tag_source`).
    /// - `Nature::Machinery` + `"lower.image"` — **the common case**: a node the
    ///   minting rule considered an image of source text but which is not an
    ///   expression root (a callee `Var`, a chained comparison, a statement-level
    ///   image).
    /// - `Nature::Machinery` + `"lower.<rule>"` — lowering-manufactured plumbing.
    ///
    /// The `"lower.image"` label carries no cross-site guarantee — it is per-rule
    /// judgment, and the taxonomy is provisional (`LoweringContext::tag_image`).
    /// Coverage, by contrast, is guaranteed: the whole `walk_children` domain is
    /// present, since an unrecorded mint surfaces as `Leak::Unexplained` at the
    /// fold. Produced by
    /// [`collapse_lowering`](crate::ccl::lineage::collapse_lowering) at the
    /// lowering boundary, never mutated incrementally. It is always-on and the
    /// release `InferError` diagnostics read it one-hop (spans of the blame node).
    pub lowering_projection: SourceProjection,
    /// The **pre-inference** IR snapshot — the inspector's upstream (source-shaped,
    /// pre-monomorphization) pane, captured right after `uniquify` and before
    /// `infer`.
    ///
    /// It is the same tree `infer` consumes: source-shaped (lambdas intact,
    /// Defer/Feed/Define still present) and **untyped** — every node's `ty` is a
    /// `Hole`/`Infer`. The inspector renders those holes; the resolved downstream
    /// type is stitched in from [`post_inference_ir`](Self::post_inference_ir) via
    /// shared/remapped `NodeId`s.
    ///
    /// Monomorphization runs *inside* `infer`, freshening cloned ids, so this
    /// snapshot holds the pre-mono **originals**; every ordinary node keeps its
    /// id identical across the pair. Its ids resolve against the
    /// [`lowering_projection`](Self::lowering_projection) (they are the pre-mono originals, keyed by lowering's
    /// directly-lowered attributions).
    pub pre_inference_ir: Expr,
    /// The post-inference IR snapshot — the program inspector's anchor.
    ///
    /// This is `expr` captured **right after `infer`/`typecheck` and before
    /// `inline::inline_capability_lambdas` consumes it**: fully typed, but
    /// still *source-shaped* (lambdas intact, not yet point-free — `inline`,
    /// `lambda_elim`, and `planning` have not run).
    ///
    /// Distinct from [`ast`](Self::ast), which holds `join_planned` (the
    /// *post-planning* tree): `lambda_elim`/`planning` re-mint every `NodeId`,
    /// so `ast`'s ids don't resolve against the lowering projection, and it is
    /// execution-shaped (point-free, fused) — the wrong tree for a source-level
    /// view. The inspector anchors here instead.
    pub post_inference_ir: Expr,
    /// The post-desugar IR snapshot — the inspector's **downstream** pane, one
    /// pipeline stage *below* [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// This is `expr` captured **right after `channelize`** (which now runs
    /// after `infer`/`inline`/`transact`/`letrec`): fully typed and structurally
    /// final for the source view — no Defer/Feed/Define nodes remain, and the
    /// channelization artifacts (`Compose` wrapper chains, `Copair`
    /// fan-ins) are present. Because monomorphization ran earlier (inside
    /// `infer`), this tree is post-mono like [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// Every id preserved through inline/transact/letrec/desugar is shared with
    /// [`post_inference_ir`](Self::post_inference_ir).
    pub post_desugar_ir: Expr,
    /// The parsed CHL surface AST — the source-of-truth for source-level
    /// (lexical) inspector queries.
    ///
    /// This is the [`Module`](crate::chl_parser::ast::Module) lowering consumed,
    /// retained verbatim. It is the anchor for *source-language* questions —
    /// name resolution (`goto-definition`, the binder half of `scope-at`) —
    /// answered by the inspector's name-binder index.
    ///
    /// It is deliberately **distinct from [`post_inference_ir`](Self::post_inference_ir)**
    /// (the typed IR): lowering destroys some source variables before any IR
    /// node exists — notably `uncurry_params` rewrites multi-param references
    /// `Var(x)` to `__arg_tuple_N ▷ .i` *before* uniquify, so the lowered/typed
    /// tree structurally cannot resolve a multi-param `def`/`lambda` parameter
    /// back to its binder. The surface AST still has `x`/`y` with their
    /// `Param.name_span`, so lexical resolution over *this* is lossless.
    pub source_ast: chl_parser::ast::Module,
    /// The original program source text, retained verbatim.
    ///
    /// Inspector queries need the source string to produce snippets (`hover`'s
    /// `snippet` = `source[span]`) and to serve the snapshot wire's
    /// `source.text`. Every
    /// span-keyed projection above (the [`lowering_projection`](Self::lowering_projection), the surface AST's
    /// spans) is a byte offset *into this string*, so retaining it is what makes
    /// those offsets resolvable to text. Cheap (one program's source).
    pub source: String,
}

impl CompiledProgram {
    /// Returns a reference to the `main` output, if any.
    pub fn main(&self) -> Option<&CompiledOutput> {
        self.outputs.iter().find(|o| o.is_main())
    }

    /// Returns a mutable reference to the `main` output, if any.
    pub fn main_mut(&mut self) -> Option<&mut CompiledOutput> {
        self.outputs.iter_mut().find(|o| o.is_main())
    }

    /// Iterates over the program's sink outputs (every output except `main`).
    pub fn sinks(&self) -> impl Iterator<Item = &CompiledOutput> {
        self.outputs.iter().filter(|o| !o.is_main())
    }
}

/// Every main-tree node id reachable in `expr` (the `walk_children` node set,
/// refinement-predicate interiors excluded — the domain the lineage steps and
/// the pane projections reason about).
pub(crate) fn collect_tree_ids(expr: &Expr) -> std::collections::HashSet<NodeId> {
    fn go(e: &Expr, acc: &mut std::collections::HashSet<NodeId>) {
        acc.insert(e.node_id());
        e.walk_children(|c| go(c, acc));
    }
    let mut acc = std::collections::HashSet::new();
    go(expr, &mut acc);
    acc
}

/// The lowering-boundary leak gate: the lowering log records every mint and
/// copy at its site, so [`collapse_lowering`]'s fold must explain every
/// output-tree node with **no** leak of any class — an `Unexplained` (an
/// unrecorded lowering mint) is a recording bug, not tolerated residue.
/// Debug/test only, single code path (`cfg!`, not `#[cfg]`).
fn assert_leaks_clean(leaks: &[Leak], boundary: &str) {
    if !cfg!(any(debug_assertions, test)) {
        return;
    }
    assert!(
        leaks.is_empty(),
        "lineage leak at the fully-recorded {boundary} boundary (expected none): {leaks:?}"
    );
}

/// Every duplicated [`NodeId`] over the **main tree** — the `walk_children`
/// node-set, refinement predicates excluded (matching inline's blind spot, so the
/// check does not false-fire there). Returns `(id, node kind)` for each
/// occurrence *beyond the first*.
fn duplicate_node_ids(expr: &Expr) -> Vec<(NodeId, &'static str)> {
    fn walk(
        e: &Expr,
        seen: &mut std::collections::HashSet<NodeId>,
        dups: &mut Vec<(NodeId, &'static str)>,
    ) {
        if !seen.insert(e.node_id()) {
            dups.push((e.node_id(), e.node.kind_name()));
        }
        e.walk_children(|c| walk(c, seen, dups));
    }
    let mut seen = std::collections::HashSet::new();
    let mut dups = Vec::new();
    walk(expr, &mut seen, &mut dups);
    dups
}

/// Pipeline-wide id-uniqueness tripwire: panic if `expr` carries a duplicated
/// [`NodeId`], naming the `boundary` and the offending id(s) + node kinds.
///
/// Uniqueness within a tree is what makes a `NodeId` an *identity*: the lineage
/// map is keyed by id, so two live nodes sharing one id make their attributions
/// and edges indistinguishable. The failure mode this catches is a clone that
/// forgot to freshen, or a rewrite that preserved an id where it minted.
///
/// This asserts a *tree invariant* at a pass boundary and encodes no pass order,
/// so it is robust to pass reordering (a moved pass carries its check with it).
/// It catches the *class* of preserve-as-mint / clone-without-freshen bugs
/// across the whole test suite, not just a crafted program.
///
/// The walk is the same main-tree `walk_children` walk as
/// [`duplicate_node_ids`]/[`collect_tree_ids`] — a predicate-inclusive walk would
/// false-fire on inline's known predicate blind spot. Gated
/// via `cfg!(...)` as an expression (not a `#[cfg]` item) so the same call site
/// compiles under both `./ci.sh` clippy passes without a release-only
/// gated-item-reference failure.
pub(crate) fn assert_unique_node_ids(expr: &Expr, boundary: &str) {
    if !cfg!(any(debug_assertions, test)) {
        return;
    }
    let dups = duplicate_node_ids(expr);
    assert!(
        dups.is_empty(),
        "node-id uniqueness invariant violated at `{boundary}`: {} duplicated id(s) \
         (id, kind): {:?}",
        dups.len(),
        dups
    );
    // The `Default`/`mem::take` sentinel (see `NodeId::PLACEHOLDER`) is a
    // transient throwaway that must always be overwritten before it reaches a
    // pass boundary; a persisted placeholder means a `mem::take` slot was left
    // unfilled, which would silently corrupt provenance.
    fn walk_placeholder(e: &Expr, found: &mut bool) {
        if e.node_id() == NodeId::PLACEHOLDER {
            *found = true;
        }
        e.walk_children(|c| walk_placeholder(c, found));
    }
    let mut placeholder = false;
    walk_placeholder(expr, &mut placeholder);
    assert!(
        !placeholder,
        "Default/mem::take placeholder node persisted into the tree at `{boundary}`"
    );
}

/// Compile a CHL program and return its operator graph plus subscribed outputs.
///
/// Returns a [`CompiledProgram`] whose `outputs` vector contains one entry
/// per "output" of the program:
///
/// - **Pure programs** (no sinks): a single `("main", op)` entry whose
///   producer is subscribed to `main_consumer`.  The caller drives the main
///   loop by repeatedly calling [`TileProducer::get`] on that producer.
/// - **Sink programs** (e.g. `http_serve`): one entry per sink field of the
///   trailing `Record{…}`, each wired to a [`SinkConsumer`] that dispatches
///   to the registered [`DataSink`](crate::interpreter::DataSink).  For
///   sink-only programs the supplied `main_consumer` is dropped before
///   returning.
pub fn compile_program(
    ctx: &mut GlobalContext,
    code: &str,
    main_consumer: Box<dyn Consumer>,
) -> Result<CompiledProgram, Vec<CompileError>> {
    // ---- User-facing failure points ----
    //
    // The pipeline now accumulates errors across the *parse* and *lower*
    // stages before bailing: when the parser recovers from a syntax error
    // it still produces a partial AST, which lowering can run on and report
    // its own errors against. The combined list is returned in one pass so
    // the user sees everything at once. Inference and downstream stages
    // skip when anything earlier produced an error — they assume a well-
    // typed CCL tree without `Error` placeholders.
    //
    // Stage-internal consistency checks (`typecheck`, `check_fully_typed`)
    // keep their `.expect` because firing them means the compiler itself is
    // wrong, not the user's input.
    let mut errors: Vec<CompileError> = Vec::new();

    let parse_result = chl_parser::parse_module(code);
    errors.extend(parse_result.errors.into_iter().map(CompileError::Parse));
    let Some(module) = parse_result.value else {
        return Err(errors);
    };

    // Empty program: surface a properly-spanned error before lowering, so the
    // user sees the whole file underlined rather than `lower_stmts`'s catch-all
    // 0..0 fallback. (The catch-all stays in place to defend against direct
    // callers of `lower_stmts` that don't go through this path.)
    if module.body.is_empty() {
        errors.push(CompileError::Lower(LoweringError::unsupported(
            chl_parser::ast::Span::new(0, code.len()),
            "empty program: file contains no top-level statements",
        )));
        return Err(errors);
    }

    // The always-on lowering session: installed in every
    // build for the whole of lowering. Its leaf entries (`tag_source`/
    // `tag_machinery`) and copy-frame flushes (uncurry, compare-chain) record a
    // `LoweringLog`, folded once at the handoff below into the always-on lowering
    // projection. It must fully drain before the first pass (Mono) session opens.
    let lowering_session = RecorderSession::lowering();
    let lower_result = lower_stmts(&module.body, ctx.lowering_ctx());
    errors.extend(lower_result.errors.into_iter().map(CompileError::Lower));
    let Some(mut expr) = lower_result.value else {
        return Err(errors);
    };

    // Anything wrong earlier in the pipeline means `expr` may contain
    // `TypedExprNode::Error` placeholders; inference and below would
    // panic on them via [`crate::unexpected_error_node!`]. Bail here.
    if !errors.is_empty() {
        return Err(errors);
    }

    // Drain sink bindings discovered during lowering before taking sources.
    let sink_bindings_registry = ctx.lowering_ctx().take_sink_bindings();

    // Drain the lowering log and fold it once, at the lowering→pipeline
    // handoff (before uniquify/inference, so the release `InferError` read timing
    // is unchanged), into the always-on **lowering projection**: every lowered
    // node's [`SourceAttribution`], keyed by NodeId. It is the base every later
    // pane fold bottoms out in, and the source the release `InferError`
    // diagnostics resolve against one-hop. `uniquify` preserves every id in
    // place, so the projection's keys survive into the pre-inference pane.
    //
    // The fold's leak taxonomy enforces mint coverage: an unrecorded lowering
    // mint surfaces as `Leak::Unexplained` (every output-tree node must be
    // explained by a leaf or a copy). The checks are debug/test
    // gated at the boundary via `assert_leaks_clean`; the fold itself is
    // always-on (its product is release-critical).
    // Id uniqueness is the precondition for keying anything by `NodeId`, so gate
    // it before the fold that does exactly that: a duplicate here would silently
    // collapse two nodes' attributions into one projection entry. Lowering's own
    // copy sites (uncurry's template discharge, the chained-comparison operand
    // freshens) are what make this a live risk at this boundary.
    assert_unique_node_ids(&expr, "post-lowering");

    let lowering_log = lowering_session.into_lowering_log();
    let lowering_projection = {
        let output_ids = collect_tree_ids(&expr);
        let (projection, leaks) = collapse_lowering(&lowering_log, &output_ids);
        assert_leaks_clean(&leaks, "lowering");
        projection
    };

    debug!("Lowered (pre-desugar):\n{}", symbolic(&expr));

    // α-uniquify all binders (Barendregt convention): every binding site gets
    // a globally fresh `Name` uid, so shadowing ceases to exist before any
    // pass that compares names. Must run before defer desugaring — desugar's
    // rewrites splice and rename terms under the assumption that distinct
    // binders are distinct names. (Desugar now runs after inference; see below.)
    expr = uniquify::run(expr);

    // Retain the pre-inference IR for the inspector's upstream pane before
    // `infer` mutates `expr` in place. This is the source-shaped, pre-mono,
    // still-hole-typed tree. Its ids resolve against the `lowering_projection`
    // (the pre-mono originals). See `CompiledProgram::pre_inference_ir`.
    let pre_inference_ir = expr.clone();

    // Register every source (pre-registered + discovered during lowering) with
    // inference and operator-conversion now that the full source set is known.
    for (_name, source) in ctx.lowering_ctx().take_sources() {
        let name = source.borrow().get_id().to_string();
        let output_type = source.borrow().output_type();
        // The source's data-function type is constructed inside
        // `register_source_type` from the element type — the `Data` kind is
        // intrinsic, not stamped here.
        ctx.inference_ctx().register_source_type(&name, output_type);
        ctx.conversion_ctx().register_source(name, source);
    }

    debug!("Lowered:\n{}", symbolic(&expr));

    // Inference runs on the user-shaped tree — before channelize — so type
    // errors are reported against the program the user wrote, not the
    // channelized rewrite.
    let infer_outcome = infer(&mut expr, ctx.inference_ctx());
    // On failure, resolve each error's own blame node to a source span *here* —
    // the lowering projection is in scope and holds the lowered attribution (this
    // is the always-on release read: one hop, no fold). Every error names a node;
    // an id the projection doesn't cover (a node minted after lowering, e.g. by
    // monomorphization) degrades to a span-less diagnostic.
    if let Err(errors) = infer_outcome {
        return Err(errors
            .into_iter()
            .map(|located| {
                let span = lowering_projection
                    .get(&located.node_id)
                    .and_then(|attr| attr.spans.first().copied());
                CompileError::Infer {
                    error: located.error,
                    span,
                }
            })
            .collect());
    }
    debug!("Inferred:\n{}", symbolic(&expr));
    debug!("Inferred (typed):\n{}", symbolic_typed(&expr));
    // Consistency wall between `infer` and `channelize`. It is the relaxed
    // *pre-desugar* check (`check_pre_desugar`), which permits the transient
    // `Feed` / `Infer`-channel-domain types only desugar can erase. A failure
    // here is a compiler bug — with one exception: residual `Type::Infer`
    // variables, which inference deliberately tolerates for a generalized
    // definition the program never exercises at a concrete type (see
    // `Type::Infer`'s invariant). That residue is an *ambiguous program* — a
    // user error — so it is rendered as a diagnostic; anything else panics.
    check_pre_desugar(&expr).map_err(|errs| {
        if errs
            .iter()
            .all(|e| matches!(e, InferError::UnresolvedInfer { .. }))
        {
            errs.into_compile_errors()
        } else {
            panic!("Inference created invalid expr: {errs:?}")
        }
    })?;

    // Enforce the second-class `Mut` discipline (`src/ccl/design/mutability.md`,
    // "No aliasing: `Mut` values are second-class (downward-only)") on the
    // fully-typed, still-`Mut`-bearing tree — after the consistency wall,
    // before inlining. It needs the pre-inline `Apply`/parameter structure
    // (rule 1's argument check) and the coalesced `.ty` slots and
    // `user_annotation`s. Unlike the surrounding `check_pre_desugar` walls
    // (compiler-bug backstops), these are user errors: aliasing or nesting a
    // mutable reference.
    check_mut_discipline(&expr).map_err(|errs| errs.into_compile_errors())?;

    // Enforce that every `:=` / `+=` write targets a mutable variable (a write is
    // never a shadowing rebind of an immutable). Post-inference so binder types
    // are resolved, post-`uniquify` so write targets carry their binder's
    // α-unique name — see `check_mut_write_targets`. Load-bearing rather than a
    // formality: lowering emits a `MutWrite` for any `x := e` whose name is already in
    // scope, mutable variable or not (see `src/ccl/design/mutability.md`, "Mutability is the
    // type (no lowering registry)"), so this is what rejects a write to an immutable
    // binding — or to one monomorphization has since dropped.
    check_mut_write_targets(&expr).map_err(|errs| errs.into_compile_errors())?;

    // Inline UDFs *before* desugar: a defer-mediating UDF (`λ out → out << e`)
    // or a cross-function writer is beta-reduced to its call site before
    // desugar routes feeds and before the unified letrec phase folds writers,
    // both of which need their targets lexically present. Inlining runs on the
    // still-defer-bearing tree (Defer/Feed nodes and `Feed` types present) via
    // the defer-aware `Subst` engine (which renames a fed-to handle on
    // beta-reduction) and preserves defer-returning generators, so the
    // post-inline wall is the relaxed `check_pre_desugar`, not strict
    // `typecheck`.
    // Retain the post-inference IR for the inspector before `inline` consumes
    // `expr`. This is the source-shaped, fully-typed anchor (lambdas intact, not
    // yet point-free; inline/transact/letrec/desugar/lambda_elim/planning have
    // not run). `ast` (`join_planned`) is the *wrong* tree for a source
    // view — `lambda_elim`/`planning` re-mint ids and produce execution shape.
    // See `CompiledProgram::post_inference_ir`.
    let post_inference_ir = expr.clone();

    expr = inline::inline_capability_lambdas(expr);
    debug!("UDFs inlined CCL:\n{}", symbolic(&expr));
    check_pre_desugar(&expr).map_err(|errs| {
        if errs
            .iter()
            .all(|e| matches!(e, InferError::UnresolvedInfer { .. }))
        {
            errs.into_compile_errors()
        } else {
            panic!("UDF inlining created invalid expr: {errs:?}")
        }
    })?;

    // Transactional slice of the unified phase: rewrite every `with begin():`
    // writer of a `Mut(_, Txn)` mutable variable into a `get_prev_txn`-guarded `LetRec`
    // (histories + commit records over the commit domain), which
    // `planning::plan_loops` destructures into the `Transact{…, Txn}` node
    // op-conversion compiles to the commit engine — unifying the transaction and
    // induction paths on one `LetRec` + recognition representation. Runs *before*
    // `mut_elim` so the induction phase never sees a transaction loop. See
    // src/ccl/design/mutability.md.
    //
    // Being a transactional variable is the `Mut(_, Txn)` type; identity is the α-unique
    // binder `Name`. Both are read off the *inlined, typed* tree — so a
    // cross-function writer's mutable variables (its `transfer(a, b)` writes already
    // beta-reduced to name `a`/`b`) are seen, and an unrelated local merely spelled
    // like a mutable variable is not (its binder is a distinct `Name`). This replaces the
    // lowering-time base-name registry.
    let txn_mut_vars = transact_phase::collect_txn_mut_vars(&expr);
    // A transactional writer reaching a `with begin():` block via a function call
    // is a nested transaction — the callee's inlined `For` would otherwise be
    // silently absorbed into the outer block's read-your-writes env, dropping its
    // commit. Reject it before the phase strips the sites.
    transact_phase::check_no_nested_transactions(&expr, &txn_mut_vars)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    // An induction accumulator written inside a block with no mutable variable write is a
    // no-atomicity transaction — rejected here (type-aware), not at lowering.
    transact_phase::check_no_induction_only_transactions(&expr, &txn_mut_vars)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    // A *guarded* induction write inside a committing block (`balance := …; if p:
    // cnt += 1`) is not liftable and would be silently dropped from the decision
    // record — reject it before the phase runs (a debug-only assert would miss it
    // in release).
    transact_phase::check_no_guarded_induction_write_in_block(&expr, &txn_mut_vars)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    expr = transact_phase::run(expr, &txn_mut_vars);
    debug!("Transact phase CCL:\n{}", symbolic(&expr));
    check_pre_desugar(&expr).expect("transact phase produced an inconsistent tree");

    // The unified letrec phase: direct-mirror mutation loops (`For` /
    // `MutWrite`) become causal `LetRec` groups — mutable histories over
    // the induction domain, per src/ccl/design/mutability.md. Runs after
    // inlining (so cross-function writers land at their call sites) and
    // *before* channelize, so a per-iteration feed inside a loop is
    // hoisted to an ordinary feed of the loop's history for desugar to route.
    // The tree still carries Defer/Feed here, so the walls are the relaxed
    // pre-desugar check.
    let phase_out = mut_elim::run(expr);
    debug!("Letrec phase CCL:\n{}", symbolic(&phase_out));
    check_pre_desugar(&phase_out).expect("letrec phase produced an inconsistent tree");

    // Feed channelization — the feed-routing step of the unified phase, run on
    // the phase-emitted `LetRec` tree (recognition happens *after*
    // `lambda_elim`, below). Every `let d = Defer in body` is rewritten to
    // `let d = <channel> in body`, where `<channel>` is the `++`-union of the
    // defer's `<<` / `<<=` contributions; a channel assembled from a group's
    // taps binds inside the letrec body, below the binders it captures.
    // After this, no Defer/Feed/Define nodes — and no `Feed`/`ChanDom` types —
    // remain: channelization is type-preserving by construction and closes
    // channel domains by substitution; the strict `typecheck` below is the
    // release-visible enforcement.
    let mut desugared = channelize::run(phase_out).errs()?;
    debug!("Channelized:\n{}", symbolic(&desugared));
    typecheck(&desugared).expect("channelize produced an ill-typed tree");

    // Retain the post-channelize tree for the inspector's downstream pane. On the
    // post-inference desugar order this snapshot is *downstream* of
    // `post_inference_ir` (post-inline/transact/letrec/channelize); see the doc
    // comment on `post_desugar_ir`.
    let post_desugar_ir = desugared.clone();

    // Fed-out mutable variable reads: rewrite a read-only reply that reads a mutable variable out of
    // its block into an outer-indexed as-of join (an as-of read at the reading
    // transaction's arbitrary commit position), *before* lambda elimination — so a
    // computed reply (`resp << balance + 1`) stays a lambda the elim pass point-frees,
    // rather than a point-free `const` a planning-time recognizer would have to
    // reject. Uniform across the reading loop's domain. See
    // `transact_phase::rewrite_live_reads`.
    transact_phase::rewrite_live_reads(&mut desugared);
    typecheck(&desugared).expect("live-read rewrite produced an ill-typed tree");

    let lambda_elim = lambda_elim::run(desugared).errs()?;
    debug!("λ-eliminated CCL:\n{}", symbolic(&lambda_elim));
    debug!("λ-eliminated typed CCL:\n{}", symbolic_typed(&lambda_elim));

    // `typecheck` enforces hole-freeness as its first phase, so this call
    // alone covers both checks.
    typecheck(&lambda_elim).expect("type error after lambda elimination");

    // Recognition: lower each causal group — now in its point-free normal
    // form — onto the domain-parameterized `Transact` carrier (a
    // `get_prev_txn` transaction group → `Transact{Txn}`; a `get_prev_seq`
    // induction group → `Transact{iteration extent}`) so planning stages the
    // writer sources and operator conversion picks the engine on the domain.
    // Running post-elim is what keeps ONE letrec representation through
    // channelize and lambda_elim; the point-free guard matcher re-checks
    // causality at this wall. See the `mut_elim` recognition docs.
    let recognized = planning::plan_loops(lambda_elim);
    debug!("Letrec recognized CCL:\n{}", symbolic(&recognized));
    typecheck(&recognized).expect("letrec recognition produced an ill-typed tree");

    let join_planned = planning::run(recognized);
    debug!(
        "Join-planned CCL:\n{} : {}",
        symbolic(&join_planned),
        join_planned.ty
    );
    debug!("Join-planned CCL:\n{}", symbolic_typed(&join_planned));

    // Planning is the one pass that introduces `iterate` / `restrict` /
    // `Compose` staging, so re-checking its output catches a malformed tile
    // graph an adjacency that doesn't chain would otherwise hide. Planning
    // surfaces each iterated / join-satisfying extent on its producer
    // (`refine_extent` / `set_extent`) and the strict checker
    // matches the fresh refinements it mints by structural predicate
    // equality, so the staging shapes now validate without re-blinding the
    // check or peeling cast refinements.
    typecheck(&join_planned).expect("type error after join planning");
    // Invariant (debug): planning's `iterate`/`restrict` markers live in the
    // term tree, never inside a type's refinement predicates — the substitution
    // boundary strips the neutral `iterate` marker (`ccl_utils::strip_iterate_markers`),
    // and a `restrict` reaching a predicate (a filtered source used in a refined
    // domain) is unsupported and must surface loudly, not miscompile.
    #[cfg(debug_assertions)]
    crate::ccl::ccl_utils::debug_assert_no_iteration_markers(&join_planned);

    // Compile to one operator per field of the trailing record.  Pure
    // programs (no sinks) end up at this point with a bare expression at the
    // tail of the `Let*` chain rather than a `Record`; we synthesise a single
    // `("main", op)` entry for them so the rest of the function operates
    // uniformly on `Vec<(name, op)>`.
    let per_field_ops = if sink_bindings_registry.is_empty() {
        let op = convert_to_operators(&join_planned, ctx.conversion_ctx()).errs()?;
        vec![("main".to_string(), op)]
    } else {
        convert_record_fields_to_operators(&join_planned, ctx.conversion_ctx()).errs()?
    };

    let sink_count = per_field_ops
        .iter()
        .filter(|(name, _)| name != "main")
        .count();
    let (mut notifiers, done_rx) = DoneNotifier::create(sink_count);

    let mut main_consumer = Some(main_consumer);
    let mut outputs = Vec::with_capacity(per_field_ops.len());
    for (name, mut op) in per_field_ops {
        let universal = op.tiling().universal_guard();
        if name == "main" {
            // Subscribe the user-supplied consumer to drive the main output.
            let main_consumer = main_consumer
                .take()
                .expect("multiple `main` fields in trailing record");
            let producer = op.subscribe(universal, main_consumer, ctx.scheduler());
            debug!(
                "Main producer:\n{}",
                pretty_tile_producer_with(
                    producer.as_ref(),
                    &VizOptions {
                        max_depth: Some(30),
                        ..Default::default()
                    }
                )
            );
            outputs.push(CompiledOutput {
                name,
                op,
                producer: Some(producer),
                sink_consumer: None,
            });
        } else {
            let sink = sink_bindings_registry
                .get(&name)
                .unwrap_or_else(|| panic!("no sink registered for field '{name}'"))
                .clone();

            let notifier = notifiers.pop().unwrap();
            let (sink_consumer, producer_slot) = SinkConsumer::new(sink, notifier);
            let consumer_rc = Rc::new(RefCell::new(sink_consumer));
            let sink_producer =
                op.subscribe(universal, Box::new(consumer_rc.clone()), ctx.scheduler());
            debug!(
                "Sink producer for {name}:\n{}",
                pretty_tile_producer_with(
                    sink_producer.as_ref(),
                    &VizOptions {
                        max_depth: Some(30),
                        ..Default::default()
                    }
                )
            );
            *producer_slot.borrow_mut() = Some(sink_producer);
            outputs.push(CompiledOutput {
                name,
                op,
                producer: None,
                sink_consumer: Some(consumer_rc),
            });
        }
    }

    Ok(CompiledProgram {
        ast: join_planned,
        outputs,
        done: done_rx,
        lowering_projection,
        pre_inference_ir,
        post_inference_ir,
        post_desugar_ir,
        source_ast: module,
        source: code.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    /// Driver that runs `compile_program` for an error-only test, returning
    /// the collected error list. Discards the program — these tests only
    /// care about which errors surface.
    fn compile_err(code: &str) -> Vec<CompileError> {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        match compile_program(&mut ctx, code, consumer) {
            Ok(_) => panic!("expected compile error, got success"),
            Err(errs) => errs,
        }
    }

    #[test]
    fn rendered_errors_have_exact_format() {
        let code = "\
x = 1 +
y = {a: 1}
y
";
        let errs = compile_err(code);
        let out = render_errors(&errs, "<test>", code);
        let expected = "\
Error: parse error
   ╭─[<test>:1:8]
   │
 1 │ x = 1 +
   │ ───┬─┬─┬
   │    ╰────── while parsing statement
   │      │ │
   │      ╰──── while parsing expression
   │        │
   │        ╰── found 'newline', expected expression, or '-'
───╯
Error: lowering error
   ╭─[<test>:2:5]
   │
 2 │ y = {a: 1}
   │     ───┬──
   │        ╰──── `{…}` is type syntax (a record type `{name: T}`); a record value is written `(name=value)`
───╯
";
        let normalize = |s: &str| -> String {
            s.lines()
                .map(|l| l.trim_end())
                .collect::<Vec<_>>()
                .join("\n")
                + "\n"
        };
        assert_eq!(
            normalize(&out),
            normalize(expected),
            "actual rendered output:\n{out}"
        );
    }

    /// Resolution: a deliberate type error carries a blame node
    /// whose provenance resolves to a source span. `1 and 2` constrains the
    /// integer literal against `and`'s `Bool` operand during pass-1 emission,
    /// so the blame node is that pass-1 emit site and its id round-trips
    /// through the lowering projection (`SourceProjection`, keyed by `NodeId`)
    /// to a `Some` span over the offending expression.
    ///
    /// (`1 + "a"` reaches the same outcome by the other route: its `Int`/`String`
    /// collision surfaces in pass-2 coalesce, which blames per error — see
    /// `coalesce_error_carries_resolved_span`.)
    #[test]
    fn infer_error_carries_resolved_span() {
        let code = "1 and 2\n";
        let errs = compile_err(code);
        let (error, span) = errs
            .iter()
            .find_map(|e| match e {
                CompileError::Infer { error, span } => Some((error, *span)),
                _ => None,
            })
            .unwrap_or_else(|| panic!("expected an Infer error, got: {errs:?}"));
        assert!(
            matches!(error, InferError::TypeMismatch { .. }),
            "expected a pass-1 TypeMismatch, got {error:?}"
        );
        let span = span.expect("the type error resolves to a source span");
        let pointed = &code[span.start..span.end];
        assert!(
            pointed.contains("and"),
            "span {span:?} should cover the offending expression, points at {pointed:?}"
        );
    }

    /// The pass-2 counterpart: a collision the emitter accepts and *coalesce*
    /// rejects still resolves to a span.
    ///
    /// `1 + "a"` constrains one variable against both `Int` and `String`, which
    /// only fails when the bounds are resolved — so this is the accumulating
    /// walk's blame path (`CoalesceCtx::current_node`, stamped by `coalesce_node`),
    /// not emission's. Coalesce blames per error, so each of several errors
    /// renders with its own source context.
    #[test]
    fn coalesce_error_carries_resolved_span() {
        let code = "1 + \"a\"\n";
        let errs = compile_err(code);
        let (error, span) = errs
            .iter()
            .find_map(|e| match e {
                CompileError::Infer { error, span } => Some((error, *span)),
                _ => None,
            })
            .unwrap_or_else(|| panic!("expected an Infer error, got: {errs:?}"));
        let span = span.unwrap_or_else(|| {
            panic!("the coalesce error resolves to a source span, got {error:?} with no span")
        });
        let pointed = &code[span.start..span.end];
        assert_eq!(
            pointed, "1 + \"a\"",
            "the blame is the node whose coalesce frame raised the error — here the \
             `+` application over both operands, not the whole program or nothing"
        );
    }

    /// An unbound variable (the canonical pass-1 emit error) also resolves to
    /// its single-token source span.
    #[test]
    fn unbound_variable_carries_resolved_span() {
        let code = "y\n";
        let errs = compile_err(code);
        let (error, span) = errs
            .iter()
            .find_map(|e| match e {
                CompileError::Infer { error, span } => Some((error, *span)),
                _ => None,
            })
            .unwrap_or_else(|| panic!("expected an Infer error, got: {errs:?}"));
        assert!(matches!(error, InferError::UnboundVariable(_)));
        assert_eq!(
            span,
            Some(chl_parser::ast::Span::new(0, 1)),
            "the use of `y` spans byte offsets 0..1"
        );
    }

    /// The requirement sweep is a *third* blame path, beside emission's and
    /// coalesce's, and it resolves to a span like both of them.
    ///
    /// It needs its own because it raises before coalesce and about a **place**, which
    /// is not always some node's type: where a value's occurrences are split across
    /// variables, the conflict sits at an interior place that only a *bound* reaches.
    /// Blame is structural and does not follow bounds, so no node's type names a
    /// variable standing there — which is why the failure offers the variable the walk
    /// started from as well, and why both spellings below can name the lambda.
    ///
    /// Both are pinned because they are the same program: whether the parameters are
    /// curried decides whether the place is interior, and the diagnostic must not
    /// notice. Each case also puts a binding *before* the offending one, so the tree
    /// root's own span is not the expected answer — without that, a blame path that had
    /// silently collapsed to the root would still look correct here.
    #[rstest]
    #[case::curried(
        "g = 2\nf = \\a -> (a + 1, a + \"s\")\ng\n",
        "\\a -> (a + 1, a + \"s\")"
    )]
    #[case::uncurried(
        "g = 2\nf = \\a, b -> (a + 1, a + \"s\")\ng\n",
        "\\a, b -> (a + 1, a + \"s\")"
    )]
    fn unsatisfiable_operand_carries_resolved_span(#[case] code: &str, #[case] expected: &str) {
        let errs = compile_err(code);
        let (error, span) = errs
            .iter()
            .find_map(|e| match e {
                CompileError::Infer { error, span } => Some((error, *span)),
                _ => None,
            })
            .unwrap_or_else(|| panic!("expected an Infer error, got: {errs:?}"));
        assert!(
            matches!(error, InferError::UnsatisfiableOperand { .. }),
            "expected the sweep's own error, got {error:?}"
        );
        let span = span.expect("an unsatisfiable operand resolves to a source span");
        assert_eq!(
            &code[span.start..span.end],
            expected,
            "blame must land on a node enclosing the conflict, never the whole program \
             and never nothing",
        );
    }

    /// Terminal rendering: a span-carrying inference error renders
    /// as an ariadne report with the source line and an underline, NOT the
    /// bare `error: type inference: …` plain-text fallback.
    #[test]
    fn infer_error_renders_with_source_context() {
        let code = "1 and 2\n";
        let errs = compile_err(code);
        let out = render_errors(&errs, "<test>", code);
        assert!(
            !out.contains("error: type inference:"),
            "span-carrying infer error must not use the plain-text fallback; got:\n{out}"
        );
        // ariadne report markers: the source line, the file:line:col header,
        // and box-drawing for the underline/gutter.
        assert!(
            out.contains("<test>:1") && out.contains("1 and 2") && out.contains('│'),
            "expected an ariadne report with source context; got:\n{out}"
        );
    }

    /// A parser-recoverable error in one statement does not stop us from
    /// running lowering and reporting lowering errors elsewhere. Both stages'
    /// errors come back in a single `Vec<CompileError>`.
    #[test]
    fn parse_error_does_not_suppress_later_lowering_errors() {
        // Statement 1 has a syntax error (parser recovers at the next
        // newline); statement 2 is a brace record in value position, which
        // parses but lowering rejects (braces are type syntax). We must see
        // both stages' errors in the result.
        let code = "\
x = (1 +)
y = {a: 1}
y
";
        let errs = compile_err(code);
        let has_parse = errs.iter().any(|e| matches!(e, CompileError::Parse(_)));
        let has_lower = errs.iter().any(|e| matches!(e, CompileError::Lower(_)));
        assert!(
            has_parse && has_lower,
            "expected at least one Parse and one Lower error, got: {errs:?}"
        );
    }

    /// Multiple parse errors in one file all flow through, one
    /// `CompileError::Parse` per `ParseError`.
    #[test]
    fn multiple_parse_errors_all_surface() {
        let code = "\
x = 1 +
y = 2 *
1
";
        let errs = compile_err(code);
        let parse_count = errs
            .iter()
            .filter(|e| matches!(e, CompileError::Parse(_)))
            .count();
        assert!(
            parse_count >= 2,
            "expected at least 2 parse errors, got {parse_count}: {errs:?}"
        );
    }

    /// Lowering also recovers per top-level statement: if two distinct
    /// statements each carry a lowering-rejected construct, both errors come
    /// back instead of just the first.
    #[test]
    fn multiple_lowering_errors_all_surface() {
        let code = "\
x = {a: 1}
y = {b: 2}
y
";
        let errs = compile_err(code);
        let lower_count = errs
            .iter()
            .filter(|e| matches!(e, CompileError::Lower(_)))
            .count();
        assert!(
            lower_count >= 2,
            "expected at least 2 lowering errors, got {lower_count}: {errs:?}"
        );
    }

    /// A pure parse-error file (no extra lowering issues) reports only its
    /// parse errors — no spurious lowering error from the `Expr::Error`
    /// recovery placeholder bubbling up.
    #[test]
    fn parse_recovery_placeholders_dont_produce_lowering_errors() {
        let code = "\
x = (1 +)
1
";
        let errs = compile_err(code);
        let lower_count = errs
            .iter()
            .filter(|e| matches!(e, CompileError::Lower(_)))
            .count();
        assert_eq!(
            lower_count, 0,
            "lowering errors should be silent on parse-recovery placeholders, got: {errs:?}"
        );
        let parse_count = errs
            .iter()
            .filter(|e| matches!(e, CompileError::Parse(_)))
            .count();
        assert!(
            parse_count >= 1,
            "expected at least 1 parse error: {errs:?}"
        );
    }
}

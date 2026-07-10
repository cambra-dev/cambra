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
        Expr, Type, desugar_defers,
        infer::{
            InferError, TypeInferenceContext, check_mut_discipline, check_mut_write_targets,
            check_pre_desugar, infer, typecheck,
        },
        inline, lambda_elim, letrec_phase,
        lower::{LoweringContext, LoweringError, lower_stmts},
        planning,
        provenance::{NodeId, Pass, Provenance, ProvenanceTable},
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
/// remaining variants render as plain `error: …` lines. The same
/// [`CompileError`]s feed the web [`Diagnostic`](crate::inspector_model::Diagnostic)
/// JSON path via [`diagnostics_from_compile_errors`](crate::inspector_model::diagnostics_from_compile_errors)
/// — one error model, two renderers. Lambda-elim/conversion spans remain
/// future work; the enum is shaped so they migrate without changing the
/// list-of-errors return contract.
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
    DesugarDefers(desugar_defers::DeferError),
    /// Type inference rejected one expression.
    ///
    /// `span` is the offending source range, resolved at the `compile_program`
    /// boundary via the `ProvenanceTable`. `None` when no precise
    /// node was known (coalesce/scope errors, or a caller without the table) —
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
    /// only becomes visible after inlining / type inference — a nested
    /// transaction reaching a `with begin():` block via a function call, or a
    /// live cross-endpoint read in a shape the as-of rewrite cannot stage. These
    /// run on a lambda-free / inlined tree whose nodes carry no source span, so
    /// they render as a plain `error: …` line rather than an ariadne report.
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

impl From<desugar_defers::DeferError> for CompileError {
    fn from(e: desugar_defers::DeferError) -> Self {
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
        // Fallback for callers that don't hold the `ProvenanceTable` (i.e. not
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

impl IntoCompileErrors for desugar_defers::DeferError {
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
    /// Provenance side table mapping post-inference-node
    /// [`NodeId`](crate::ccl::provenance::NodeId)s to the source spans they came
    /// from. Populated by lowering (`Source(span)`), then extended through
    /// inference by the monomorphization remap (`Derived { via: Mono }`) and the
    /// `desugar_defers` tagging (`Derived`/`Synthetic { via: Desugar }`).
    ///
    /// The table is complete for the **post-inference tree**: its entries key on
    /// the same [`NodeId`]s carried by [`post_inference_ir`](Self::post_inference_ir).
    /// Resolving any node of that snapshot against this table is the inspector's
    /// (and diagnostics') source-map projection (node → span). The inverse
    /// direction (span → node) is provided by
    /// [`crate::inspector_model::SpanIndex`], built over the same pair.
    pub provenance: ProvenanceTable,
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
    /// snapshot holds the pre-mono **originals**. Its fan-out to the post-mono
    /// [`post_inference_ir`](Self::post_inference_ir) is exactly what the
    /// [`Pass::Mono`] entry of [`pass_remaps`](Self::pass_remaps) carries (one
    /// upstream def → N downstream clones); every ordinary node keeps its id
    /// identical across the pair. Its ids resolve against
    /// [`provenance`](Self::provenance) (they are the pre-mono originals, keyed
    /// by the lowering `Source` tags in that table).
    pub pre_inference_ir: Expr,
    /// The post-inference IR snapshot — the program inspector's anchor.
    ///
    /// This is `expr` captured **right after `infer`/`typecheck` and before
    /// `inline::inline_non_iterable_lambdas` consumes it**: fully typed, but
    /// still *source-shaped* (lambdas intact, not yet point-free — `inline`,
    /// `lambda_elim`, and `planning` have not run). Its node ids resolve against
    /// [`provenance`](Self::provenance) (they are the very same nodes the table
    /// was tagged against).
    ///
    /// Distinct from [`ast`](Self::ast), which holds `join_planned` (the
    /// *post-planning* tree): `lambda_elim`/`planning` re-mint every `NodeId`,
    /// so `ast`'s ids resolve to `None` in the table, and it is
    /// execution-shaped (point-free, fused) — the wrong tree for a source-level
    /// view. The inspector anchors here instead (see [[provenance-substrate]]
    /// Anchor note).
    pub post_inference_ir: Expr,
    /// The post-desugar IR snapshot — the inspector's **downstream** pane, one
    /// pipeline stage *below* [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// This is `expr` captured **right after `desugar_defers`** (which now runs
    /// after `infer`/`inline`/`transact`/`letrec`): fully typed and structurally
    /// final for the source view — no Defer/Feed/Define nodes remain, and the
    /// channelization artifacts (`Compose` wrapper chains, `CollectionUnion`
    /// fan-ins) are present. Because monomorphization ran earlier (inside
    /// `infer`), this tree is post-mono like [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// The post-inference ⇄ post-desugar adjacency: every id preserved through
    /// inline/transact/letrec/desugar is shared with
    /// [`post_inference_ir`](Self::post_inference_ir) (an implicit identity
    /// edge), and the inline fan-out's non-identity edges are the [`Pass::Inline`]
    /// entry of [`pass_remaps`](Self::pass_remaps). The richer desugar
    /// cross-edges are deferred to the desugar recorder's rewrite. See
    /// [[multi-pane-inspector]].
    pub post_desugar_ir: Expr,
    /// Raw node→node remaps, keyed by the [`Pass`] that produced each — retained
    /// for the inspector's stage-adjacency projection
    /// ([`crate::inspector_model::StageAdjacency`]).
    ///
    /// Each entry's pairs are `(downstream id, upstream origin id)` — the
    /// orientation [`crate::ccl::node_recorder::NodeRecorder::stage_remap`]
    /// emits and [`crate::inspector_model::StageAdjacency::from_remap`]
    /// expects. These are the **non-identity** edges a pass introduces;
    /// identity edges (a `NodeId` present in both trees) are implicit and not
    /// stored.
    ///
    /// * [`Pass::Mono`] — monomorphization fan-out surfaced by inference (one
    ///   upstream def → N downstream clones) plus the
    ///   `coalesce_generalized_let` wrappers. Possibly chained for nested
    ///   specializations (an origin may itself be a fresh id of an earlier
    ///   pair — resolved transitively when the adjacency is built).
    /// * [`Pass::Inline`] — inline fan-out surfaced by the inline pass's
    ///   [`NodeRecorder`](crate::ccl::node_recorder::NodeRecorder) (one
    ///   upstream node → N freshened copies when a UDF body is beta-reduced to
    ///   multiple call sites).
    ///
    /// Keyed by **pass**, not by inspector stage/pane: the compiler knows which
    /// pass produced a remap; which adjacent stage *pair* a pass bridges is
    /// inspector vocabulary and lives in `inspector_model` (the pair→pass
    /// association in its stage-links assembly).
    pub pass_remaps: Vec<(Pass, Vec<(NodeId, NodeId)>)>,
    /// The parsed CHL surface AST — the source-of-truth for source-level
    /// (lexical) inspector queries.
    ///
    /// This is the [`Module`](crate::chl_parser::ast::Module) lowering consumed,
    /// retained verbatim. It is the anchor for *source-language* questions —
    /// name resolution (`goto-definition`, the binder half of `scope-at`) —
    /// answered by [`crate::inspector_model::NameBinderIndex`].
    ///
    /// It is deliberately **distinct from [`post_inference_ir`](Self::post_inference_ir)**
    /// (the typed IR): lowering destroys some source variables before any IR
    /// node exists — notably `uncurry_params` rewrites multi-param references
    /// `Var(x)` to `__arg_tuple_N ▷ .i` *before* uniquify, so the lowered/typed
    /// tree structurally cannot resolve a multi-param `def`/`lambda` parameter
    /// back to its binder. The surface AST still has `x`/`y` with their
    /// `Param.name_span`, so lexical resolution over *this* is lossless (D5).
    pub source_ast: chl_parser::ast::Module,
    /// The original program source text, retained verbatim.
    ///
    /// Inspector queries need the source string to produce snippets (`hover`'s
    /// `snippet` = `source[span]`) and, in I3, to serve the `/api/snapshot`
    /// `source.text`. `CompiledProgram` did not retain it before; every
    /// span-keyed projection above (the [`ProvenanceTable`], the surface AST's
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

    /// The retained `(downstream, upstream)` node remap of `pass`, or an empty
    /// slice if the pass retained none (see
    /// [`pass_remaps`](Self::pass_remaps)). If a pass ever retains multiple
    /// entries, this returns the first — consumers that must see them all
    /// iterate `pass_remaps` directly.
    pub fn remap_for(&self, pass: Pass) -> &[(NodeId, NodeId)] {
        self.pass_remaps
            .iter()
            .find(|(p, _)| *p == pass)
            .map_or(&[], |(_, remap)| remap.as_slice())
    }
}

/// Names of the declared provenance record sets, shared by the per-boundary
/// record appliers (application order + [`PendingRecordTargets`] bookkeeping)
/// and the ordering-violation messages.
const RECORDS_MONO_REMAP: &str = "mono remap";
/// See [`RECORDS_MONO_REMAP`].
const RECORDS_INLINE: &str = "inline fan-out";
/// See [`RECORDS_MONO_REMAP`].
const RECORDS_FANINS: &str = "desugar fan-in";

/// Ordering guardrail for the per-boundary record appliers: the target ids of
/// every *declared* record set that has not yet been applied.
///
/// A single instance is [`declare`](Self::declare)d incrementally and threaded
/// across the whole `compile_program` sequence — mono at the infer boundary,
/// inline at the inline boundary, the desugar sets at the desugar boundary — so
/// the guardrail spans every application even though each set's targets only
/// become known at its own pipeline stage.
///
/// Each declared set knows exactly which node ids it will tag — the mono
/// remap's fresh clone ids, the inline fan-out copy ids, the desugar fan-in
/// `target`s. (The trailing `Synthetic` sweep is a fallback over "whatever is
/// left" and is deliberately not declared.) When a record's origin id fails to
/// resolve during application, there are two cases the graceful-`None` path
/// alone cannot distinguish:
///
/// - the id is unknown everywhere → genuinely unresolvable; degrade gracefully
///   (empty origins / `Synthetic`), exactly as before;
/// - the id is a **target of a not-yet-applied set** → the current set was
///   applied before a set it data-depends on: an ordering violation that would
///   otherwise silently manifest as empty origins (how the gap-2 inversion
///   hid).
///
/// The second case panics in debug/test builds (reconcile-style: every compile
/// in the suite probes the ordering) and is compiled down to a no-op in
/// release, where the graceful path is the behavior. A set is removed from the
/// pending union *before* it applies, so its own targets never count as
/// "later" — a fan-in's source list can legitimately name other fan-in targets,
/// and a failed mono chain passes through interior mono-fresh ids.
struct PendingRecordTargets {
    /// `(set name, its target ids)`, one entry per declared-but-unapplied set.
    /// Left empty in release non-test builds, which turns every method into a
    /// cheap no-op without `cfg`-gating any signature.
    pending: Vec<(&'static str, std::collections::HashSet<NodeId>)>,
}

impl PendingRecordTargets {
    /// An empty guardrail; record sets are added by [`declare`](Self::declare)
    /// as they become known along the pipeline.
    fn new() -> Self {
        Self {
            pending: Vec::new(),
        }
    }

    /// Declare a record set and the node ids it will tag, before it is applied.
    ///
    /// In release non-test builds the guardrail compiles down to no-ops (see the
    /// field docs), so the target set is never built.
    fn declare(&mut self, set: &'static str, targets: impl IntoIterator<Item = NodeId>) {
        if !cfg!(any(debug_assertions, test)) {
            return;
        }
        self.pending.push((
            set,
            targets
                .into_iter()
                .collect::<std::collections::HashSet<_>>(),
        ));
    }

    /// Convenience: declare a desugar record set from its [`DesugarFanin`]s.
    fn declare_fanins(&mut self, set: &'static str, records: &[desugar_defers::DesugarFanin]) {
        self.declare(set, records.iter().map(|record| record.target));
    }

    /// Remove `set` from the pending union. Call *before* applying the set so
    /// its own targets don't count as "later" (see the type docs).
    fn mark_applied(&mut self, set: &'static str) {
        self.pending.retain(|(name, _)| *name != set);
    }

    /// The not-yet-applied set that owns `id` as a target, if any.
    fn owner_of(&self, id: NodeId) -> Option<&'static str> {
        self.pending
            .iter()
            .find(|(_, targets)| targets.contains(&id))
            .map(|(name, _)| *name)
    }

    /// Report an origin id that failed to resolve while applying a
    /// `record_kind` record: panics (debug/test builds) if a not-yet-applied
    /// set owns it — an ordering violation — and does nothing for a
    /// genuinely-unknown id (the graceful `None` path).
    fn check_unresolved_origin(&self, record_kind: &'static str, failed: NodeId) {
        if let Some(owner) = self.owner_of(failed) {
            panic!(
                "provenance record ordering violation: a {record_kind} record's origin \
                 {failed:?} failed to resolve, but it is a target of the not-yet-applied \
                 {owner} record set — the {record_kind} records were applied before the \
                 {owner} records they data-depend on"
            );
        }
    }
}

/// Every duplicated [`NodeId`] over the **main tree** — the `walk_children`
/// node-set [`crate::ccl::node_recorder`]'s `collect_ids` uses (refinement
/// predicates excluded, matching inline's known predicate blind spot so the
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
/// This asserts a *tree invariant* at a pass boundary and encodes no pass order,
/// so it is robust to pass reordering (a moved pass carries its check with it).
/// It catches the *class* of preserve-as-mint / clone-without-freshen bugs
/// across the whole test suite, not just a crafted program.
///
/// The walk is the same main-tree `walk_children` walk as
/// [`duplicate_node_ids`]/`collect_ids` — a predicate-inclusive walk would
/// false-fire on inline's known predicate blind spot (review finding 6). Gated
/// via `cfg!(...)` as an expression (not a `#[cfg]` item) so the same call site
/// compiles under both `./ci.sh` clippy passes without a release-only
/// gated-item-reference failure.
fn assert_unique_node_ids(expr: &Expr, boundary: &str) {
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
}

/// Apply the monomorphization remap to `provenance`.
///
/// `remap` is the `(fresh_clone_id, source_clone_id)` pairs inference produced:
/// every node a specialization cloned got a fresh id, paired with the id it was
/// cloned *from*. For each `fresh`, walk the chain `fresh → source → …` through
/// the remap until reaching an id that is present in the table (a real lowered
/// node), and tag `fresh` `Derived { via: Mono }` with that node's origins.
///
/// Why a chain: a clone is coalesced re-entrantly, so a nested generalized
/// `let` specializes recursively and its own clone's nodes were freshened off
/// the *outer* clone's already-fresh ids. Those interior fresh ids are not in
/// the table, so resolution must follow the remap transitively to the original
/// lowered node. Resolution is against table *membership* (not insertion
/// order), so the pass is robust to pair ordering. A chain that bottoms out at
/// an id absent from the table (an untagged synthetic interior node) leaves
/// `fresh` untagged — graceful `None`. The visited-set guards against cycles
/// (there should be none — each fresh id is minted once and appears as a `new`
/// exactly once — but the walk must terminate regardless).
fn apply_mono_remap(
    provenance: &mut ProvenanceTable,
    remap: &[(NodeId, NodeId)],
    pending: &PendingRecordTargets,
) {
    use std::collections::HashMap;

    // `new → old` lookup so a chain step is O(1).
    let predecessor: HashMap<NodeId, NodeId> = remap.iter().copied().collect();

    // Collect tags first, then apply: resolving reads the table, so deciding
    // all tags before mutating keeps resolution against the table's original
    // (lowered) membership and order-independent.
    let mut tags: Vec<(NodeId, Provenance)> = Vec::new();
    for &(fresh, source) in remap {
        match resolve_origins_through_chain(provenance, source, &predecessor) {
            // Chain reached a known (lowered) node: blame its source span(s).
            Some(origins) => tags.push((fresh, Provenance::derived(Pass::Mono, origins))),
            // Chain bottomed out at an untagged interior node (e.g. a
            // generalized-`let` whose binding id was re-minted upstream). Tag it
            // `Synthetic { via: Mono }` rather than leaving it `None`: it is
            // honestly mono plumbing the inspector hides, and attributing it to
            // its actual pass keeps the `Synthetic` sweep from mislabeling it
            // `via: Desugar`.
            None => {
                // Ordering guardrail: every id the failed chain visited is
                // unknown to the table (the walk stops at the first id that
                // resolves), so re-walk it and check each against the
                // not-yet-applied record sets' targets.
                if cfg!(any(debug_assertions, test)) {
                    let mut cursor = source;
                    let mut seen = std::collections::HashSet::new();
                    loop {
                        pending.check_unresolved_origin(RECORDS_MONO_REMAP, cursor);
                        if !seen.insert(cursor) {
                            break;
                        }
                        match predecessor.get(&cursor) {
                            Some(&next) => cursor = next,
                            None => break,
                        }
                    }
                }
                tags.push((fresh, Provenance::synthetic(Pass::Mono, [])));
            }
        }
    }
    for (fresh, prov) in tags {
        provenance.insert(fresh, prov);
    }
}

/// Follow the remap chain `start → predecessor[start] → …` until reaching an id
/// the table knows, returning that node's origins. `None` if the chain bottoms
/// out at an untagged interior node (graceful degradation) — the visited set
/// guards against cycles (there should be none).
///
/// Shared by [`apply_mono_remap`] (which chains through the mono remap) and, as
/// the single-step degenerate case (`predecessor` empty), by direct id
/// resolution.
fn resolve_origins_through_chain(
    provenance: &ProvenanceTable,
    start: NodeId,
    predecessor: &std::collections::HashMap<NodeId, NodeId>,
) -> Option<Vec<chl_parser::ast::Span>> {
    use std::collections::HashSet;
    let mut cursor = start;
    let mut seen = HashSet::new();
    loop {
        if let Some(prov) = provenance.resolve(cursor) {
            break Some(prov.origins.clone());
        }
        if !seen.insert(cursor) {
            break None;
        }
        match predecessor.get(&cursor) {
            Some(&next) => cursor = next,
            None => break None,
        }
    }
}

/// Tag each [`DesugarFanin`]'s target with the source spans its feeds resolve
/// to — a multi-origin `Derived { via: Desugar }` (the many-to-one source→node
/// lineage, D2).
///
/// Applied by [`apply_desugar_records`] in dataflow order after the mono remap
/// and inline fan-out (`record_kind` names the set for the ordering guardrail's
/// messages). A target whose feeds all resolve to nothing is still tagged
/// `Derived` with empty origins (it remains `None`-for-spans but, being a table
/// member now, is excluded from the trailing `Synthetic` sweep). Every target
/// this tags becomes a table member, which is what lets the sweep skip them by
/// table membership alone.
fn apply_desugar_fanins(
    provenance: &mut ProvenanceTable,
    fanins: &[desugar_defers::DesugarFanin],
    record_kind: &'static str,
    pending: &PendingRecordTargets,
) {
    // Empty predecessor map → single-step resolution (no chaining).
    let no_chain = std::collections::HashMap::new();
    let mut tags: Vec<(NodeId, Provenance)> = Vec::new();
    for fanin in fanins {
        // Never overwrite a node the table already knows — a fan-in record may
        // name a node whose id was *preserved* from lowering (e.g. a feed-value
        // subexpression keeps its finer `Source` span); the synthesized
        // channel-union nodes are the unknown ids. Skipping known ids also keeps
        // this pass idempotent.
        if provenance.resolve(fanin.target).is_some() {
            continue;
        }
        // Each `sources` entry is one feed's pre-order id list (see
        // `combine_feed_values` / `DesugarFanin`). Take the *first* id that
        // resolves per feed — the feed-value span the user wrote — rather than
        // every descendant span (which would also blame sub-expressions). The
        // union of one span per feed is the many-to-one feed→channel lineage.
        // Dedup (two feeds can blame the same span) preserving first-seen order.
        let mut origins: Vec<chl_parser::ast::Span> = Vec::new();
        for feed_ids in &fanin.sources {
            let feed_origins = feed_ids.iter().find_map(|&id| {
                resolve_origins_through_chain(provenance, id, &no_chain)
                    .filter(|spans| !spans.is_empty())
            });
            if let Some(spans) = feed_origins {
                for span in spans {
                    if !origins.contains(&span) {
                        origins.push(span);
                    }
                }
            } else if cfg!(any(debug_assertions, test)) {
                // Ordering guardrail: the whole feed resolved to nothing.
                // Check every id the feed named that is truly *unknown*
                // against the not-yet-applied record sets' targets. (An id
                // that resolved with empty spans is excluded: it answered,
                // and the answer was "no source" — applying more sets could
                // not change it.)
                for &id in feed_ids.iter() {
                    if provenance.resolve(id).is_none() {
                        pending.check_unresolved_origin(record_kind, id);
                    }
                }
            }
        }
        tags.push((fanin.target, Provenance::derived(Pass::Desugar, origins)));
    }
    for (id, prov) in tags {
        provenance.insert(id, prov);
    }
}

/// Sweep `expr` for every node id the table does not already know and tag it
/// `Synthetic { via: Desugar }` —
/// the pass's pure plumbing (floated lambdas, DI wrappers, contribution
/// records, projections, the untracked Case/Loop unions). Ensures no
/// synthesized node is left `None`; the inspector hides them unless
/// "show internals" is on.
///
/// (P)-preserved nodes already carry their lowered `Source` provenance, and the
/// fan-in / mono / inline tags already ran, so all of those are skipped. The
/// sweep relies on a single invariant to find only genuine plumbing: **every id
/// a prior boundary declared as a target is a table member by now** (the mono
/// remap inserts an entry for every fresh id, inline for every `Replicated`
/// copy, and `apply_desugar_fanins` for every target it doesn't skip-as-known),
/// so table membership alone excludes them — no separate already-tagged set is
/// threaded in.
///
/// # Known limitation: this catch-all silently *masks* id-preservation leaks
///
/// The sweep tags *whatever* is untagged, so it cannot tell a genuinely
/// synthesized plumbing node from an overlooked "(P)" 1:1 transform that
/// mistakenly rebuilt with `NodeId::fresh()` instead of preserving its id. Such
/// a leak should surface as a detectable `None`; instead the sweep confidently
/// (and wrongly) labels it `Synthetic { via: Desugar }`.
///
/// [`crate::ccl::node_recorder`]'s `NodeRecorder` is the structural fix: a pass
/// builds its output through the recorder's preserve/fuse/mint/replicate verbs,
/// so every construction is classified at the site that performs it and
/// `reconcile` catches a mismatch between declared intent and the tree actually
/// produced — no catch-all sweep, no silent mislabeling. `desugar_defers` has
/// not yet adopted it; until it does, this sweep remains the fallback for that
/// pass.
fn apply_desugar_synthetic_sweep(provenance: &mut ProvenanceTable, expr: &Expr) {
    let mut synth: Vec<NodeId> = Vec::new();
    collect_untagged_node_ids(expr, provenance, &mut synth);
    for id in synth {
        provenance.insert(id, Provenance::synthetic(Pass::Desugar, []));
    }
}

/// Collect every node id reachable from `expr` that the table does not already
/// know — the pass's synthesized plumbing. Every prior-boundary target is a
/// table member by now (see [`apply_desugar_synthetic_sweep`]), so
/// table-membership alone distinguishes plumbing from tagged nodes.
fn collect_untagged_node_ids(expr: &Expr, provenance: &ProvenanceTable, out: &mut Vec<NodeId>) {
    let id = expr.node_id();
    if provenance.resolve(id).is_none() {
        out.push(id);
    }
    expr.walk_children(|c| collect_untagged_node_ids(c, provenance, out));
}

/// Apply the inline pass's construction records into `provenance` at the inline
/// boundary — the composed-view entries for its `Replicated` fan-out copies
/// (and any future `Minted`).
///
/// Each copy mirrors its origin: the resolver maps an origin [`NodeId`] to the
/// source spans it reaches through the *already mono-tagged* table
/// ([`ProvenanceTable::origins`]), so a replica of a mono clone resolves through
/// the mono-tagged origin (which is why the mono remap is applied earlier, at
/// the infer boundary). A copy whose origin resolves to nothing degrades to
/// `Synthetic { via: Inline }`, exactly the mono graceful-degradation behavior.
///
/// `inlined` is the actual post-inline tree (the entries are keyed on its ids).
/// The recorder emits no `Minted` today, so no output walk is strictly needed —
/// but passing the real tree costs nothing and stays correct if inline ever
/// gains a `Minted`.
fn apply_inline_records(
    provenance: &mut ProvenanceTable,
    inline_rec: &crate::ccl::node_recorder::NodeRecorder,
    inlined: &Expr,
) {
    // Collect first (the resolver borrows `provenance`), then insert.
    let entries = inline_rec.to_provenance_entries(inlined, |id| {
        provenance
            .origins(id)
            .map(<[chl_parser::ast::Span]>::to_vec)
            .unwrap_or_default()
    });
    for (id, prov) in entries {
        provenance.insert(id, prov);
    }
}

/// Apply the `desugar_defers` record sets to the retained table at the
/// post-desugar boundary — the channel fan-ins — then run the fallback
/// `Synthetic` sweep over the post-desugar tree. Extracted so the application
/// sequence is testable against hand-built records.
///
/// The sweep skips the ids the earlier boundaries tagged (the mono remap's
/// fresh clone ids, the inline fan-out copy ids, and this pass's fan-in targets)
/// by table membership alone — every one of them is a table member by this
/// point, so the sweep's own `resolve(id).is_none()` check excludes them without
/// a separate already-tagged set (see [`apply_desugar_synthetic_sweep`]).
///
/// # The application order is derived from record data-dependencies
///
/// The rule (see "Application order is data-derived, never a frozen pass
/// order" in [`crate::ccl::node_recorder`]): the order is derived from the
/// current pipeline's record data-dependencies, never a frozen pass order. A
/// set applies only after every set that tags the ids its records name as
/// origins/sources. On the current pipeline (desugar runs *after*
/// inference / monomorphization / inline):
///
/// 1. **Mono remap** (infer boundary) — its `source` ids are pre-mono lowered
///    ids, already tagged by lowering; it depends on no other set.
/// 2. **Inline fan-out** (inline boundary) — each copy mirrors a post-mono
///    origin, so it resolves only after the mono remap has tagged it.
/// 3. **Desugar fan-ins** — a synthesized channel union's feed subtrees are
///    post-mono/post-inline content, so its `sources` can be mono-fresh /
///    inline-copy ids that resolve only once those sets have tagged them.
/// 4. **`Synthetic` sweep** — the undeclared fallback; tags whatever the tree
///    still doesn't resolve, so it runs last by construction.
///
/// [`PendingRecordTargets`] enforces the derivation structurally: an origin id
/// that fails to resolve but is a *later* set's target is an ordering
/// violation (loud in debug/test builds). That distinguishes "legitimately
/// unresolvable" from "asked too early" — the distinction whose absence let an
/// earlier inversion of steps 1 and 3 silently produce fan-in records with
/// empty origins after the pipeline reordered around them.
///
/// # Removed: the defer-mediating UDF wrapper-blame record set
///
/// `desugar_defers` once emitted a second set ("wrapper-blames") attributing the
/// synthesized `Lambda`/`Record`/`Compose`/`Var` chain a defer-mediating UDF's
/// function-class rewrite builds. That machinery was removed as unreachable:
/// `inline` beta-reduces every such UDF to its call sites *before* desugar runs,
/// so the function-class path never fires on the current pipeline (verified: the
/// recorder fired zero times across the whole suite). If that path is ever
/// reached again, its wrapper nodes simply fall to the `Synthetic` sweep —
/// graceful; proper attribution is re-derived at the `desugar_defers`
/// channelization rewrite via the [`crate::ccl::node_recorder`] recorder.
fn apply_desugar_records(
    provenance: &mut ProvenanceTable,
    desugar_prov: &desugar_defers::DesugarProvenance,
    desugared: &Expr,
    pending: &mut PendingRecordTargets,
) {
    pending.mark_applied(RECORDS_FANINS);
    apply_desugar_fanins(provenance, &desugar_prov.fanins, RECORDS_FANINS, pending);

    apply_desugar_synthetic_sweep(provenance, desugared);
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

    // Drain the provenance side table while it is still populated (lowering is
    // the only populator today). Retained on `CompiledProgram` so the inspector
    // and diagnostics can resolve lowered nodes back to source spans. `uniquify`
    // preserves every id in place; monomorphization freshens cloned ids and the
    // remap below tags each clone `Derived { via: Mono }`.
    let mut provenance = ctx.lowering_ctx().take_provenance();

    debug!("Lowered (pre-desugar):\n{}", symbolic(&expr));

    // α-uniquify all binders (Barendregt convention): every binding site gets
    // a globally fresh `Name` uid, so shadowing ceases to exist before any
    // pass that compares names. Must run before defer desugaring — desugar's
    // rewrites splice and rename terms under the assumption that distinct
    // binders are distinct names. (Desugar now runs after inference; see below.)
    expr = uniquify::run(expr);

    // Retain the pre-inference IR for the inspector's upstream pane before
    // `infer` mutates `expr` in place. This is the source-shaped, pre-mono,
    // still-hole-typed tree; its fan-out to the post-inference snapshot (mono
    // freshens clone ids inside `infer`) is carried by `mono_remap` below. Its
    // ids resolve against `provenance` (the pre-mono originals keyed by
    // lowering's `Source` tags). See `CompiledProgram::pre_inference_ir`.
    let pre_inference_ir = expr.clone();

    // Register every source (pre-registered + discovered during lowering) with
    // inference and operator-conversion now that the full source set is known.
    for (_name, source) in ctx.lowering_ctx().take_sources() {
        let name = source.borrow().get_id().to_string();
        let output_type = source.borrow().output_type();
        ctx.inference_ctx().register_source_type(
            &name,
            Type::Fun {
                name: None,
                domain: Box::new(Type::DataSource(name.clone())),
                codomain: Box::new(output_type),
            },
        );
        ctx.conversion_ctx().register_source(name, source);
    }

    debug!("Lowered:\n{}", symbolic(&expr));

    // Inference runs on the user-shaped tree — before desugar_defers — so type
    // errors are reported against the program the user wrote, not the
    // channelized rewrite. On failure, resolve each error's blame node to a
    // source span *here* — `provenance` is in scope and still holds the lowered
    // `Source` tags (this is the dual-use seam: the same `provenance.origins`
    // the inspector uses now feeds terminal + web diagnostics).
    // `take_infer_error_nodes` returns ids positionally aligned with the errors;
    // `.chain(repeat(None))` guards against any length skew.
    if let Err(errors) = infer(&mut expr, ctx.inference_ctx()) {
        let node_ids = ctx.inference_ctx().take_infer_error_nodes();
        return Err(errors
            .into_iter()
            .zip(node_ids.into_iter().chain(std::iter::repeat(None)))
            .map(|(error, node_id)| {
                let span = node_id
                    .and_then(|id| provenance.origins(id))
                    .and_then(|spans| spans.first().copied());
                CompileError::Infer { error, span }
            })
            .collect());
    }
    // Provenance records are applied per-boundary in pipeline dataflow order
    // (see `apply_desugar_records` for the full ordering + rationale): the mono
    // remap here at the infer boundary, the inline fan-out at the inline
    // boundary, and the desugar record sets + sweep at the desugar boundary. A
    // single `PendingRecordTargets` guardrail is threaded across all three so an
    // out-of-order application is caught even though each set's targets only
    // become known at its own stage.
    //
    // The `(fresh, source)` monomorphization remap is surfaced here (drained
    // from the inference context) and applied to the retained table *now*, so it
    // is in place before the inline boundary resolves a replica of a mono clone
    // through its origin.
    let mono_remap = ctx.inference_ctx().take_mono_remap();
    let mut pending = PendingRecordTargets::new();
    pending.declare(
        RECORDS_MONO_REMAP,
        mono_remap.iter().map(|&(fresh, _)| fresh),
    );
    pending.mark_applied(RECORDS_MONO_REMAP);
    apply_mono_remap(&mut provenance, &mono_remap, &pending);
    debug!("Inferred:\n{}", symbolic(&expr));
    debug!("Inferred (typed):\n{}", symbolic_typed(&expr));
    // Consistency wall between `infer` and `desugar_defers`. It is the relaxed
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

    // Enforce the second-class `Mut` discipline (design doc, "No aliasing:
    // `Mut` values are second-class") on the fully-typed, still-`Mut`-bearing
    // tree — after the consistency wall, before inlining. It needs the
    // pre-inline `Apply`/parameter structure (rule 1's argument check) and the
    // coalesced `.ty` slots and `user_annotation`s. Unlike the surrounding
    // `check_pre_desugar` walls (compiler-bug backstops), these are user
    // errors: aliasing or nesting a mutable reference.
    check_mut_discipline(&expr).map_err(|errs| errs.into_compile_errors())?;

    // Enforce that every `:=` / `+=` write targets a mutable store (a write is
    // never a shadowing rebind of an immutable). Post-inference so binder types
    // are resolved, post-`uniquify` so write targets carry their binder's
    // α-unique name — see `check_mut_write_targets`. (Currently satisfied by
    // construction, since lowering only emits `MutWrite` for registered stores;
    // it becomes load-bearing once lowering emits writes uniformly and drops the
    // registry — see src/ccl/design-mut-txn-feed.md, "Store-ness is the type".)
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
    // not run). Its node ids resolve against the final `provenance` table (the
    // Source + mono + desugar tags applied above/below all key off ids that
    // survive into this pre-inline tree). `ast` (`join_planned`) is the *wrong*
    // tree for a source view — `lambda_elim`/`planning` re-mint ids (resolve to
    // `None`) and produce execution shape. See `CompiledProgram::post_inference_ir`.
    let post_inference_ir = expr.clone();

    let (inlined, inline_rec) = inline::inline_with_records(expr);
    expr = inlined;
    // Boundary check: inline's construction records must fully explain the
    // output tree (every output id preserved/replicated/minted, every dropped
    // input id declared). A leak means the pass mutated identity without
    // recording it. Debug-gated — the reconcile walk is not free.
    debug_assert!(
        inline_rec.reconcile(&expr).is_ok(),
        "inline: unreconciled provenance: {:?}",
        inline_rec.reconcile(&expr).err()
    );
    // Apply the inline pass's construction records at its boundary, over the
    // actual inlined tree (`expr`). Its `Replicated` fan-out copies resolve
    // `Derived { via: Inline }` through the mono-tagged origins applied above,
    // instead of falling to the desugar `Synthetic` sweep. The
    // `(copy, origin)` stage remap is retained on `CompiledProgram::pass_remaps`
    // (keyed `Pass::Inline`) for the multi-pane inspector's stage-adjacency.
    let inline_remap = inline_rec.stage_remap();
    pending.declare(RECORDS_INLINE, inline_remap.iter().map(|&(copy, _)| copy));
    pending.mark_applied(RECORDS_INLINE);
    apply_inline_records(&mut provenance, &inline_rec, &expr);
    // Id-uniqueness tripwire at the inline boundary (after inline's dedup sweep).
    // Order-agnostic tree invariant; see `assert_unique_node_ids`.
    assert_unique_node_ids(&expr, "post-inline");
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
    // writer of a `Mut[_, Txn]` store into a `get_prev_txn`-guarded `LetRec`
    // (histories + commit records over the commit domain), which
    // `letrec_phase::recognize` destructures into the `Transact{…, Txn}` node
    // op-conversion compiles to the commit engine — unifying the transaction and
    // induction paths on one `LetRec` + recognition representation. Runs *before*
    // `letrec_phase` so the induction phase never sees a transaction loop. See
    // src/ccl/design-mut-txn-feed.md.
    //
    // Store identity is the `Mut[_, Txn]` type on the α-unique binding, gathered
    // from the *inlined, typed* tree — so a cross-function writer's stores (its
    // `transfer(a, b)` writes already beta-reduced to name `a`/`b`) are seen, and
    // an unrelated local merely spelled like a register is not (its binder is a
    // distinct `Name`). This replaces the lowering-time base-name registry.
    let txn_stores = transact_phase::collect_txn_stores(&expr);
    // A transactional writer reaching a `with begin():` block via a function call
    // is a nested transaction — the callee's inlined `For` would otherwise be
    // silently absorbed into the outer block's read-your-writes env, dropping its
    // commit. Reject it before the phase strips the sites.
    transact_phase::check_no_nested_transactions(&expr, &txn_stores)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    expr = transact_phase::run(expr, &txn_stores);
    assert_unique_node_ids(&expr, "post-transact");
    debug!("Transact phase CCL:\n{}", symbolic(&expr));
    check_pre_desugar(&expr).expect("transact phase produced an inconsistent tree");

    // The unified letrec phase: direct-mirror mutation loops (`For` /
    // `MutWrite`) become guarded `LetRec` groups — mutable histories over
    // the induction domain, per src/ccl/design-mut-txn-feed.md. Runs after
    // inlining (so cross-function writers land at their call sites) and
    // *before* desugar_defers, so a per-iteration feed inside a loop is
    // hoisted to an ordinary feed of the loop's history for desugar to route.
    // The tree still carries Defer/Feed here, so the walls are the relaxed
    // pre-desugar check.
    let phase_out = letrec_phase::run(expr);
    assert_unique_node_ids(&phase_out, "post-letrec-run");
    debug!("Letrec phase CCL:\n{}", symbolic(&phase_out));
    check_pre_desugar(&phase_out).expect("letrec phase produced an inconsistent tree");

    // Recognition: lower each guarded group onto the domain-parameterized
    // `Transact` carrier (a `get_prev_txn` transaction group → `Transact{Txn}`;
    // a `get_prev_seq` induction group → `Transact{iteration extent}`) so
    // planning and operator conversion pick the engine on the domain. See the
    // `letrec_phase` module docs.
    let recognized = letrec_phase::recognize(phase_out);
    assert_unique_node_ids(&recognized, "post-letrec-recognize");
    debug!("Letrec recognized CCL:\n{}", symbolic(&recognized));
    check_pre_desugar(&recognized).expect("letrec recognition produced an inconsistent tree");

    // Desugar Defer/Feed/Define after the letrec phase: every `let d = Defer in
    // body` is rewritten so the body publishes its contribution to `d` via a
    // `Record({result, to_d})` at its terminal, with the defer-bind site
    // consuming the `to_d` projection. Running after the phase lets a loop's
    // hoisted in-loop feed be routed here as an ordinary channel contribution.
    // After this, no Defer/Feed/Define nodes — and no `Feed`/`Infer` types —
    // remain: the pass is type-preserving (it ends with a retype synthesis),
    // and the strict `typecheck` below is the release-visible enforcement.
    // `desugar_defers` preserves lowered/mono ids at its (P) 1:1 sites and
    // carries the surviving binding's id at (M) merges, so the retained table
    // stays valid; it also surfaces fan-in records for its synthesized channel
    // unions, tagged below over the post-desugar tree.
    let desugar_prov;
    let mut desugared;
    // The post-desugar id-uniqueness tripwire is GATED to defer-free inputs:
    // `desugar_substitute` legitimately leaves duplicate ids on defer-bearing
    // programs (the `Defer`/`Feed`/`Define` channelization) until the desugar
    // channelization rewrite lands — the same exemption `is_pure_structural` /
    // `run_with_provenance`'s preservation assert already carve out. On a
    // defer-free input desugar is a pure 1:1 transform, so uniqueness must hold.
    let desugar_input_defer_free = !desugar_defers::contains_defer_nodes(&recognized);
    (desugared, desugar_prov) =
        desugar_defers::run_with_provenance(recognized, /* input_typed= */ true).errs()?;
    if desugar_input_defer_free {
        assert_unique_node_ids(&desugared, "post-desugar (defer-free input)");
    }
    debug!("Desugared:\n{}", symbolic(&desugared));
    typecheck(&desugared).expect("desugar_defers produced an ill-typed tree");

    // Apply the `desugar_defers` plumbing tags on the retained table now, over
    // the post-desugar tree (desugar runs after inference on this pipeline, so
    // its provenance records are only available here). The mono remap (infer
    // boundary) and inline fan-out (inline boundary) already landed; the desugar
    // records data-depend on them, so they slot last before the sweep. See
    // `apply_desugar_records` for the full application order and its rationale.
    pending.declare_fanins(RECORDS_FANINS, &desugar_prov.fanins);
    apply_desugar_records(&mut provenance, &desugar_prov, &desugared, &mut pending);

    // Retain the post-desugar tree + its own provenance projection for the
    // inspector's downstream pane. On the post-inference desugar order this
    // snapshot is *downstream* of `post_inference_ir` (post-inline/transact/
    // letrec/desugar); see the doc comment on `post_desugar_ir`.
    let post_desugar_ir = desugared.clone();

    // Live cross-endpoint reads: rewrite a read-only reply that broadcasts a
    // live store's terminal read over a request loop into an outer-indexed as-of
    // join, *before* lambda elimination — so a computed reply (`resp << store +
    // 1`) stays a lambda the elim pass point-frees, rather than a point-free
    // `const` a planning-time recognizer would have to reject. See
    // `transact_phase::rewrite_live_reads`.
    transact_phase::rewrite_live_reads(&mut desugared);
    // A live read the rewrite could not resolve (a multi-register reply) would
    // otherwise compile to a never-terminating `ExtractLast` — reject it with a
    // clear error rather than hang the endpoint. See `check_live_reads_resolved`.
    transact_phase::check_live_reads_resolved(&desugared)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    typecheck(&desugared).expect("live-read rewrite produced an ill-typed tree");

    let lambda_elim = lambda_elim::run(desugared).errs()?;
    debug!("λ-eliminated CCL:\n{}", symbolic(&lambda_elim));
    debug!("λ-eliminated typed CCL:\n{}", symbolic_typed(&lambda_elim));

    // `typecheck` enforces hole-freeness as its first phase, so this call
    // alone covers both checks.
    typecheck(&lambda_elim).expect("type error after lambda elimination");

    let join_planned = planning::run(lambda_elim);
    debug!(
        "Join-planned CCL:\n{} : {}",
        symbolic(&join_planned),
        join_planned.ty
    );
    debug!("Join-planned CCL:\n{}", symbolic_typed(&join_planned));

    // Planning is the one pass that introduces `iterate` / `restrict` /
    // `Compose` staging, so re-checking its output catches a malformed tile
    // graph an adjacency that doesn't chain would otherwise hide. Planning
    // surfaces each iterated / join-satisfying extent on its producer's
    // codomain (`refine_codomain` / `set_codomain`) and the strict checker
    // matches the fresh refinement witnesses it mints by structural predicate
    // equality, so the staging shapes now validate without re-blinding the
    // check or peeling cast refinements.
    typecheck(&join_planned).expect("type error after join planning");

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
        provenance,
        pre_inference_ir,
        post_inference_ir,
        post_desugar_ir,
        pass_remaps: vec![(Pass::Mono, mono_remap), (Pass::Inline, inline_remap)],
        source_ast: module,
        source: code.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compile a program for provenance inspection, returning the whole
    /// [`CompiledProgram`].
    fn compile_ok(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        compile_program(&mut ctx, code, consumer).expect("program compiles")
    }

    /// Provenance census of a stage tree against its [`ProvenanceTable`]: a count
    /// of every **main-tree** node (the `walk_children` node-set) by resolution
    /// category — `Source`, `Derived(<pass>)`, `Synthetic(<pass>)`, or
    /// `unresolved` (no table entry). A `BTreeMap` so the pinned rows are
    /// order-stable and diff cleanly.
    ///
    /// This is the guardrail that converts a future pass churning ids without
    /// recording into a *forced visible diff*: it shows up as `Synthetic` /
    /// `unresolved` inflation and fails the pinned row.
    fn provenance_census(
        stage_ir: &Expr,
        table: &ProvenanceTable,
    ) -> std::collections::BTreeMap<String, usize> {
        use crate::ccl::provenance::Derivation;
        fn label(table: &ProvenanceTable, id: NodeId) -> String {
            match table.resolve(id) {
                None => "unresolved".to_string(),
                Some(p) => match p.kind {
                    Derivation::Source => "Source".to_string(),
                    Derivation::Derived { via } => format!("Derived({via:?})"),
                    Derivation::Synthetic { via } => format!("Synthetic({via:?})"),
                },
            }
        }
        fn walk(
            e: &Expr,
            table: &ProvenanceTable,
            out: &mut std::collections::BTreeMap<String, usize>,
        ) {
            *out.entry(label(table, e.node_id())).or_default() += 1;
            e.walk_children(|c| walk(c, table, out));
        }
        let mut out = std::collections::BTreeMap::new();
        walk(stage_ir, table, &mut out);
        out
    }

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

    /// Apply the mono remap and the desugar record sets through a single
    /// threaded [`PendingRecordTargets`], matching the pipeline's pre-inline →
    /// desugar sequence with no inline records in play. The RT-2 ordering tests
    /// feed it hand-built records (they exercise the mono → desugar dataflow
    /// dependency, not the inline boundary).
    fn apply_records_through_desugar(
        provenance: &mut ProvenanceTable,
        mono_remap: &[(NodeId, NodeId)],
        desugar_prov: &desugar_defers::DesugarProvenance,
        desugared: &Expr,
    ) {
        let mut pending = PendingRecordTargets::new();
        pending.declare(RECORDS_MONO_REMAP, mono_remap.iter().map(|&(f, _)| f));
        pending.declare_fanins(RECORDS_FANINS, &desugar_prov.fanins);
        pending.mark_applied(RECORDS_MONO_REMAP);
        apply_mono_remap(provenance, mono_remap, &pending);
        apply_desugar_records(provenance, desugar_prov, desugared, &mut pending);
    }

    /// RT-4c: the provenance-census ratchet. Pins the exact per-category node
    /// counts for a corpus of representative programs at each retained stage. A
    /// future pass that churns ids without recording shows up as `Synthetic` /
    /// `unresolved` inflation and fails the matching row; a deliberate provenance
    /// improvement (e.g. a desugar lift-preserve that turns a swept node into a
    /// tracked one) *moves* a row, and that diff is itself the commit's
    /// provenance-impact statement.
    ///
    /// The txn/loop rows demonstrate the gap-4 state: their post-desugar trees are
    /// heavy `Synthetic{Desugar}` (the transact/letrec scaffolding and freshened
    /// `subst_env` copies are swept by desugar's fallback — unattributed until the
    /// transact/letrec recorders land, a documented follow-up). These counts are
    /// **structural** (nodes counted by tree position), so they are invariant to
    /// the id-uniqueness fix itself — the fail-before evidence for the fixes lives
    /// in RT-4a/RT-4b (id-uniqueness); this test's job is the forward ratchet and
    /// pinning the attribution shape.
    ///
    /// # Re-bless procedure
    /// Run `cargo test -q --lib census_ratchet -- --nocapture` (or read the assert
    /// diff on failure), confirm the delta is an *intended* provenance change for
    /// the commit in flight, then update the affected row's expected map here.
    #[test]
    fn census_ratchet() {
        use std::collections::BTreeMap;
        /// A per-stage census (category → count).
        type Census = BTreeMap<String, usize>;
        /// One corpus row: program name, source, and expected census for the
        /// three retained stages (pre-inference, post-inference, post-desugar).
        type Row = (&'static str, &'static str, [Census; 3]);
        fn bt(pairs: &[(&str, usize)]) -> Census {
            pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
        }

        let cases: &[Row] = &[
            (
                "arithmetic",
                "x = 1 + 2\nx\n",
                [
                    bt(&[("Source", 5)]),
                    bt(&[("Source", 5)]),
                    bt(&[("Source", 5)]),
                ],
            ),
            (
                "polymorphic",
                "dup = lambda x: (x, x)\n(dup(1), dup(2 == 2))\n",
                [
                    bt(&[("Source", 12), ("unresolved", 2)]),
                    bt(&[("Derived(Mono)", 10), ("Source", 7), ("unresolved", 2)]),
                    bt(&[("Derived(Inline)", 4), ("Derived(Mono)", 2), ("Source", 5)]),
                ],
            ),
            (
                "udf_fanout",
                "def inc(n):\n    n + 1\na = inc(1)\nb = inc(2)\na + b\n",
                [
                    bt(&[("Source", 14), ("unresolved", 2)]),
                    bt(&[("Derived(Mono)", 5), ("Source", 9), ("unresolved", 2)]),
                    bt(&[("Derived(Inline)", 2), ("Derived(Mono)", 2), ("Source", 7)]),
                ],
            ),
            (
                "mutation_loop",
                "x := 0\nfor i in [1, 2, 3]:\n    x += i\nx\n",
                [
                    bt(&[("Source", 7), ("Synthetic(Desugar)", 2), ("unresolved", 6)]),
                    bt(&[("Source", 7), ("Synthetic(Desugar)", 2), ("unresolved", 6)]),
                    bt(&[("Source", 7), ("Synthetic(Desugar)", 28)]),
                ],
            ),
            (
                "txn_begin",
                "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [10, 20, 30]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
                [
                    bt(&[("Source", 13), ("unresolved", 12)]),
                    bt(&[("Source", 13), ("unresolved", 12)]),
                    bt(&[("Source", 13), ("Synthetic(Desugar)", 46)]),
                ],
            ),
        ];

        for (name, code, expected) in cases {
            let p = compile_ok(code);
            let actual = [
                provenance_census(&p.pre_inference_ir, &p.provenance),
                provenance_census(&p.post_inference_ir, &p.provenance),
                provenance_census(&p.post_desugar_ir, &p.provenance),
            ];
            let stages = ["pre_inference_ir", "post_inference_ir", "post_desugar_ir"];
            for i in 0..3 {
                assert_eq!(
                    actual[i], expected[i],
                    "census drift for `{name}` at {}: re-bless if intended (see the \
                     re-bless procedure on this test)",
                    stages[i]
                );
            }
        }
    }

    #[test]
    fn rendered_errors_have_exact_format() {
        let code = "\
x = 1 +
y = {\"a\": 1}
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
 2 │ y = {\"a\": 1}
   │     ────┬───
   │         ╰───── dict literals (with non-identifier keys) are not yet supported
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
    /// through `provenance.origins` to a `Some` span over the offending
    /// expression.
    ///
    /// (Note: `1 + "a"` does *not* exercise this path — the `Int`/`String`
    /// collision there surfaces in pass-2 coalesce as `IncompatibleBounds`,
    /// which has no single blame node and renders as `node_id: None`.)
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
        // newline); statement 2 contains a dict literal with non-identifier
        // keys, which lowering rejects. We must see both stages' errors in
        // the result.
        let code = "\
x = (1 +)
y = {\"a\": 1}
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
x = {\"a\": 1}
y = {\"b\": 2}
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

    /// Monomorphization end-to-end: a generalized definition used at two
    /// distinct types is monomorphized into two specializations. Each
    /// specialization's cloned nodes get fresh `NodeId`s (so they no longer
    /// collide on the original definition's ids), and the provenance table
    /// tags them `Derived { via: Mono }` with `origins` resolving —
    /// transitively through the remap — back to the original lowered node's
    /// source span. This depends on `desugar_defers` preserving lowered ids at
    /// its (P) sites: the lowering-populated provenance table survives to
    /// inference time, so the mono remap's `source` ids resolve to real
    /// lowered nodes.
    #[test]
    fn monomorphization_tags_specializations_with_mono_provenance() {
        use crate::ccl::provenance::{Derivation, Pass};

        // `dup` is bound to a polymorphic lambda and applied at Int and String,
        // forcing two specializations. A non-trivial body (`(x, x)`) keeps the
        // definition from being beta-reduced away before inference (a plain
        // `lambda x: x` is inlined during lowering, leaving nothing to
        // monomorphize). The trailing tuple is the program's value.
        let code = "\
dup = lambda x: (x, x)
(dup(1), dup(\"a\"))
";
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("compiles");
        let table = &compiled.provenance;

        // The `dup = lambda x: (x, x)` statement is the first line; its nodes
        // were tagged `Source` within that span by lowering. The mono remap
        // carries those origins onto the freshened specialization clones.
        let def_line_end = code.find('\n').expect("two-line program");

        // At least one node was tagged `Derived { via: Mono }` — the
        // specialization clones — and every such node's origins trace back to
        // the original `id` definition's source span (within the first line).
        let mono: Vec<&Provenance> = table
            .iter_provenances()
            .filter(|p| matches!(p.kind, Derivation::Derived { via: Pass::Mono }))
            .collect();
        assert!(
            !mono.is_empty(),
            "monomorphization must tag specialization clones Derived{{via: Mono}}"
        );
        for p in &mono {
            assert!(
                !p.origins.is_empty(),
                "a mono specialization resolves to its original def's source span(s)"
            );
            for span in &p.origins {
                assert!(
                    span.end <= def_line_end,
                    "mono origin span {span:?} traces back to the `id` definition \
                     (within the first line, bytes 0..{def_line_end})"
                );
            }
        }
    }

    /// RT-3a — the inline recorder's `Replicated` copies resolve
    /// `Derived { via: Inline }` with real origins (not swept
    /// `Synthetic { via: Desugar }`).
    ///
    /// A scalar UDF called at two sites *at the same type* fans its body out
    /// during inlining (one specialization from mono, N copies from inline).
    /// Each freshened body copy is a `Replicated` node whose origin is the
    /// original body node — so it must resolve to that body's source span,
    /// tagged `Derived { via: Inline }`.
    ///
    /// Without the inline recorder, the copy ids would be unknown to the table
    /// and fall to the desugar `Synthetic` sweep, resolving
    /// `Synthetic { via: Desugar }` with empty origins instead.
    #[test]
    fn rt3a_inline_fanout_copies_resolve_derived_via_inline() {
        use crate::ccl::provenance::{Derivation, Pass};

        // `add1` is a scalar UDF (Int → Int, non-iterable domain → inlined),
        // called at two sites both at `Int`, so mono produces ONE specialization
        // and the two-site fan-out is inline's. The body `x + 1` is duplicated:
        // one copy preserves the input ids, the other is freshened (Replicated).
        let code = "\
add1 = lambda x: x + 1
a = add1(10)
b = add1(20)
a + b
";
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("compiles");

        fn collect(expr: &Expr, acc: &mut std::collections::HashSet<NodeId>) {
            acc.insert(expr.node_id());
            expr.walk_children(|c| collect(c, acc));
        }
        let mut pre = std::collections::HashSet::new();
        collect(&compiled.post_inference_ir, &mut pre);
        let mut post = std::collections::HashSet::new();
        collect(&compiled.post_desugar_ir, &mut post);

        // Candidate inline copies: ids that appear post-desugar but not
        // post-inference (the freshened fan-out copies; on this defer-free
        // program transact/letrec/desugar mint nothing else of note).
        let new_ids: Vec<NodeId> = post.difference(&pre).copied().collect();
        assert!(
            !new_ids.is_empty(),
            "the two-site UDF must fan out into fresh post-desugar ids"
        );

        let table = &compiled.provenance;
        let derived_inline: Vec<NodeId> = new_ids
            .iter()
            .copied()
            .filter(|id| {
                table.resolve(*id).is_some_and(|p| {
                    matches!(p.kind, Derivation::Derived { via: Pass::Inline })
                        && !p.origins.is_empty()
                })
            })
            .collect();
        assert!(
            !derived_inline.is_empty(),
            "at least one inline fan-out copy must resolve Derived{{via: Inline}} \
             with non-empty origins; new ids resolved as: {:?}",
            new_ids
                .iter()
                .map(|id| (*id, table.resolve(*id).map(|p| p.kind)))
                .collect::<Vec<_>>()
        );

        // Mislabel regression guard: no inline fan-out copy is swept
        // `Synthetic { via: Desugar }` (the pre-fix behavior).
        for id in &new_ids {
            if let Some(p) = table.resolve(*id) {
                assert_ne!(
                    p.kind,
                    Derivation::Synthetic { via: Pass::Desugar },
                    "inline fan-out copy {id:?} was mislabeled Synthetic{{via: Desugar}}"
                );
            }
        }
    }

    /// `desugar_defers` tags its channelized plumbing: a defer program compiles
    /// end-to-end and the retained provenance table carries
    /// `Synthetic { via: Desugar }` entries (the channel/loop plumbing the
    /// generic sweep tags). Proves the desugar tagging lands in the real
    /// pipeline. (The multi-origin `Derived { via: Desugar }` fan-in mapping is
    /// covered at the unit level by
    /// `desugar_fanin_resolves_to_multi_origin_derived` and the desugar pass's
    /// own `desugar_emits_fanin_record_for_multi_feed_channel`.)
    #[test]
    fn desugar_tags_channelized_plumbing_with_desugar_provenance() {
        use crate::ccl::provenance::{Derivation, Pass};

        // A for-loop feed: lowering/desugar synthesize the loop channel +
        // per-scope `Record` plumbing, none of which lowering tagged.
        let code = "\
x = defer()
for i in [1, 2, 3]:
  x << i
x
";
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("compiles");
        let table = &compiled.provenance;

        let synthetic = table
            .iter_provenances()
            .filter(|p| matches!(p.kind, Derivation::Synthetic { via: Pass::Desugar }))
            .count();
        assert!(
            synthetic >= 1,
            "desugar plumbing must be tagged Synthetic{{via: Desugar}}; \
             table: {:?}",
            table.iter_provenances().collect::<Vec<_>>()
        );
    }

    // There is no defer-mediating UDF wrapper-blame record machinery: `inline`
    // beta-reduces every defer-mediating UDF to its call sites *before* desugar
    // runs, so no non-`Plain` lambda `Let` ever reaches desugar for a
    // wrapper-blame recorder to fire on (cf. the `#[ignore]`d
    // `generator_coverage_maps_wrapper_chain`, which pins that gap). This is why
    // the RT-2a/RT-2a′ ordering tests below cover only the *fan-in* record set
    // (`DesugarFanin`, its applier, and the mono→desugar data dependency) rather
    // than a separate wrapper case. Proper wrapper attribution is re-derived at
    // the `desugar_defers` channelization rewrite via the `node_recorder`
    // recorder. The `PendingRecordTargets` assertion turns every suite compile
    // into an ordering probe.

    /// RT-2a — the record-application order follows the pipeline's dataflow:
    /// a desugar fan-in whose `sources` contain a **mono-fresh** id (desugar
    /// runs after inference/monomorphization, so its records can name clone ids)
    /// resolves through the mono remap. Table `{A: Source(s)}`, mono remap
    /// `[(B, A)]`, fan-in `{target: T, sources: [[B]]}` — after
    /// `apply_records_through_desugar`, `T` must be `Derived { via: Desugar }`
    /// with origins `[s]`.
    ///
    /// Under the pre-fix order (fan-ins before the mono remap) `B` was unknown
    /// when the record applied, so `T` got *empty* origins — the gap-2 inversion
    /// this test pins. It also proves the ordering assertion inside the applier
    /// stays silent on the correct order (RT-2a′ case i).
    #[test]
    fn fanin_with_mono_fresh_source_resolves_through_mono_remap() {
        use crate::ccl::desugar_defers::{DesugarFanin, DesugarProvenance};
        use crate::ccl::provenance::{Derivation, NodeId, Pass};

        let a = NodeId::fresh(); // pre-mono original, Source-tagged by lowering
        let b = NodeId::fresh(); // mono-fresh clone of `a`
        let t = NodeId::fresh(); // desugar-synthesized fan-in blaming `b`
        let s = chl_parser::ast::Span::new(0, 4);
        let mut table = ProvenanceTable::new();
        table.insert(a, Provenance::source(s));

        let mono_remap = [(b, a)];
        let desugar_prov = DesugarProvenance {
            fanins: vec![DesugarFanin {
                target: t,
                sources: vec![vec![b].into()],
            }],
        };
        // A trivial post-desugar tree whose only node is the fan-in target,
        // so the trailing Synthetic sweep has nothing extra to tag.
        let tree = Expr::lit(crate::ccl::Lit::Unit).with_node_id(t);

        apply_records_through_desugar(&mut table, &mono_remap, &desugar_prov, &tree);

        let prov = table.resolve(t).expect("fan-in target tagged");
        assert_eq!(prov.kind, Derivation::Derived { via: Pass::Desugar });
        assert_eq!(
            prov.origins,
            vec![s],
            "the fan-in resolves its mono-fresh source through the mono \
             remap to the original's span"
        );
    }

    /// RT-2a′ (i/ii) — the record-dependency assertion fires on a deliberately
    /// mis-ordered application: the same records as RT-2a, but the fan-ins are
    /// applied while the mono remap — which owns `B` as a target — is still
    /// pending. (Silence on the *correct* order is proven by RT-2a above, which
    /// routes the same records through `apply_records_through_desugar`.)
    #[test]
    #[should_panic(expected = "provenance record ordering violation")]
    fn dependency_assertion_fires_on_misordered_application() {
        use crate::ccl::desugar_defers::{DesugarFanin, DesugarProvenance};
        use crate::ccl::provenance::NodeId;

        let a = NodeId::fresh();
        let b = NodeId::fresh();
        let t = NodeId::fresh();
        let mut table = ProvenanceTable::new();
        table.insert(a, Provenance::source(chl_parser::ast::Span::new(0, 4)));

        let mono_remap = [(b, a)];
        let desugar_prov = DesugarProvenance {
            fanins: vec![DesugarFanin {
                target: t,
                sources: vec![vec![b].into()],
            }],
        };

        let mut pending = PendingRecordTargets::new();
        pending.declare(RECORDS_MONO_REMAP, mono_remap.iter().map(|&(f, _)| f));
        pending.declare_fanins(RECORDS_FANINS, &desugar_prov.fanins);
        // Deliberately wrong: fan-ins first, mono remap still pending.
        pending.mark_applied(RECORDS_FANINS);
        apply_desugar_fanins(&mut table, &desugar_prov.fanins, RECORDS_FANINS, &pending);
    }

    /// RT-2a′ (iii) — a genuinely-unknown origin id (present in no declared
    /// set's targets and not in the table) keeps the graceful path: the record
    /// applies with empty origins and the dependency assertion stays silent.
    #[test]
    fn dependency_assertion_silent_on_genuinely_unknown_origin() {
        use crate::ccl::desugar_defers::{DesugarFanin, DesugarProvenance};
        use crate::ccl::provenance::{Derivation, NodeId, Pass};

        let stray = NodeId::fresh(); // unknown everywhere
        let t = NodeId::fresh();
        let desugar_prov = DesugarProvenance {
            fanins: vec![DesugarFanin {
                target: t,
                sources: vec![vec![stray].into()],
            }],
        };
        let tree = Expr::lit(crate::ccl::Lit::Unit).with_node_id(t);
        let mut table = ProvenanceTable::new();

        apply_records_through_desugar(&mut table, &[], &desugar_prov, &tree);

        let prov = table
            .resolve(t)
            .expect("target tagged despite unknown origin");
        assert_eq!(prov.kind, Derivation::Derived { via: Pass::Desugar });
        assert!(
            prov.origins.is_empty(),
            "graceful degradation: an unknown origin yields empty origins, not a panic"
        );
    }

    /// Unit-level proof that a `desugar_defers` fan-in record resolves to a
    /// multi-origin `Derived { via: Desugar }`: given a table where two source
    /// nodes carry `Source` spans, a fan-in over them tags its target with both
    /// spans (the many-to-one feed→channel lineage, D2).
    #[test]
    fn desugar_fanin_resolves_to_multi_origin_derived() {
        use crate::ccl::desugar_defers::DesugarFanin;
        use crate::ccl::provenance::{Derivation, NodeId, Pass};

        // Each feed's pre-order id list leads with an untagged wrapper id
        // (mirroring the `λ __unused → V` / `Compose` wrappers desugar
        // synthesizes) followed by the source-tagged feed-value id; the
        // resolver must skip the wrapper and take the first that resolves.
        let wrap_a = NodeId::fresh();
        let src_a = NodeId::fresh();
        let wrap_b = NodeId::fresh();
        let src_b = NodeId::fresh();
        let target = NodeId::fresh();
        let mut table = ProvenanceTable::new();
        table.insert(src_a, Provenance::source(chl_parser::ast::Span::new(0, 4)));
        table.insert(src_b, Provenance::source(chl_parser::ast::Span::new(5, 9)));

        // A trivial expr tree whose only node is the fan-in target, so the
        // Synthetic sweep has nothing extra to do.
        let expr = Expr::lit(crate::ccl::Lit::Unit).with_node_id(target);
        let fanins = [DesugarFanin {
            target,
            sources: vec![vec![wrap_a, src_a].into(), vec![wrap_b, src_b].into()],
        }];
        // No other record sets in play: declare none pending.
        let mut pending = PendingRecordTargets::new();
        pending.mark_applied(RECORDS_FANINS);
        apply_desugar_fanins(&mut table, &fanins, RECORDS_FANINS, &pending);
        // The applier makes `target` a table member; the sweep skips it by table
        // membership. The trivial tree's only node is the fan-in target, so the
        // sweep is a no-op here (kept for parity with the real pipeline ordering).
        apply_desugar_synthetic_sweep(&mut table, &expr);

        let prov = table.resolve(target).expect("fan-in target tagged");
        assert_eq!(prov.kind, Derivation::Derived { via: Pass::Desugar });
        assert_eq!(
            prov.origins,
            vec![
                chl_parser::ast::Span::new(0, 4),
                chl_parser::ast::Span::new(5, 9)
            ],
            "the fan-in resolves to both feed values' source spans (many-to-one)"
        );
    }
}

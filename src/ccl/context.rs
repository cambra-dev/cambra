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
            check_pre_channelize, infer, typecheck,
        },
        inline, lambda_elim,
        lower::{LoweringContext, LoweringError, lower_stmts},
        mut_elim, planning,
        provenance::{
            Leak, LoweringSession, PassScope, ProvenanceMap, ProvenanceTable, SourceProjection,
            TableSession, collapse, collapse_lowering,
        },
        provenance::{NodeId, Pass},
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
    /// Defer/Feed/Define channelization rejected the program (e.g. a defer
    /// binding with no feeds, mixed `<<`/`<<=` on the same handle, or a
    /// `<<=` inside a non-top-level scope).
    ///
    /// Channelization runs *after* inference (so type errors report against
    /// the user's program shape); a program with both a type error and a
    /// structural defer error therefore surfaces only the type error
    /// first.
    ChannelizeDefers(channelize::DeferError),
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
            CompileError::ChannelizeDefers(e) => {
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
        Self::ChannelizeDefers(e)
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
        vec![CompileError::ChannelizeDefers(self)]
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
    /// [`SourceAttribution`](crate::ccl::provenance::SourceAttribution) folded from
    /// lowering's [`LoweringLog`](crate::ccl::provenance::LoweringLog). Every entry
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
    /// [`collapse_lowering`](crate::ccl::provenance::collapse_lowering) at the
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
    /// The post-channelize IR snapshot — the inspector's **downstream** pane, one
    /// pipeline stage *below* [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// This is `expr` captured **right after `channelize`** (which now runs
    /// after `infer`/`inline`/`transact`/`letrec`): fully typed and structurally
    /// final for the source view — no Defer/Feed/Define nodes remain, and the
    /// channelization artifacts (`Compose` wrapper chains, `Copair`
    /// fan-ins) are present. Because monomorphization ran earlier (inside
    /// `infer`), this tree is post-mono like [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// Every id preserved through inline/transact/letrec/channelize is shared with
    /// [`post_inference_ir`](Self::post_inference_ir).
    pub post_channelize_ir: Expr,
    /// The compile's provenance record: `NodeId → { parents, blame, rule }`, one
    /// row per node a pass produced, written by the recorder as those passes run
    /// ([`crate::ccl::provenance`]).
    ///
    /// One table covers the whole compile, because a row's key is a
    /// process-unique `NodeId` and needs no pass set to disambiguate it; a row's
    /// `via` is what a pane relation restricts by. The passes that record are
    /// [`Pass::Mono`] (everything monomorphization mints inside `infer`, which
    /// bridges the pre-inference ⇄ post-inference panes) and [`Pass::Inline`],
    /// [`Pass::Transact`], [`Pass::Letrec`], [`Pass::Channelize`] (the four passes
    /// between the post-inference and post-channelize snapshots) — see
    /// [`MONO_PASSES`] and [`CHANNELIZE_PASSES`].
    ///
    /// Rows exist only for nodes a recording produced, so an untouched node has
    /// none — it was never rewritten. Refinement-predicate interiors are rows
    /// like any other: `collect_tree_ids` enumerates them, so the fold must
    /// explain them, and `PredMemo::rebuild` records a derived predicate against
    /// the one it was built from. What is not recorded is planning **raising** a
    /// predicate back into the main tree; see `design/provenance.md`, "Known
    /// prerequisites for panes past `post-channelize`".
    ///
    /// Empty when capture is switched off — no pass scope is opened then, so
    /// every flush is a no-op — see [`provenance_capture_enabled`]. This is the
    /// authoritative provenance surface:
    /// [`materialize_panes`](Self::materialize_panes) folds it for each pane
    /// relation.
    // Consumed by `materialize_panes` and the inspector model; the compiler
    // itself never reads it.
    #[allow(dead_code)]
    pub(crate) provenance_table: ProvenanceTable,
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

    /// Fold [`provenance_table`](Self::provenance_table) across the two pane relations into
    /// the per-pane [`SourceProjection`]s, the pane-pair [`ProvenanceMap`]s, and
    /// each relation's [`Leak`]s. Cold path (snapshot-serve only), never called
    /// by [`compile_program`]:
    ///
    /// * pre-inference pane = the lowering projection (`uniquify` preserves every
    ///   id in place, so lowering's keys are still the pane's keys);
    /// * post-inference pane = fold the [`MONO_PASSES`] rows against the
    ///   pre-inference pane;
    /// * post-channelize pane = fold the [`CHANNELIZE_PASSES`] rows against the
    ///   post-inference pane.
    ///
    /// The leaks are **returned, not asserted**: `Unexplained` is the capture
    /// gate ([`gate_leaks`]) but a relation is only clean once every pass inside
    /// it records its rewrites, and `Died` is the death report, which a caller
    /// reads rather than gates on.
    // Cold path: the inspector's snapshot serve, which is not in this workspace.
    #[allow(dead_code)]
    pub(crate) fn materialize_panes(&self) -> MaterializedPanes {
        let pre_ids = collect_tree_ids(&self.pre_inference_ir);
        let post_inf_ids = collect_tree_ids(&self.post_inference_ir);
        let post_des_ids = collect_tree_ids(&self.post_channelize_ir);

        let (mono_map, post_inference, mono_leaks) = collapse(
            &self.provenance_table,
            MONO_PASSES,
            &pre_ids,
            &post_inf_ids,
            &self.lowering_projection,
        );
        let (channelize_map, post_channelize, channelize_leaks) = collapse(
            &self.provenance_table,
            CHANNELIZE_PASSES,
            &post_inf_ids,
            &post_des_ids,
            &post_inference,
        );

        MaterializedPanes {
            pre_inference: self.lowering_projection.clone(),
            post_inference,
            post_channelize,
            mono_map,
            channelize_map,
            mono_leaks,
            channelize_leaks,
        }
    }
}

/// The passes each pane relation spans — the set
/// [`CompiledProgram::materialize_panes`] restricts the whole-compile table by.
///
/// A pane relation is defined by the passes that ran between its panes, not by a
/// position in a list: a program that skips a pass must not shift the other one's
/// set, and a row produced outside a relation's passes has to read to it as an
/// ordinary un-produced id.
pub(crate) const MONO_PASSES: &[Pass] = &[Pass::Mono];

/// The passes between the post-inference and post-channelize panes. See
/// [`MONO_PASSES`].
pub(crate) const CHANNELIZE_PASSES: &[Pass] =
    &[Pass::Inline, Pass::Transact, Pass::Letrec, Pass::Channelize];

/// The per-pane projections, pane-pair provenance maps, and per-relation leaks
/// materialized from [`CompiledProgram::provenance_table`] — see
/// [`CompiledProgram::materialize_panes`].
// Consumed by the inspector model; unused within the compiler itself.
#[allow(dead_code)]
pub(crate) struct MaterializedPanes {
    /// pre-inference pane projection (= the lowering projection).
    pub(crate) pre_inference: SourceProjection,
    /// post-inference pane projection.
    pub(crate) post_inference: SourceProjection,
    /// post-channelize pane projection.
    pub(crate) post_channelize: SourceProjection,
    /// pre-inference → post-inference provenance map (the `Mono` fan-out). Dense:
    /// an id that survived is its own self-edge.
    pub(crate) mono_map: ProvenanceMap<NodeId, NodeId>,
    /// post-inference → post-channelize provenance map.
    pub(crate) channelize_map: ProvenanceMap<NodeId, NodeId>,
    /// Leaks at the pre-inference → post-inference pane relation.
    pub(crate) mono_leaks: Vec<Leak>,
    /// Leaks at the post-inference → post-channelize pane relation.
    pub(crate) channelize_leaks: Vec<Leak>,
}

impl MaterializedPanes {
    /// `(relation name, leaks)` for each pane relation, in pipeline order.
    #[allow(dead_code)]
    pub(crate) fn pane_relations(&self) -> [(&'static str, &[Leak]); 2] {
        [
            ("pre-inference → post-inference", &self.mono_leaks),
            ("post-inference → post-channelize", &self.channelize_leaks),
        ]
    }

    /// The pane relations a gate can hold at zero: the ones whose passes are
    /// **instrumented**. Same discipline as an audit span's endpoint — a gate
    /// over a relation whose passes do not record cannot reach zero however
    /// correct the recording is, so it would report a constant rather than a
    /// regression.
    ///
    /// Today that is the second relation only. The first spans monomorphization
    /// and inference, and **inference's predicate producers do not record**:
    /// `specialize_use` clones a definition per instantiation, and the copies of
    /// a predicate term inside it row against interior ids no pass ever produced
    /// (`Leak::ParentUnknown`). Over `tests/compilation_pipeline` that is 5
    /// programs, all of them UDF-with-filter or poly-wrapper shapes, and all of
    /// it the crossing "Known prerequisites" records. **Add the first relation
    /// here in the commit that makes inference record**, exactly as an audit
    /// span's endpoint moves with the pass that earns it.
    pub(crate) fn gated_pane_relations(&self) -> [(&'static str, &[Leak]); 1] {
        [("post-inference → post-channelize", &self.channelize_leaks)]
    }
}

/// Ids duplicated across *distinct* predicate terms — the uniqueness question
/// `assert_unique_node_ids` does not answer, since it walks the main tree only.
///
/// Dedups by `Rc` pointer first — one term riding many type slots is one term
/// and shares its ids with itself legitimately — then reports any id carried by
/// two different terms, or by a predicate term and the main tree.
#[cfg(test)]
pub(crate) fn predicate_id_collisions(expr: &Expr) -> Vec<(NodeId, &'static str)> {
    use crate::ccl::ty::Type;
    use std::collections::{HashMap, HashSet};
    use std::rc::Rc;

    // One entry per *distinct* predicate term, keyed by `Rc` pointer: a term
    // riding many type slots is one term and shares its ids with itself.
    fn ids_of(e: &Expr, out: &mut HashSet<NodeId>) {
        out.insert(e.node_id());
        e.walk_children(|c| ids_of(c, out));
    }
    fn from_ty(t: &Type, acc: &mut HashMap<usize, HashSet<NodeId>>) {
        if let Type::Refinement(_, r) = t {
            let key = Rc::as_ptr(&r.predicate) as usize;
            if let std::collections::hash_map::Entry::Vacant(slot) = acc.entry(key) {
                let mut s = HashSet::new();
                ids_of(&r.predicate, &mut s);
                slot.insert(s);
            }
            from_expr_ty(&r.predicate, acc);
        }
        t.walk_children(|c| from_ty(c, acc));
    }
    fn from_expr_ty(e: &Expr, acc: &mut HashMap<usize, HashSet<NodeId>>) {
        from_ty(&e.ty, acc);
        if let Some(a) = &e.user_annotation {
            from_ty(a, acc);
        }
        if let crate::ccl::TypedExprNode::Cast { target, .. } = &e.node {
            from_ty(target, acc);
        }
        e.walk_children(|c| from_expr_ty(c, acc));
    }
    let mut terms: HashMap<usize, HashSet<NodeId>> = HashMap::new();
    from_expr_ty(expr, &mut terms);

    let main = collect_main_tree_ids(expr);
    let mut seen: HashSet<NodeId> = HashSet::new();
    let mut dups = Vec::new();
    for local in terms.values() {
        for id in local {
            if main.contains(id) {
                dups.push((*id, "predicate-vs-main-tree"));
            } else if !seen.insert(*id) {
                dups.push((*id, "predicate-vs-predicate"));
            }
        }
    }
    dups.sort();
    dups.dedup();
    dups
}

/// Every [`NodeId`] on the **main tree only** — the `walk_children` node-set,
/// refinement predicates excluded.
///
/// The counterpart to [`collect_tree_ids`], which is predicate-*inclusive* and is
/// the id domain the fold must explain. This narrow walk exists so the two can be
/// measured against the same logs (see [`ProvenanceAudit::live_ids`]): with the
/// narrow live set, planning's *main-tree* output is essentially fully explained
/// and the residue is entirely inside refinement predicates, which is the
/// measurement that says where the remaining work is.
pub(crate) fn collect_main_tree_ids(expr: &Expr) -> std::collections::HashSet<NodeId> {
    fn go(e: &Expr, acc: &mut std::collections::HashSet<NodeId>) {
        acc.insert(e.node_id());
        e.walk_children(|c| go(c, acc));
    }
    let mut acc = std::collections::HashSet::new();
    go(expr, &mut acc);
    acc
}

/// Every node id reachable in `expr`: the `walk_children` node set plus the
/// interiors of every refinement predicate riding a type slot — the id domain the
/// recordings and the pane projections must explain.
///
/// Deliberately wider than `assert_unique_node_ids`, which walks children only.
/// Explanation and uniqueness are two questions with two answers; see
/// `design/provenance.md`, "Walking the ids".
pub(crate) fn collect_tree_ids(expr: &Expr) -> std::collections::HashSet<NodeId> {
    use crate::ccl::TypedExprNode;
    use crate::ccl::ty::Type;

    fn from_ty(t: &Type, acc: &mut std::collections::HashSet<NodeId>) {
        if let Type::Refinement(_, r) = t {
            from_expr(&r.predicate, acc);
        }
        t.walk_children(|c| from_ty(c, acc));
    }

    fn from_expr(e: &Expr, acc: &mut std::collections::HashSet<NodeId>) {
        acc.insert(e.node_id());
        from_ty(&e.ty, acc);
        if let Some(ann) = &e.user_annotation {
            from_ty(ann, acc);
        }
        // A `Cast`'s target is a type slot `walk_children` skips, and it is where
        // lowering parks the predicate it just built.
        if let TypedExprNode::Cast { target, .. } = &e.node {
            from_ty(target, acc);
        }
        e.walk_children(|c| from_expr(c, acc));
    }

    let mut acc = std::collections::HashSet::new();
    from_expr(expr, &mut acc);
    acc
}

/// The pane-relation leak gate: **[`Leak::Unexplained`] and [`Leak::ParentUnknown`]
/// must be zero**.
///
/// `Unexplained` is the capture gate — an output-pane node with no origin means
/// the driver missed a mint. `ParentUnknown` is the record-integrity gate — a
/// node's ancestry stopping at an id the fold has never heard of.
///
/// [`Leak::Died`] is deliberately **not** gated. Nothing declares a fate under
/// driver capture, so `Died` fires for every node that dies across the fold — it
/// is the death report, and asserting it empty would be unsatisfiable on any
/// program that rewrites anything.
///
/// Debug/test only, single code path (`cfg!`, not `#[cfg]`).
fn gate_leaks(leaks: &[Leak], relation: &str) {
    if !cfg!(any(debug_assertions, test)) {
        return;
    }
    let defects: Vec<&Leak> = leaks.iter().filter(|l| l.is_defect()).collect();
    assert!(
        defects.is_empty(),
        "provenance capture defect across the {relation} pane relation \
         ({} of {} leaks; `Died` is the death report and is not gated): {defects:?}",
        defects.len(),
        leaks.len(),
    );
}

/// Every duplicated [`NodeId`] over the **main tree** — the `walk_children`
/// node-set, refinement predicates excluded — uniqueness is a narrower question
/// than explanation, and this matches inline's blind spot, so the
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
/// Uniqueness within a tree is what makes a `NodeId` an *identity*: the provenance
/// map is keyed by id, so two live nodes sharing one id make their attributions
/// and edges indistinguishable. The failure mode this catches is a clone that
/// forgot to freshen, or a rewrite that preserved an id where it minted.
///
/// This asserts a *tree invariant* at a pass boundary and encodes no pass order,
/// so it is robust to pass reordering (a moved pass carries its check with it).
/// It catches the *class* of preserve-as-mint / clone-without-freshen bugs
/// across the whole test suite, not just a crafted program.
///
/// The walk is [`duplicate_node_ids`]'s main-tree `walk_children` walk, and
/// **deliberately narrower than [`collect_tree_ids`]**, which enumerates
/// refinement predicates too. The two answer different questions — explanation
/// versus uniqueness (`design/provenance.md`, "Walking the ids") — and a
/// predicate-inclusive uniqueness walk would false-fire on inline's known
/// predicate blind spot, where a predicate interior legitimately aliases a
/// main-tree id. Gated
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

// ---------------------------------------------------------------------------
// Provenance measurement switches
//
// Four environment variables steer what the recorder does. Each is named once
// and read through exactly one accessor, because two of them interact: pane
// capture and an audit span are alternative modes over *one* recorder session
// (per-thread, non-reentrant), so the two switches have to agree on what "an
// audit is running" means. A second `std::env::var` call on the same name is
// how that agreement silently drifts.
// ---------------------------------------------------------------------------

/// Turns pane capture off (`=0`), so the cost of capture can be measured
/// against the same binary compiling the same programs.
const PROVENANCE_ENV: &str = "CAMBRA_PROVENANCE";

/// Names the [`ProvenanceAudit`] span to open, e.g. `full`.
const PROVENANCE_AUDIT_ENV: &str = "CAMBRA_PROVENANCE_AUDIT";

/// Gates the pane-relation leak classes on **every** compile (`=1`), making the
/// gate's corpus whatever the caller compiles.
const PROVENANCE_GATE_ENV: &str = "CAMBRA_PROVENANCE_GATE";

/// Narrows an audit's live set to the main tree, excluding refinement-predicate
/// interiors (`=0`). Predicate-inclusive otherwise — see
/// [`provenance_predicates_live`].
const PROVENANCE_PREDICATES_ENV: &str = "CAMBRA_PROVENANCE_PREDICATES";

/// Repetition count for the ignored perf driver. Test-only — the driver is a
/// `#[test]`, so the name is dead in a lib build; it lives here rather than
/// beside its reader so that adding a fifth switch means editing one block.
#[cfg(test)]
const PERF_REPS_ENV: &str = "CAMBRA_PERF_REPS";

/// The audit span named by [`PROVENANCE_AUDIT_ENV`], if any. **Sole reader** of
/// that variable — see the section note above.
fn provenance_audit_span() -> Option<String> {
    std::env::var(PROVENANCE_AUDIT_ENV).ok()
}

/// Whether an audit's live set admits refinement-predicate interiors. **On by
/// default**; `=0` narrows it to [`collect_main_tree_ids`]'s `walk_children`
/// domain.
///
/// The default matches what the shipped gate folds: [`materialize_panes`] takes
/// every pane's live set with [`collect_tree_ids`], which is predicate-inclusive.
/// An audit measuring the *narrower* set therefore reports edges the gate does
/// not — a recorded predicate rebuild's parents are input-tree predicate
/// interiors, which the narrow set omits from the input side, so those edges
/// dangle as [`Leak::ParentUnknown`] with nothing actually unrecorded. Defaulting
/// to the narrow set made the plain invocation report ~166 folds of noise on
/// the pipeline orpus and buried real defects in it.
///
/// [`materialize_panes`]: CompiledProgram::materialize_panes
fn provenance_predicates_live() -> bool {
    !std::env::var(PROVENANCE_PREDICATES_ENV).is_ok_and(|v| v == "0")
}

/// Whether [`compile_program`] opens the per-pass recorder scopes that fill
/// [`CompiledProgram::provenance_table`]. On by default.
///
/// The switch changes only whether a scope is opened; every recording hook is
/// already a no-op outside one (`STEP_STACK` empty / no ambient pass).
///
/// A [`ProvenanceAudit`] span opens its own scope, so naming one turns pane
/// capture off.
pub(crate) fn provenance_capture_enabled() -> bool {
    !std::env::var(PROVENANCE_ENV).is_ok_and(|v| v == "0") && provenance_audit_span().is_none()
}

/// Whether every compile folds its pane relations and gates the leak classes,
/// rather than only the programs a test asks about.
///
/// **What this buys.** The always-on gate is
/// `pane_relations_fold_with_no_structural_leaks`, whose corpus is the handful
/// of programs listed in `corpus()`. That is a *sample*, and a recording gap in
/// a shape the sample misses is invisible: the unrecorded
/// `fold_induction_loop` call in `transact_phase` (a commit decision reading
/// another loop's accumulator) and `flatten_spine`'s value-position writer hoist
/// both sat outside it. With this on, the corpus is every program the caller
/// compiles — point it at `tests/compilation_pipeline` and the gate covers the
/// whole suite instead of eleven programs.
///
/// Off by default because it folds the table twice per compile, which is
/// superlinear work the ordinary pipeline does not need; CI turns it on. It is
/// **not** a substitute for the sampled gate, which stays always-on so a plain
/// `cargo test` still fails on the common shapes.
///
/// Requires capture: with `CAMBRA_PROVENANCE=0`, or under an audit span (which
/// takes the pass scopes for itself), the table is empty and every output node
/// would read as unexplained. Both are honoured rather than asserted, so a run
/// can name one without also having to unset this.
fn provenance_gate_every_compile() -> bool {
    std::env::var(PROVENANCE_GATE_ENV).is_ok_and(|v| v != "0") && provenance_capture_enabled()
}

/// Run `f` with `pass` installed as the recorder's ambient pass, so every row a
/// recording inside it writes is tagged with that pass. With `capture` false this
/// is exactly `f()` — no scope, and every construction hook stays a no-op.
///
/// The pass identity lives in the *data* — the row's `RewriteTag`, completed
/// from the scope when a guard drops — which is why one helper covers every pass
/// regardless of its signature: the passes here are free functions of four
/// different shapes and nothing is threaded through them.
fn recorded<R>(capture: bool, pass: Pass, f: impl FnOnce() -> R) -> R {
    if !capture {
        return f();
    }
    let _scope = PassScope::enter(pass);
    f()
}

/// A driver-capture audit over one span of the pipeline: install a pass recorder at
/// the input pane, fold at the output pane, and print what the capture explains.
///
/// Opt-in via `CAMBRA_PROVENANCE_AUDIT=1` so the whole test suite can run either
/// way. It is a **measurement**, not a gate: the point of driver capture is that
/// nothing declares a fate, so the fold's `retired` set is empty by construction
/// and every genuinely-dead input id surfaces as [`Leak::Died`]. That class is
/// therefore the *death report*, not an error, and the audit counts it
/// separately from the classes that really are recording bugs
/// ([`Leak::Unexplained`] — an output node no recording accounted for).
struct ProvenanceAudit {
    span: &'static str,
    state: Option<(PassScope, std::collections::HashSet<NodeId>)>,
}

impl ProvenanceAudit {
    /// The `via` an audit's rows carry. A span covers several passes under one
    /// scope, so no single pass is the truthful answer; the tag is nominal, and
    /// naming it once keeps the scope's tag and the passes the fold restricts by
    /// from disagreeing about which nominal pass it is.
    const AUDIT_VIA: Pass = Pass::Planning;

    /// The audit's live set: [`collect_main_tree_ids`]'s `walk_children` domain,
    /// or — when [`provenance_predicates_live`] says so — [`collect_tree_ids`]'s
    /// predicate-inclusive domain.
    ///
    /// Both arms are real and differ: the narrow one is *not* the id domain any
    /// more. `collect_tree_ids` became predicate-inclusive, which briefly made
    /// this switch inert (both arms computing the same set) and its own doc
    /// comment false. Keeping a named narrow walk is what makes the comparison
    /// measurable rather than a no-op.
    fn live_ids(expr: &Expr) -> std::collections::HashSet<NodeId> {
        if provenance_predicates_live() {
            collect_tree_ids(expr)
        } else {
            collect_main_tree_ids(expr)
        }
    }

    /// Open the audit if [`provenance_audit_span`] names this `span`. Spans are
    /// mutually exclusive because a pass scope is per-thread and non-reentrant;
    /// naming them lets a run narrow the measurement to the passes under study
    /// instead of the whole tail of the pipeline.
    fn start(span: &str, name: &'static str, input: &Expr) -> Self {
        let on = provenance_audit_span().is_some_and(|w| w == span);
        ProvenanceAudit {
            span: name,
            state: on.then(|| (PassScope::enter(Self::AUDIT_VIA), Self::live_ids(input))),
        }
    }

    fn finish(self, output: &Expr) {
        let Some((scope, input_ids)) = self.state else {
            return;
        };
        // Close the scope before folding: the rows are in the compile's table,
        // which is still installed (it is drained at the end of the compile),
        // so the measurement reads them in place rather than draining anything.
        drop(scope);
        let output_ids = Self::live_ids(output);
        let Some((rows, projection, leaks)) = crate::ccl::provenance::with_active_table(|table| {
            let (_map, projection, leaks) = collapse(
                table,
                &[Self::AUDIT_VIA],
                &input_ids,
                &output_ids,
                &SourceProjection::new(),
            );
            (table.len(), projection, leaks)
        }) else {
            return;
        };
        let mut counts = std::collections::BTreeMap::<&str, usize>::new();
        for l in &leaks {
            *counts
                .entry(match l {
                    Leak::Unexplained { .. } => "Unexplained(output not covered by any recording)",
                    Leak::Died { .. } => "Died(= the death report)",
                    Leak::ParentUnknown { .. } => "ParentUnknown",
                })
                .or_default() += 1;
        }
        eprintln!(
            "[provenance-audit {}] rows={rows} input={} output={} attributed={} leaks={counts:?}",
            self.span,
            input_ids.len(),
            output_ids.len(),
            projection.len(),
        );
    }
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

    // The node table spans the **whole compile**, not a pass: its rows are keyed
    // by `NodeId`, which is unique for the life of the process, so every pass
    // session's flushes mirror into one table with no possibility of collision.
    // Installed before the first session opens (the lowering one) and drained
    // below; every early return drops it, clearing the slot.
    let table_session = TableSession::install();

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
    // `tag_machinery`) and copy-sink writes (uncurry, compare-chain) record a
    // `LoweringLog`, folded once at the handoff below into the always-on lowering
    // projection. It must fully drain before the first pass (Mono) session opens.
    let lowering_session = LoweringSession::install();
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
    // gated at the boundary via `gate_leaks`; the fold itself is
    // always-on (its product is release-critical).
    // Id uniqueness is the precondition for keying anything by `NodeId`, so gate
    // it before the fold that does exactly that: a duplicate here would silently
    // collapse two nodes' attributions into one projection entry. Lowering's own
    // copy sites (uncurry's template discharge, the chained-comparison operand
    // freshens) are what make this a live risk at this boundary.
    assert_unique_node_ids(&expr, "post-lowering");

    let lowering_log = lowering_session.into_log();
    let lowering_projection = {
        let output_ids = collect_tree_ids(&expr);
        let (projection, leaks) = collapse_lowering(&lowering_log, &output_ids);
        gate_leaks(&leaks, "lowering");
        projection
    };

    debug!("Lowered (pre-channelize):\n{}", symbolic(&expr));

    // α-uniquify all binders (Barendregt convention): every binding site gets
    // a globally fresh `Name` uid, so shadowing ceases to exist before any
    // pass that compares names. Must run before channelization — channelize's
    // rewrites splice and rename terms under the assumption that distinct
    // binders are distinct names. (Channelize now runs after inference; see below.)
    expr = uniquify::run(expr);

    // Retain the pre-inference IR for the inspector's upstream pane before
    // `infer` mutates `expr` in place. This is the source-shaped, pre-mono,
    // still-hole-typed tree. Its ids resolve against the `lowering_projection`
    // (the pre-mono originals). See `CompiledProgram::pre_inference_ir`.
    // A pane snapshot: the same nodes as the live tree, observed at a point in
    // time, so it preserves ids. A freshening clone would hand the pane a
    // structurally identical program sharing no identity with the one it is meant
    // to snapshot, and these ids must resolve against the `lowering_projection`,
    // which is keyed by the originals.
    let pre_inference_ir = expr.clone_preserving_ids();

    // Pass recording for the rows the two pane relations fold. One scope per
    // pass, opened and closed in place: a pass scope is per-thread and
    // non-reentrant, so the scopes are sequential, never nested.
    let capture_lineage = provenance_capture_enabled();

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
    // Monomorphization runs inside `infer` and is the only thing there that
    // mints or clones nodes, so this session *is* the pre-inference →
    // post-inference pane bridge.
    let infer_outcome = recorded(capture_lineage, Pass::Mono, || {
        infer(&mut expr, ctx.inference_ctx())
    });
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
    // *pre-channelize* check (`check_pre_channelize`), which permits the transient
    // `Feed` / `Infer`-channel-domain types only channelize can erase. A failure
    // here is a compiler bug — with one exception: residual `Type::Infer`
    // variables, which inference deliberately tolerates for a generalized
    // definition the program never exercises at a concrete type (see
    // `Type::Infer`'s invariant). That residue is an *ambiguous program* — a
    // user error — so it is rendered as a diagnostic; anything else panics.
    check_pre_channelize(&expr).map_err(|errs| {
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
    // `user_annotation`s. Unlike the surrounding `check_pre_channelize` walls
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

    // Inline UDFs *before* channelize: a defer-mediating UDF (`λ out → out << e`)
    // or a cross-function writer is beta-reduced to its call site before
    // channelize routes feeds and before the unified letrec phase folds writers,
    // both of which need their targets lexically present. Inlining runs on the
    // still-defer-bearing tree (Defer/Feed nodes and `Feed` types present) via
    // the defer-aware `Subst` engine (which renames a fed-to handle on
    // beta-reduction) and preserves defer-returning generators, so the
    // post-inline wall is the relaxed `check_pre_channelize`, not strict
    // `typecheck`.
    // Retain the post-inference IR for the inspector before `inline` consumes
    // `expr`. This is the source-shaped, fully-typed anchor (lambdas intact, not
    // yet point-free; inline/transact/letrec/channelize/lambda_elim/planning have
    // not run). `ast` (`join_planned`) is the *wrong* tree for a source
    // view — `lambda_elim`/`planning` re-mint ids and produce execution shape.
    // See `CompiledProgram::post_inference_ir`.
    // A pane snapshot; see `pre_inference_ir`.
    let post_inference_ir = expr.clone_preserving_ids();

    // Driver-capture audit span: post-inference pane in, and out at the **last
    // instrumented pane** — currently `post-as-of-read`, covering inline,
    // transact, mut_elim, channelize and the as-of-read rewrite.
    //
    // The endpoint is chosen rather than inherited. An audit measures what the
    // recordings explain, so a span running past the last instrumented pass
    // reports every node the uninstrumented tail mints as a defect — a number
    // that cannot reach zero however correct the recording is, which makes the
    // audit read as a broken gate instead of a measurement. `lambda_elim` is the
    // next pass here and records nothing (it re-mints nearly every pass-through
    // node), so the span stops in front of it.
    //
    // **Move this endpoint when a pass becomes instrumented, in the same commit
    // that instruments it** — to `post-lambda-elim` when the elim pass records,
    // and to `join-planned` when planning does. Leaving it behind understates
    // coverage; moving it ahead reintroduces the unreachable-zero problem.
    let audit = ProvenanceAudit::start(
        "full",
        "post-inference..post-as-of-read",
        &post_inference_ir,
    );
    // A narrower pane pair over just the mutability phases (inline, transact,
    // mut_elim), which is where the fate-prediction question lives.
    let audit_letrec =
        ProvenanceAudit::start("letrec", "post-inference..post-letrec", &post_inference_ir);

    expr = recorded(capture_lineage, Pass::Inline, || {
        inline::inline_capability_lambdas(expr)
    });
    assert_unique_node_ids(&expr, "post-inline");
    debug!("UDFs inlined CCL:\n{}", symbolic(&expr));
    check_pre_channelize(&expr).map_err(|errs| {
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
    // `await_final` consumes its mutable variable: no mention may follow its await. A
    // statement-order rule lowering cannot see — it builds its chain right-to-left —
    // and a callee's mention only becomes a read, a write, or a `Begin` once inlined.
    // (The companion rule, that a commit store may not depend on the completion of
    // that same store, is decided per store and so lives inside the phase.)
    transact_phase::check_await_final_linearity(&expr)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    expr = recorded(capture_lineage, Pass::Transact, || {
        transact_phase::run(expr, &txn_mut_vars)
    })
    .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    assert_unique_node_ids(&expr, "post-transact");
    debug!("Transact phase CCL:\n{}", symbolic(&expr));
    check_pre_channelize(&expr).expect("transact phase produced an inconsistent tree");

    // The unified letrec phase: direct-mirror mutation loops (`For` /
    // `MutWrite`) become causal `LetRec` groups — mutable histories over
    // the induction domain, per src/ccl/design/mutability.md. Runs after
    // inlining (so cross-function writers land at their call sites) and
    // *before* channelize, so a per-iteration feed inside a loop is
    // hoisted to an ordinary feed of the loop's history for channelize to route.
    // The tree still carries Defer/Feed here, so the walls are the relaxed
    // pre-channelize check.
    // Isolated pane pair over `mut_elim` alone — the pass whose fate prediction
    // driver capture is meant to delete.
    let audit_mutelim = ProvenanceAudit::start("mutelim", "post-transact..post-letrec", &expr);
    let phase_out = recorded(capture_lineage, Pass::Letrec, || mut_elim::run(expr));
    audit_mutelim.finish(&phase_out);
    assert_unique_node_ids(&phase_out, "post-letrec-run");
    audit_letrec.finish(&phase_out);
    debug!("Letrec phase CCL:\n{}", symbolic(&phase_out));
    check_pre_channelize(&phase_out).expect("letrec phase produced an inconsistent tree");

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
    let mut channelized = recorded(capture_lineage, Pass::Channelize, || {
        channelize::run(phase_out)
    })
    .errs()?;
    assert_unique_node_ids(&channelized, "post-channelize");
    debug!("Channelized:\n{}", symbolic(&channelized));
    typecheck(&channelized).expect("channelize produced an ill-typed tree");

    // Retain the post-channelize tree for the inspector's downstream pane. On the
    // post-inference channelize order this snapshot is *downstream* of
    // `post_inference_ir` (post-inline/transact/letrec/channelize); see the doc
    // comment on `post_channelize_ir`.
    // A pane snapshot; see `pre_inference_ir`.
    let post_channelize_ir = channelized.clone_preserving_ids();

    // Fed-out mutable variable reads: rewrite a read-only reply that reads a mutable variable out of
    // its block into an outer-indexed as-of join (an as-of read at the reading
    // transaction's arbitrary commit position), *before* lambda elimination — so a
    // computed reply (`resp << balance + 1`) stays a lambda the elim pass point-frees,
    // rather than a point-free `const` a planning-time recognizer would have to
    // reject. Uniform across the reading loop's domain. See
    // `transact_phase::rewrite_as_of_reads`.
    transact_phase::rewrite_as_of_reads(&mut channelized)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    assert_unique_node_ids(&channelized, "post-as-of-read");
    typecheck(&channelized).expect("as-of-read rewrite produced an ill-typed tree");
    // The last instrumented pane: see the span's own note at `ProvenanceAudit::start`.
    audit.finish(&channelized);

    let lambda_elim = lambda_elim::run(channelized).errs()?;
    assert_unique_node_ids(&lambda_elim, "post-lambda-elim");
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

    // Isolated pane pair over `planning::run` — the passes containing
    // `simplify`'s 13 rules and `wrap_with_iterate`.
    let audit_planning =
        ProvenanceAudit::start("planning", "recognized..join-planned", &recognized);
    let join_planned = planning::run(recognized);
    audit_planning.finish(&join_planned);
    assert_unique_node_ids(&join_planned, "post-planning");
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

    let provenance_table = table_session.into_table();

    let program = CompiledProgram {
        ast: join_planned,
        outputs,
        done: done_rx,
        lowering_projection,
        pre_inference_ir,
        post_inference_ir,
        post_channelize_ir,
        provenance_table,
        source_ast: module,
        source: code.to_string(),
    };

    // Every compile its own gate — see `provenance_gate_every_compile` for why this
    // is opt-in and what it covers that the sampled gate does not.
    if provenance_gate_every_compile() {
        for (relation, leaks) in program.materialize_panes().gated_pane_relations() {
            gate_leaks(leaks, relation);
        }
    }

    Ok(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    /// The pane-measurement corpus: every demo-gallery program that compiles
    /// today, plus four inline programs covering the passes the gallery does not
    /// reach (a `with begin():` transaction, a group-by, a UDF chain, and a
    /// nested comprehension).
    ///
    /// The gallery's remaining programs are excluded for reasons unrelated to
    /// provenance: most are deliberate *failure* fixtures (`while`, record-term
    /// syntax, `Feed(_)` types) that pin errors and so have no panes to fold,
    /// and the three HTTP demos bind a real listening socket during lowering,
    /// which collides with itself under a parallel test runner.
    fn corpus() -> Vec<(&'static str, String)> {
        vec![
            (
                "arithmetic",
                include_str!("../../tests/programs/arithmetic/program.cambra").to_string(),
            ),
            (
                "filter_and_aggregate",
                include_str!("../../tests/programs/filter_and_aggregate/program.cambra").to_string(),
            ),
            (
                "for_accumulator",
                include_str!("../../tests/programs/for_accumulator/program.cambra").to_string(),
            ),
            (
                "generator_pipeline",
                include_str!("../../tests/programs/generator_pipeline/program.cambra").to_string(),
            ),
            (
                "inner_join",
                include_str!("../../tests/programs/inner_join/program.cambra").to_string(),
            ),
            (
                "prefix_lines",
                include_str!("../../tests/programs/prefix_lines/program.cambra").to_string(),
            ),
            (
                "streaming_echo",
                include_str!("../../tests/programs/streaming_echo/program.cambra").to_string(),
            ),
            (
                "transaction",
                "out = defer()\n\
                 pool: Mut(Int, Txn) := 100\n\
                 for r in [10, 20, 30]:\n\
                 \x20   with begin():\n\
                 \x20       pool := pool - r\n\
                 with begin():\n\
                 \x20   out << pool\n\
                 out\n"
                    .to_string(),
            ),
            (
                "group_by",
                "[sum(x) for x in groupby([y + 10 for y in [2,3,4,5,6] if y < 6], \\x -> x // 2)]\n"
                    .to_string(),
            ),
            (
                "udf_chain",
                "def double(x):\n    x * 2\ndef bump(x):\n    double(x) + 1\n\
                 xs = [1, 2, 3]\n[bump(x) for x in xs]\n"
                    .to_string(),
            ),
            (
                "feed_loop",
                "out = defer()\nfor x in [1, 2, 3]:\n    out << x * 2\nout\n".to_string(),
            ),
        ]
    }

    /// Compile `code` through the full pipeline, panicking on error.
    fn compile_ok(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        match compile_program(&mut ctx, code, consumer) {
            Ok(p) => p,
            Err(errs) => panic!("expected a successful compile, got {errs:?}"),
        }
    }

    /// Per-leak-class counts, for reporting a pane relation.
    #[derive(Default, Debug, PartialEq, Eq)]
    struct LeakCounts {
        unexplained: usize,
        died: usize,
        parent_unknown: usize,
    }

    impl LeakCounts {
        fn tally(leaks: &[Leak]) -> Self {
            let mut c = LeakCounts::default();
            for l in leaks {
                match l {
                    Leak::Unexplained { .. } => c.unexplained += 1,
                    Leak::Died { .. } => c.died += 1,
                    Leak::ParentUnknown { .. } => c.parent_unknown += 1,
                }
            }
            c
        }

        fn add(&mut self, o: &LeakCounts) {
            self.unexplained += o.unexplained;
            self.died += o.died;
            self.parent_unknown += o.parent_unknown;
        }

        /// The structural class — a record-integrity defect, independent of how
        /// much of the pipeline records its rewrites. See [`gate_leaks`].
        fn structural(&self) -> usize {
            self.parent_unknown
        }
    }

    /// **Capture totality**, as a corpus-wide property rather than a per-pass
    /// assertion: both pane relations materialize and fold over every corpus
    /// program, every output-pane node has an origin (`Unexplained == 0`), and
    /// the structural classes are zero everywhere.
    ///
    /// The two invariants fail differently and are worth reading apart.
    /// `structural == 0` says no node's ancestry stops at an id the relation
    /// never heard of. `Unexplained == 0` says no rewrite went
    /// *unrecorded* — it is the gate the whole driver-capture design exists to
    /// pass, and the number a newly-added rewrite site breaks first.
    #[test]
    fn pane_relations_fold_with_no_structural_leaks() {
        let mut totals = [LeakCounts::default(), LeakCounts::default()];
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let panes = program.materialize_panes();
            for (i, (relation, leaks)) in panes.pane_relations().into_iter().enumerate() {
                let c = LeakCounts::tally(leaks);
                assert_eq!(
                    c.structural(),
                    0,
                    "{name}: structural leaks across the {relation} pane relation: {c:?}"
                );
                assert_eq!(
                    c.unexplained, 0,
                    "{name}: unexplained output nodes across the {relation} pane relation — a rewrite \
                     that mints with nothing recording: {c:?}"
                );
                eprintln!("[pane {name} / {relation}] {c:?}");
                totals[i].add(&c);
            }
            // The panes are the thing being materialized: each projection must
            // hold entries for the tree it describes, and each map edges.
            assert!(!panes.pre_inference.is_empty(), "{name}");
            assert!(!panes.post_inference.is_empty(), "{name}");
            assert!(!panes.post_channelize.is_empty(), "{name}");
            assert!(!panes.mono_map.edges().is_empty(), "{name}");
            assert!(!panes.channelize_map.edges().is_empty(), "{name}");
        }
        eprintln!("[pane totals] pre→post-inference {:?}", totals[0]);
        eprintln!(
            "[pane totals] post-inference→post-channelize {:?}",
            totals[1]
        );
    }

    /// Every pass that records rows in a normal compile belongs to exactly one
    /// pane relation, so no rewrite is folded twice and none is silently dropped.
    ///
    /// [`MONO_PASSES`] and [`CHANNELIZE_PASSES`] are the only things that decide
    /// which pane relation a row reaches, so a pass that opens a scope without
    /// joining neither would record rows nothing ever folds.
    #[test]
    fn every_recorded_pass_belongs_to_exactly_one_pane_relation() {
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            for p in program.provenance_table.recorded_passes() {
                assert!(
                    MONO_PASSES.contains(&p) != CHANNELIZE_PASSES.contains(&p),
                    "{name}: {p:?} is in neither pane relation, or in both",
                );
            }
        }
    }

    /// The `program / relation` pairs at which the pane relation is **not**
    /// vacuous — where some node's origin is another node, so the fold had to
    /// read a row. See
    /// [`the_pane_folds_derive_a_non_vacuous_lineage_relation`].
    /// Grew from seven entries to sixteen — a strict superset, every original
    /// retained — when monomorphization and transport-mode substitution started
    /// recording. `pre-inference → post-inference` in particular was vacuous on
    /// eight programs because the only pass rewriting there, `Mono`,
    /// opened its recording *after* the clone that produced its nodes, so
    /// nothing captured.
    const EXERCISED_BOUNDARIES: &[&str] = &[
        "arithmetic / pre-inference → post-inference",
        "feed_loop / post-inference → post-channelize",
        "feed_loop / pre-inference → post-inference",
        "filter_and_aggregate / pre-inference → post-inference",
        "for_accumulator / post-inference → post-channelize",
        "for_accumulator / pre-inference → post-inference",
        "generator_pipeline / post-inference → post-channelize",
        "generator_pipeline / pre-inference → post-inference",
        "group_by / pre-inference → post-inference",
        "inner_join / pre-inference → post-inference",
        "prefix_lines / pre-inference → post-inference",
        "streaming_echo / pre-inference → post-inference",
        "transaction / post-inference → post-channelize",
        "transaction / pre-inference → post-inference",
        "udf_chain / post-inference → post-channelize",
        "udf_chain / pre-inference → post-inference",
    ];

    /// **The pane relation is well-formed and non-vacuous** on every corpus
    /// program: every edge runs from an input-pane id to an output-pane id,
    /// every id present in both panes is its own dense self-edge, and the
    /// pane relations where the fold had to read a *row* are exactly the ones
    /// pinned above.
    ///
    /// The non-vacuity half is what this test is for. Fifteen of the
    /// twenty-two corpus relations are pure identity: no pass inside them
    /// minted, so the relation is the input pane's self-edges and holds for
    /// reasons that have nothing to do with the recording. A corpus edit that
    /// silently dropped the rewriting programs would otherwise leave a green
    /// tautology behind.
    #[test]
    fn the_pane_folds_derive_a_non_vacuous_lineage_relation() {
        let mut exercised: Vec<String> = Vec::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let panes = program.materialize_panes();
            let pre = collect_tree_ids(&program.pre_inference_ir);
            let post_inf = collect_tree_ids(&program.post_inference_ir);
            let post_des = collect_tree_ids(&program.post_channelize_ir);

            let relations: [(&str, &ProvenanceMap<NodeId, NodeId>, _, _); 2] = [
                (
                    "pre-inference → post-inference",
                    &panes.mono_map,
                    &pre,
                    &post_inf,
                ),
                (
                    "post-inference → post-channelize",
                    &panes.channelize_map,
                    &post_inf,
                    &post_des,
                ),
            ];

            for (relation, map, input_ids, output_ids) in relations {
                let edges = map.edges();
                assert!(
                    !edges.is_empty(),
                    "{name}: the {relation} pane relation derived no edges at all",
                );
                for (u, d) in &edges {
                    assert!(
                        input_ids.contains(u),
                        "{name}: {u:?} is an edge origin at {relation} but not an input-pane id",
                    );
                    assert!(
                        output_ids.contains(&d.id),
                        "{name}: {:?} is an edge target at {relation} but not an output-pane id",
                        d.id,
                    );
                }
                // Dense: a node present in both panes is its own self-edge, and
                // a node descends from itself — so a consumer only ever follows
                // edges, never reconstructs one, and reads ancestry off the
                // label it finds there.
                for id in input_ids.intersection(output_ids) {
                    let self_edge = map.upstream(id).iter().find(|l| l.id == *id);
                    assert!(
                        self_edge.is_some_and(|l| l.labels.has_ancestry()),
                        "{name}: {id:?} survives {relation} without an ancestry self-edge",
                    );
                }
                // A non-self edge is the only proof a row was consulted: a
                // relation whose passes rewrote nothing derives its whole
                // relation from the two pane id sets.
                if edges.iter().any(|(u, d)| *u != d.id) {
                    exercised.push(format!("{name} / {relation}"));
                }
            }
        }
        exercised.sort();
        assert_eq!(
            exercised, EXERCISED_BOUNDARIES,
            "the pane relations at which the fold actually reads a row have changed",
        );
    }

    /// The `program / relation` pairs at which a **blame** edge reaches the
    /// pane relation — where a rewrite named blame and the fold labelled the
    /// edge it contributed. See
    /// [`blame_reaches_the_pane_relation_labelled`].
    const RELATING_BOUNDARIES: &[&str] = &[
        "for_accumulator / post-inference → post-channelize",
        "transaction / post-inference → post-channelize",
    ];

    /// **Blame reaches the pane relation, labelled**: the `blame` column is
    /// closed transitively alongside `parents`, so a consumer receives the
    /// blame edges and can render or prune them.
    ///
    /// Pinned as the set of pane relations where such an edge exists, for the same
    /// reason [`EXERCISED_BOUNDARIES`] is pinned: blame is named at a handful of
    /// sites, all in the mutability phases and so all inside the second pane
    /// relation, and a corpus or recording edit that stopped exercising them
    /// would otherwise leave the labelled half of the relation untested.
    ///
    /// A blame edge is *only* blame here: no corpus rewrite both
    /// consumes a node and blames it, so nothing in the corpus pins the
    /// both-labels case — the fold tests in `provenance.rs` do.
    #[test]
    fn blame_reaches_the_pane_relation_labelled() {
        let mut relating: Vec<String> = Vec::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let panes = program.materialize_panes();
            let relations = [
                ("pre-inference → post-inference", &panes.mono_map),
                ("post-inference → post-channelize", &panes.channelize_map),
            ];
            for (relation, map) in relations {
                if map.edges().iter().any(|(_, d)| d.labels.has_blame()) {
                    relating.push(format!("{name} / {relation}"));
                }
            }
        }
        relating.sort();
        assert_eq!(
            relating, RELATING_BOUNDARIES,
            "the pane relations at which blame contributes an edge have changed",
        );
    }

    /// The corpus programs whose definitions inference **generalizes and then
    /// specializes** — the ones monomorphization actually clones a subtree for.
    /// Everything else in the corpus is first-order, and mono mints nothing.
    const SPECIALIZING: &[&str] = &["generator_pipeline", "udf_chain"];

    /// Monomorphization — the one pass inside the first pane relation —
    /// explains every node it produces, on first-order and specializing
    /// programs alike.
    ///
    /// Two recordings get it there, and both are needed: `specialize_use` sinks
    /// the clone's `on_copy` pairs, and `coalesce_generalized_let` sinks the
    /// chain of `let`s the binding rebuilds itself as. Without the second, a
    /// specializing program leaves one unexplained `let` per demanded
    /// specialization — a per-program count that tracks how many types the body
    /// asked for, which is why it read as a small constant on this corpus.
    ///
    /// Asserted both ways so the zero cannot be vacuous: a specializing program
    /// must also *kill* nodes here, since its generalized definition is
    /// replaced by clones. A regression that stopped running mono at all would
    /// otherwise pass.
    #[test]
    fn monomorphization_explains_every_node_it_produces() {
        for (name, code) in corpus() {
            let panes = compile_ok(&code).materialize_panes();
            let c = LeakCounts::tally(&panes.mono_leaks);
            assert_eq!(c.structural(), 0, "{name}: {c:?}");
            assert_eq!(
                c.unexplained, 0,
                "{name}: pre-inference → post-inference is uncaptured: {c:?}"
            );
            if SPECIALIZING.contains(&name) {
                assert!(
                    c.died > 0,
                    "{name}: specializes, so the generalized definition must die: {c:?}"
                );
            }
        }
    }

    /// All four passes inside the second relation explain what they produce.
    ///
    /// The interesting programs are the ones that drive a *whole-program*
    /// rewrite, where naming one node is least obviously applicable: a
    /// transaction is disassembled into a commit carrier whose pieces have no
    /// single source node, and a defer cluster becomes a `LetRec` assembled from
    /// contributions scattered across the body. Both are covered by recording
    /// against the node each product stands in for — the `with begin():`
    /// statement, the register declaration, the `let d = Defer`.
    ///
    /// Asserted with a non-vacuity guard for the same reason relation 1 is: a
    /// program that reaches one of these passes must also kill nodes, so a
    /// regression that stopped running the pass cannot pass as capture.
    #[test]
    fn the_second_pane_relation_explains_every_node_its_passes_produce() {
        /// Reaches `transact_phase` or `channelize` — the whole-program
        /// rewrites, and the last two passes to adopt the recorder.
        const WHOLE_PROGRAM_REWRITES: &[&str] = &["transaction", "feed_loop", "generator_pipeline"];
        for (name, code) in corpus() {
            let panes = compile_ok(&code).materialize_panes();
            let c = LeakCounts::tally(&panes.channelize_leaks);
            assert_eq!(c.structural(), 0, "{name}: {c:?}");
            assert_eq!(
                c.unexplained, 0,
                "{name}: post-inference → post-channelize is uncaptured: {c:?}"
            );
            if WHOLE_PROGRAM_REWRITES.contains(&name) {
                assert!(
                    c.died > 0,
                    "{name}: rewrites its whole shape, so nodes must die: {c:?}"
                );
            }
        }
    }

    /// Deaths are the live-set difference and nothing else: the `Died` set across
    /// a pane relation is exactly `input_ids ∖ output_ids` on a real program, with
    /// no pass having declared any of them. `for_accumulator` folds a mutation
    /// loop into a `LetRec`, so the difference is non-empty.
    #[test]
    fn deaths_across_a_pane_relation_are_the_set_difference() {
        let program = compile_ok(include_str!(
            "../../tests/programs/for_accumulator/program.cambra"
        ));
        let panes = program.materialize_panes();
        let input = collect_tree_ids(&program.post_inference_ir);
        let output = collect_tree_ids(&program.post_channelize_ir);
        let mut expected: Vec<NodeId> = input.difference(&output).copied().collect();
        expected.sort_unstable();
        let mut reported: Vec<NodeId> = panes
            .channelize_leaks
            .iter()
            .filter_map(|l| match l {
                Leak::Died { input } => Some(*input),
                _ => None,
            })
            .collect();
        reported.sort_unstable();
        assert!(!expected.is_empty(), "the fixture must actually kill nodes");
        assert_eq!(reported, expected);
    }

    /// **Distinct predicate terms never share a `NodeId`** — with each other, or
    /// with the main tree.
    ///
    /// Predicate ids are in the explanation domain but `assert_unique_node_ids`
    /// walks the main tree only (`design/provenance.md`, "Walking the ids"), so this
    /// is the only thing asserting uniqueness for them. Dedup is by `Rc` pointer
    /// first: one term riding many type slots is one term and shares ids with
    /// itself legitimately.
    ///
    /// What this catches is a rebuild that **preserves ids when it should not**. A
    /// predicate cannot be mutated through its `Rc`, so every rewrite builds a new
    /// `Rc` and repoints the refinement it was handed. That is a *replacement*
    /// only if the walk reaches every occurrence; otherwise the original survives
    /// on some type the walk missed, and preserving ids puts one id-set on two
    /// live terms. `PredMemo::replacing` is the opt-in for walks that do reach
    /// everything, and `uniquify` — the only one — asserts its own 1:1
    /// correspondence separately.
    #[test]
    fn distinct_predicate_terms_never_share_a_node_id() {
        let mut found: Vec<(String, usize, &'static str)> = Vec::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            for (pane, tree) in [
                ("pre-inference", &program.pre_inference_ir),
                ("post-inference", &program.post_inference_ir),
                ("post-channelize", &program.post_channelize_ir),
            ] {
                for (_, kind) in predicate_id_collisions(tree) {
                    found.push((format!("{name} / {pane}"), 1, kind));
                }
            }
        }
        assert!(
            found.is_empty(),
            "{} predicate id collisions: {found:?}",
            found.len(),
        );
    }

    /// A pass that rewrites the program records its rewrites under its own pass
    /// tag — the tag being the one part of a row no recording site knows, and the
    /// only thing that places a row in a pane relation.
    ///
    /// A pass that rewrites *nothing* on a given program records nothing, which
    /// is the preserve case and correct (most of the corpus preserves end to
    /// end), so the fixture is one that drives three of the five: the
    /// transaction, which `transact_phase` disassembles, `mut_elim` rebuilds as
    /// a `LetRec`, and `channelize` rewrites.
    #[test]
    fn a_rewriting_pass_tags_its_rows_with_itself() {
        let (_, code) = corpus()
            .into_iter()
            .find(|(name, _)| *name == "transaction")
            .expect("the transaction fixture");
        let program = compile_ok(&code);
        let mut recorded = program.provenance_table.recorded_passes();
        recorded.sort_by_key(|p| format!("{p:?}"));
        assert_eq!(
            recorded,
            vec![Pass::Channelize, Pass::Letrec, Pass::Mono, Pass::Transact],
            "the transaction fixture is rewritten by exactly these four passes",
        );
    }

    // -----------------------------------------------------------------------
    // Perf sanity for pane capture
    // -----------------------------------------------------------------------

    /// One generated program shape, parameterized by size.
    ///
    /// The shapes are chosen to hit the passes the panes span: `comprehension`
    /// and `arith` are `inline`-light and mostly id-preserving, `udf` drives
    /// inlining and monomorphization, `loop_acc` drives `mut_elim`, and `feed`
    /// drives `channelize`.
    ///
    /// Sizes are deliberately small. Compile time here is **superlinear in
    /// program size** for reasons that predate provenance capture (a UDF-heavy 63-line
    /// program compiles in tens of seconds), so a corpus large enough to be a
    /// benchmark would be too slow to run; this is a sanity check on the
    /// *ratio* between capture on and capture off, not a benchmark.
    fn generated(shape: &str, n: usize) -> String {
        match shape {
            "arith" => {
                let terms: Vec<String> = (1..=n).map(|i| format!("{i} * {}", i + 1)).collect();
                format!("x = {}\nx\n", terms.join(" + "))
            }
            "comprehension" => {
                // Independent comprehensions summed, rather than a chain: a
                // chained comprehension trips an unrelated substitution bug
                // ("discharged binder still free after substitution into
                // predicate") that has nothing to do with provenance.
                let parts: Vec<String> = (0..n)
                    .map(|i| format!("sum([y + {i} for y in xs if y > 0])"))
                    .collect();
                format!("xs = [1, 2, 3, 4, 5]\nt = {}\nt\n", parts.join(" + "))
            }
            "udf" => {
                let mut src = String::new();
                for i in 0..n {
                    src.push_str(&format!("def f{i}(x):\n    x + {i}\n"));
                }
                src.push_str("xs = [1, 2, 3, 4, 5]\n");
                let calls: Vec<String> = (0..n).map(|i| format!("f{i}(y)")).collect();
                src.push_str(&format!("[{} for y in xs]\n", calls.join(" + ")));
                src
            }
            "loop_acc" => {
                let mut src = String::from("xs = [1, 2, 3, 4, 5]\n");
                for i in 0..n {
                    src.push_str(&format!("a{i}: Mut(Int) := 0\n"));
                }
                src.push_str("for v in xs:\n");
                for i in 0..n {
                    src.push_str(&format!("    a{i} += v + {i}\n"));
                }
                src.push_str(&format!("a{}\n", n - 1));
                src
            }
            "feed" => {
                let mut src = String::from("out = defer()\nxs = [1, 2, 3, 4, 5]\n");
                for i in 0..n {
                    src.push_str(&format!("for v in xs:\n    out << v + {i}\n"));
                }
                src.push_str("out\n");
                src
            }
            other => panic!("unknown shape {other}"),
        }
    }

    /// The perf corpus: `(shape, size)` pairs, sized to keep the whole run in
    /// the low seconds per repetition.
    const PERF_CORPUS: &[(&str, usize)] = &[
        ("arith", 40),
        ("arith", 80),
        ("arith", 160),
        ("comprehension", 6),
        ("comprehension", 12),
        ("comprehension", 20),
        ("udf", 5),
        ("udf", 8),
        ("udf", 12),
        ("loop_acc", 4),
        ("loop_acc", 8),
        ("loop_acc", 14),
        ("feed", 3),
        ("feed", 6),
        ("feed", 12),
    ];

    /// Rough compile-time and retained-memory sanity for pane capture. Ignored
    /// by default — it is a measurement, not an assertion.
    ///
    /// Run it as two interleaved processes so the two arms see the same machine
    /// state, and take the min over repetitions:
    ///
    /// ```text
    /// for i in 1 2 3; do
    ///   CAMBRA_PROVENANCE=1 cargo test --release --lib provenance_pane_perf -- --ignored --nocapture
    ///   CAMBRA_PROVENANCE=0 cargo test --release --lib provenance_pane_perf -- --ignored --nocapture
    /// done
    /// ```
    ///
    /// With capture on it also materializes and folds both panes, since that is
    /// the cost the design actually incurs.
    #[test]
    #[ignore = "measurement, not an assertion; see the doc comment for the driver"]
    fn provenance_pane_perf() {
        let capture = provenance_capture_enabled();
        let reps: usize = std::env::var(PERF_REPS_ENV)
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(3);
        let mut total_compile = std::time::Duration::ZERO;
        let mut total_fold = std::time::Duration::ZERO;
        for (shape, n) in PERF_CORPUS {
            let code = generated(shape, *n);
            let mut best_compile = std::time::Duration::MAX;
            let mut best_fold = std::time::Duration::MAX;
            let mut rows = 0usize;
            let mut tags = 0usize;
            // The three retained pane snapshots are unconditional — they are not
            // part of what the capture switch turns off — so their size is the
            // pane design's real memory floor, against which the logs are noise.
            let mut panes_nodes = 0usize;
            for _ in 0..reps {
                let t0 = std::time::Instant::now();
                let program = compile_ok(&code);
                best_compile = best_compile.min(t0.elapsed());
                rows = program.provenance_table.len();
                tags = program.provenance_table.tag_count();
                panes_nodes = collect_tree_ids(&program.pre_inference_ir).len()
                    + collect_tree_ids(&program.post_inference_ir).len()
                    + collect_tree_ids(&program.post_channelize_ir).len();
                if capture {
                    let t1 = std::time::Instant::now();
                    let panes = program.materialize_panes();
                    std::hint::black_box(&panes.post_channelize);
                    best_fold = best_fold.min(t1.elapsed());
                }
            }
            if !capture {
                best_fold = std::time::Duration::ZERO;
            }
            total_compile += best_compile;
            total_fold += best_fold;
            eprintln!(
                "[perf capture={capture}] {shape}/{n}: compile {:?} fold {:?} rows {rows} \
                 tags {tags} pane_nodes {panes_nodes} lines {}",
                best_compile,
                best_fold,
                code.lines().count(),
            );
        }
        eprintln!("[perf capture={capture}] TOTAL compile {total_compile:?} fold {total_fold:?}");
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
            "the blame is the node whose coalesce rule raised the error — here the \
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

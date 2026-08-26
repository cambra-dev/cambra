// ---------------------------------------------------------------------------
// Context object for state shared across all phases of compilation like
// builtins
// ---------------------------------------------------------------------------

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;
use std::{cell::RefCell, rc::Rc};

use crate::chl_parser;
use crate::chl_parser::parser::ParseError;
use log::debug;

use crate::{
    ccl::{
        Expr, Name, channelize,
        infer::{
            InferError, TypeInferenceContext, check_mut_discipline, check_mut_write_targets,
            check_pre_channelize, infer, typecheck,
        },
        inline, lambda_elim,
        lower::{LoweringContext, LoweringError, lower_stmts},
        mut_elim,
        panes::gate_leaks,
        planning,
        provenance::{
            Leak, LoweringSession, NodeId, PhaseScope, ProvenanceTable, SourceProjection,
            TableSession, fold, fold_lowering,
        },
        symbolic::{symbolic, symbolic_typed},
        transact_phase, uniquify,
    },
    interpreter::{
        Consumer, DataSink, DataSourceDomainExtentImpl, Scheduler, StdinDataSource,
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
/// consistency checks (`typecheck`, `check_fully_typed` between phases,
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
    /// The (parseable) AST uses a construct the lowering phase does not
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
    /// present, since an unrecorded mint surfaces as `Leak::Unrecorded` at the
    /// fold. Produced by
    /// [`fold_lowering`](crate::ccl::provenance::fold_lowering) at the
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
    /// The post-as-of-read IR snapshot, taken after
    /// [`transact_phase::rewrite_as_of_reads`](crate::ccl::transact_phase::rewrite_as_of_reads).
    ///
    /// Distinct from [`post_channelize_ir`](Self::post_channelize_ir) because
    /// that rewrite runs between the two: on a program with a fed-out mutable
    /// read the trees differ, and on every other program they agree node for
    /// node. Isolating it is what lets the pair ending here gate that one
    /// rewrite rather than fold it in with lambda elimination.
    pub post_as_of_read_ir: Expr,
    /// The post-lambda-elim IR snapshot, taken after
    /// [`lambda_elim::run`](crate::ccl::lambda_elim::run).
    ///
    /// The pass re-mints nearly every pass-through node, so almost no id here is
    /// shared with the pane before it and the pair's relation falls to the
    /// parents walk rather than to shared ids. That is what the pair measures.
    pub post_lambda_elim_ir: Expr,
    /// The compile's provenance record: `NodeId → { parents, blame, rule }`, one
    /// row per node a phase produced, written by the recorder as those phases run
    /// ([`crate::ccl::provenance`]).
    ///
    /// One table covers the whole compile, because a row's key is a
    /// process-unique `NodeId` and needs no phase set to disambiguate it; a row's
    /// `via` is what a fold between two panes restricts by. The phases that record are
    /// [`Phase::Infer`] (everything monomorphization mints inside `infer`, which
    /// bridges the pre-inference ⇄ post-inference panes) and [`Phase::Inline`],
    /// [`Phase::Transact`], [`Phase::Letrec`], [`Phase::Channelize`] (the phases
    /// between the post-inference and post-channelize snapshots) — see [`PANES`],
    /// which declares which phases each pane pair folds.
    ///
    /// Rows exist only for nodes a recording produced, so an untouched node has
    /// none — it was never rewritten. Refinement-predicate interiors are rows
    /// like any other: `collect_tree_ids` enumerates them, so the fold must
    /// explain them, and `PredMemo::rebuild` records a derived predicate against
    /// the one it was built from. What is not recorded is planning **raising** a
    /// predicate back into the main tree; see `design/provenance.md`, "Known
    /// prerequisites for panes past `post-planning`".
    ///
    /// Empty when capture is switched off — no phase scope is opened then, so
    /// every flush is a no-op — see [`provenance_capture_enabled`]. This is the
    /// authoritative provenance surface:
    /// [`materialize_panes`](Self::materialize_panes) folds it for each pane
    /// pane pair.
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
}

/// The compiler phase that rewrote a node — a
/// [`RewriteTag`](crate::ccl::provenance::RewriteTag)'s `via` column.
///
/// Minimal on purpose: only the phases that *mint or restructure* expression
/// nodes (and therefore need to record why a node exists) appear here.
///
/// **Declaration order is pipeline order**, and the derived [`Ord`] is therefore
/// the order [`compile_program`] runs them in. That is what makes a phase
/// *range* meaningful: [`ProvenanceTable::deaths`] takes two phases and reads
/// every phase between them, so a variant declared out of pipeline order would
/// silently put the wrong phases inside a caller's range. Adding a phase means
/// declaring it at the point it runs.
///
/// `Phase` and [`crate::ccl::names::SyntheticKind`] (which tracks *binder*
/// provenance: `Pair`, `Mono`, `SolverArg`, …) are deliberately separate enums,
/// neither wrapping the other — one tags `NodeId`s (expression nodes), the other
/// tags `Uid`s (binders), and merging them would put a binder-role payload on
/// the column that names a phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum Phase {
    /// Lowering CHL source into CCL.
    Lower,
    /// The 1:1 binder rename in [`crate::ccl::uniquify`]. **Never
    /// constructed**: `uniquify` preserves every node id, so it has nothing to
    /// record. The variant exists so the axis covers every phase.
    Uniquify,
    /// Type inference ([`crate::ccl::infer`]): the phase that bridges the
    /// pre-inference and post-inference panes. Monomorphization is what mints
    /// inside it — cloning a generalized definition's subtree once per distinct
    /// resolved type — and inference is the recorded span, since a scope covers
    /// the whole call and nothing inside it opens a narrower one.
    Infer,
    /// UDF inlining + beta-reduction ([`crate::ccl::inline`]): the phase that
    /// runs between the post-inference and post-channelize snapshots. Mostly
    /// id-preserving (a rebuilt node carries its input id); its genuine
    /// deviations are the fan-out clones at multi-use call sites (`Copy`s) and
    /// the wrappers/redexes it drops (`Transform` discards).
    Inline,
    /// The transaction slice of the unified mutability phase
    /// ([`crate::ccl::transact_phase::run`]): stripping `with begin():` writer
    /// sites and assembling the `get_prev_txn`-guarded `LetRec` (histories,
    /// commit records, taps). Runs between the post-inference and post-channelize
    /// snapshots (after `Inline`, before `Channelize`).
    Transact,
    /// The induction slice of the unified mutability phase
    /// ([`crate::ccl::mut_elim::run`]): folding direct-mirror `For`/`MutWrite`
    /// loops into guarded `LetRec` induction histories. Runs between the
    /// post-inference and post-channelize snapshots (after `Transact`, before
    /// `Channelize`).
    Letrec,
    /// Channelization ([`crate::ccl::channelize`]): channelizing
    /// `Defer`/`Feed`/`Define` into collection unions and contribution records.
    /// Mostly a 1:1 transform (ids preserved), but its channelization machinery
    /// synthesizes new nodes (channel unions, contribution records, floated
    /// lambdas, DI wrappers) that are tagged `{via: Channelize, nature: Machinery}`.
    Channelize,
    /// The as-of-read rewrite
    /// ([`crate::ccl::transact_phase::rewrite_as_of_reads`]): turning a
    /// read-only reply that reads a mutable variable out of its block into an
    /// outer-indexed as-of join.
    ///
    /// Its code lives in `transact_phase`, but a phase is declared where the
    /// rewrite *runs*, not where its code sits — this one runs after
    /// `Channelize` and before `LambdaElim`. Reusing [`Transact`](Self::Transact)
    /// for it would put one phase on both sides of the post-channelize pane, and
    /// a fold restricting by that phase would resolve straight past it.
    AsOfRead,
    /// Lambda elimination: synthesizing point-free combinators (`Compose`,
    /// `Zip`, `Id`) from explicit lambdas.
    LambdaElim,
    /// Join/dataflow planning: hash-join and restrict scaffolding, clause
    /// fusion, refinement-predicate compilation.
    Planning,
}

/// Ids carried by two *distinct* predicate terms, or by a predicate term and the
/// main tree — the half of uniqueness [`duplicate_node_ids`] cannot answer.
///
/// Dedups by `Rc` pointer first: one term riding many type slots is one term and
/// shares its ids with itself, and that sharing is an invariant the predicate
/// domain is built on (`design/type-inference.md`, "Sharing is an invariant, not
/// an optimization detail"). What survives the dedup is two live terms on one
/// id-set. A raw id-set walk over the type slots cannot report that, because it
/// cannot tell the sharing apart from the collision — which is why the main-tree
/// walk stays `Rc`-blind and this one does not.
///
/// Both walks run at every boundary, from [`assert_unique_node_ids`].
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
        if let Type::Refinement(_, rs) = t {
            for r in rs.iter() {
                let key = Rc::as_ptr(&r.predicate) as usize;
                if let std::collections::hash_map::Entry::Vacant(slot) = acc.entry(key) {
                    let mut s = HashSet::new();
                    ids_of(&r.predicate, &mut s);
                    slot.insert(s);
                }
                from_expr_ty(&r.predicate, acc);
            }
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
pub(crate) fn collect_main_tree_ids(expr: &Expr) -> HashSet<NodeId> {
    fn go(e: &Expr, acc: &mut HashSet<NodeId>) {
        acc.insert(e.node_id());
        e.walk_children(|c| go(c, acc));
    }
    let mut acc = HashSet::new();
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
pub(crate) fn collect_tree_ids(expr: &Expr) -> HashSet<NodeId> {
    use crate::ccl::TypedExprNode;
    use crate::ccl::ty::Type;

    fn from_ty(t: &Type, acc: &mut HashSet<NodeId>) {
        if let Type::Refinement(_, refinements) = t {
            // Every refinement's predicate rides the slot, so every one of them
            // carries ids the projections must explain.
            for r in refinements.iter() {
                from_expr(&r.predicate, acc);
            }
        }
        t.walk_children(|c| from_ty(c, acc));
    }

    fn from_expr(e: &Expr, acc: &mut HashSet<NodeId>) {
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
        // A binder's declared type and its annotation are type slots too. This
        // walk and `TypedExpr::walk_type_slots` enumerate the same domain, and
        // must: the rewriting passes reach predicates through `walk_type_slots`,
        // so anything it covers and this does not is a predicate a pass may
        // rebuild while the fold has never enumerated the original — which reads
        // as `DanglingParent` against an id the input pane demonstrably holds.
        // `f: (Int => {Int where _ == 9}) = …` is the shape: the predicate rides
        // the `let` binder's annotation and nothing else.
        e.walk_binders(|b| {
            from_ty(&b.ty, acc);
            if let Some(ann) = &b.user_annotation {
                from_ty(ann, acc);
            }
        });
        e.walk_children(|c| from_expr(c, acc));
    }

    let mut acc = HashSet::new();
    from_expr(expr, &mut acc);
    acc
}

/// Every duplicated [`NodeId`] over the **main tree** — the `walk_children`
/// node-set, refinement predicates excluded. Returns `(id, node kind)` for each
/// occurrence *beyond the first*.
///
/// Predicates are excluded because they are reached through `Rc`s a walk visits
/// many times over, so a second sighting of an id is not yet a collision;
/// [`predicate_id_collisions`] answers that domain, dedupping by `Rc` first.
fn duplicate_node_ids(expr: &Expr) -> Vec<(NodeId, &'static str)> {
    fn walk(e: &Expr, seen: &mut HashSet<NodeId>, dups: &mut Vec<(NodeId, &'static str)>) {
        if !seen.insert(e.node_id()) {
            dups.push((e.node_id(), e.node.kind_name()));
        }
        e.walk_children(|c| walk(c, seen, dups));
    }
    let mut seen = HashSet::new();
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
/// This asserts a *tree invariant* at a phase boundary and encodes no phase order,
/// so it is robust to phase reordering (a moved phase carries its check with it).
/// It catches the *class* of preserve-as-mint / clone-without-freshen bugs
/// across the whole test suite, not just a crafted program.
///
/// Uniqueness spans the same ids [`collect_tree_ids`] enumerates, and takes two
/// walks to check because the two domains share differently.
/// [`duplicate_node_ids`] is `Rc`-blind and covers the main tree, where a second
/// sighting of an id is a collision outright. [`predicate_id_collisions`] dedups
/// by `Rc` first and covers the predicate interiors, where one term riding many
/// type slots shares its ids with itself. See `design/provenance.md`, "Walking
/// the ids". Gated
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
    let pred_dups = predicate_id_collisions(expr);
    assert!(
        pred_dups.is_empty(),
        "predicate node-id uniqueness invariant violated at `{boundary}`: {} \
         collision(s) (id, domains): {:?}",
        pred_dups.len(),
        pred_dups
    );
    // The `Default`/`mem::take` sentinel (see `NodeId::PLACEHOLDER`) is a
    // transient throwaway that must always be overwritten before it reaches a
    // phase boundary; a persisted placeholder means a `mem::take` slot was left
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

/// Gates [`MaterializedPanes::gated_pane_pairs`]'s leak classes on **every**
/// compile (`=1`), making the gate's corpus whatever the caller compiles.
const PROVENANCE_GATE_ENV: &str = "CAMBRA_PROVENANCE_GATE";

/// Narrows an audit's live set to the main tree, excluding refinement-predicate
/// interiors (`=0`). Predicate-inclusive otherwise — see
/// [`provenance_predicates_live`].
const PROVENANCE_PREDICATES_ENV: &str = "CAMBRA_PROVENANCE_PREDICATES";

/// Repetition count for the ignored perf driver. Test-only — the driver is a
/// `#[test]`, so the name is dead in a lib build; it lives here rather than
/// beside its reader so that adding a fifth switch means editing one block.
#[cfg(test)]
pub(crate) const PERF_REPS_ENV: &str = "CAMBRA_PERF_REPS";

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
/// dangle as [`Leak::DanglingParent`] with nothing actually unrecorded. Defaulting
/// to the narrow set made the plain invocation report ~166 folds of noise on
/// the pipeline corpus and buried real defects in it.
///
/// [`materialize_panes`]: CompiledProgram::materialize_panes
fn provenance_predicates_live() -> bool {
    !std::env::var(PROVENANCE_PREDICATES_ENV).is_ok_and(|v| v == "0")
}

/// Whether [`compile_program`] opens the per-phase recorder scopes that fill
/// [`CompiledProgram::provenance_table`]. On by default.
///
/// The switch changes only whether a scope is opened; every recording hook is
/// already a no-op outside one (`RECORDING_STACK` empty / no ambient phase).
///
/// A [`ProvenanceAudit`] span opens its own scope, so naming one turns pane
/// capture off.
pub(crate) fn provenance_capture_enabled() -> bool {
    !std::env::var(PROVENANCE_ENV).is_ok_and(|v| v == "0") && provenance_audit_span().is_none()
}

/// Whether every compile folds every pane pair and gates the leak classes,
/// rather than only the programs a test asks about.
///
/// **What this buys.** The always-on gate is
/// `pane_pair_folds_have_no_structural_leaks`, whose corpus is the handful
/// of programs listed in `corpus()`. That is a *sample*, and a recording gap in
/// a shape the sample misses is invisible: the unrecorded
/// `fold_induction_loop` call in `transact_phase` (a commit decision reading
/// another loop's accumulator) and `flatten_spine`'s value-position writer hoist
/// both sat outside it. With this on, the corpus is every program the caller
/// compiles — point it at `tests/compilation_pipeline` and the gate covers the
/// whole suite instead of the programs `corpus()` lists.
///
/// Off by default because it folds the table twice per compile, which is
/// superlinear work the ordinary pipeline does not need; CI turns it on. It is
/// **not** a substitute for the sampled gate, which stays always-on so a plain
/// `cargo test` still fails on the common shapes.
///
/// Requires capture: with `CAMBRA_PROVENANCE=0`, or under an audit span (which
/// takes the phase scopes for itself), the table is empty and every output node
/// would read as unrecorded. Both are honoured rather than asserted, so a run
/// can name one without also having to unset this.
fn provenance_gate_every_compile() -> bool {
    std::env::var(PROVENANCE_GATE_ENV).is_ok_and(|v| v != "0") && provenance_capture_enabled()
}

/// Run `f` with `phase` installed as the recorder's ambient phase, so every row a
/// recording inside it writes is tagged with that phase. With `capture` false this
/// is exactly `f()` — no scope, and every construction hook stays a no-op.
///
/// The phase identity lives in the *data* — the row's `RewriteTag`, completed
/// from the scope when a guard drops — which is why one helper covers every phase
/// regardless of its signature: the phases here are free functions of four
/// different shapes and nothing is threaded through them.
fn recorded<R>(capture: bool, phase: Phase, f: impl FnOnce() -> R) -> R {
    if !capture {
        return f();
    }
    let _scope = PhaseScope::enter(phase);
    f()
}

/// A driver-capture audit over one span of the pipeline: install a phase recorder at
/// the input pane, fold at the output pane, and print what the capture explains.
///
/// Opt-in by naming a span in `CAMBRA_PROVENANCE_AUDIT` — the spans opened below
/// are `full`, `letrec` and `mutelim` — so the whole test suite can run either
/// way. It is a **measurement**, not a gate: nothing declares a fate, so every
/// genuinely-dead input id reaches the audit through the fold's death
/// collection, which it counts apart from the [`Leak`]s that really are
/// recording bugs.
///
/// A span survives gating when its enclosing pair bundles more phases than the
/// span does: the `letrec` and `mutelim` spans below each isolate a phase inside
/// the `post-inference → post-channelize` pair. See
/// `src/ccl/design/provenance.md`, "What gating every pair does not retire".
struct ProvenanceAudit {
    span: &'static str,
    state: Option<(PhaseScope, HashSet<NodeId>)>,
}

impl ProvenanceAudit {
    /// The `via` an audit's rows carry. A span covers several phases under one
    /// scope, so no single phase is the truthful answer; the tag is nominal, and
    /// naming it once keeps the scope's tag and the phases the fold restricts by
    /// from disagreeing about which nominal phase it is.
    const AUDIT_VIA: Phase = Phase::Planning;

    /// The audit's live set: [`collect_main_tree_ids`]'s `walk_children` domain,
    /// or — when [`provenance_predicates_live`] says so — [`collect_tree_ids`]'s
    /// predicate-inclusive domain.
    ///
    /// Both arms are real and differ: the narrow one is *not* the id domain any
    /// more. `collect_tree_ids` became predicate-inclusive, which briefly made
    /// this switch inert (both arms computing the same set) and its own doc
    /// comment false. Keeping a named narrow walk is what makes the comparison
    /// measurable rather than a no-op.
    fn live_ids(expr: &Expr) -> HashSet<NodeId> {
        if provenance_predicates_live() {
            collect_tree_ids(expr)
        } else {
            collect_main_tree_ids(expr)
        }
    }

    /// Open the audit if [`provenance_audit_span`] names this `span`. Spans are
    /// mutually exclusive because a phase scope is per-thread and non-reentrant;
    /// naming them lets a run narrow the measurement to the phases under study
    /// instead of the whole tail of the pipeline.
    fn start(span: &str, name: &'static str, input: &Expr) -> Self {
        let on = provenance_audit_span().is_some_and(|w| w == span);
        ProvenanceAudit {
            span: name,
            state: on.then(|| (PhaseScope::enter(Self::AUDIT_VIA), Self::live_ids(input))),
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
        let Some((rows, projection, deaths, leaks)) =
            crate::ccl::provenance::with_active_table(|table| {
                let (_map, projection, deaths, leaks) = fold(
                    table,
                    &[Self::AUDIT_VIA],
                    &input_ids,
                    &output_ids,
                    &SourceProjection::new(),
                );
                (table.len(), projection, deaths, leaks)
            })
        else {
            return;
        };
        let mut counts = BTreeMap::<&str, usize>::new();
        for l in &leaks {
            *counts
                .entry(match l {
                    Leak::Unrecorded { .. } => "Unrecorded(output not covered by any recording)",
                    Leak::DanglingParent { .. } => "DanglingParent",
                })
                .or_default() += 1;
        }
        eprintln!(
            "[provenance-audit {}] rows={rows} input={} output={} attributed={} deaths={} \
             leaks={counts:?}",
            self.span,
            input_ids.len(),
            output_ids.len(),
            projection.len(),
            deaths.len(),
        );
    }
}

/// `check_pre_channelize` as a wall between two phases. It is the relaxed
/// pre-channelize check, which permits the transient `Feed` /
/// `Infer`-channel-domain types only channelization erases.
///
/// A failure is a compiler bug, with one exception: residual `Type::Infer`
/// variables, which inference deliberately tolerates for a generalized
/// definition the program never exercises at a concrete type (see
/// `Type::Infer`'s invariant). That residue is an *ambiguous program* — a user
/// error — so it is rendered as a diagnostic; anything else panics, naming
/// `produced_by`.
fn pre_channelize_wall(expr: &Expr, produced_by: &str) -> Result<(), Vec<CompileError>> {
    check_pre_channelize(expr).map_err(|errs| {
        if errs
            .iter()
            .all(|e| matches!(e, InferError::UnresolvedInfer { .. }))
        {
            errs.into_compile_errors()
        } else {
            panic!("{produced_by} created invalid expr: {errs:?}")
        }
    })
}

/// The two user-facing mutability rules, checked on the fully-typed,
/// still-`Mut`-bearing tree — after [`pre_channelize_wall`], before inlining.
///
/// Both need the pre-inline `Apply`/parameter structure and the coalesced `.ty`
/// slots and `user_annotation`s. Unlike the surrounding [`pre_channelize_wall`]
/// calls (compiler-bug backstops), these are user errors:
///
/// - `check_mut_discipline` — the second-class `Mut` discipline
///   (`src/ccl/design/mutability.md`, "No aliasing: `Mut` values are second-class
///   (downward-only)"): no aliasing or nesting a mutable reference.
/// - `check_mut_write_targets` — every `:=` / `+=` write targets a mutable
///   variable, never a shadowing rebind of an immutable. Load-bearing rather
///   than a formality: lowering emits a `MutWrite` for any `x := e` whose name is
///   already in scope, mutable variable or not (see `src/ccl/design/mutability.md`,
///   "Mutability is the type (no lowering registry)"), so this is what rejects a
///   write to an immutable binding — or to one monomorphization has since dropped.
fn check_mut_rules(expr: &Expr) -> Result<(), Vec<CompileError>> {
    check_mut_discipline(expr).map_err(|errs| errs.into_compile_errors())?;
    check_mut_write_targets(expr).map_err(|errs| errs.into_compile_errors())
}

/// The transact phase's four rejections, run on the inlined, typed tree before
/// [`transact_phase::run`] strips the sites they inspect.
///
/// - `check_no_nested_transactions` — a transactional writer reaching a `with
///   begin():` block via a function call. The callee's inlined `For` would
///   otherwise be silently absorbed into the outer block's read-your-writes env,
///   dropping its commit.
/// - `check_no_induction_only_transactions` — an induction accumulator written
///   inside a block with no mutable variable write is a no-atomicity transaction.
/// - `check_no_guarded_induction_write_in_block` — a *guarded* induction write
///   inside a committing block (`balance := …; if p: cnt += 1`) is not liftable
///   and would be silently dropped from the decision record. A debug-only assert
///   would miss it in release.
/// - `check_await_final_linearity` — `await_final` consumes its mutable variable:
///   no mention may follow its await. A statement-order rule lowering cannot see,
///   since it builds its chain right-to-left, and a callee's mention only becomes
///   a read, a write, or a `Begin` once inlined.
fn check_transact_rejections(
    expr: &Expr,
    txn_mut_vars: &HashSet<Name>,
) -> Result<(), Vec<CompileError>> {
    let reject = |msg: String| vec![CompileError::Unsupported(msg)];
    transact_phase::check_no_nested_transactions(expr, txn_mut_vars).map_err(reject)?;
    transact_phase::check_no_induction_only_transactions(expr, txn_mut_vars).map_err(reject)?;
    transact_phase::check_no_guarded_induction_write_in_block(expr, txn_mut_vars)
        .map_err(reject)?;
    transact_phase::check_await_final_linearity(expr).map_err(reject)
}

/// What a frontend run hands back besides the tree it stopped at.
struct Frontend {
    /// The tree at the requested stop [`Phase`]'s output.
    expr: Expr,
    /// The tree at each requested phase output, keyed by the phase whose output
    /// it is. A **pane** is exactly this: a captured phase output that outlives
    /// the run.
    panes: BTreeMap<Phase, Expr>,
    /// The surface AST lowering consumed, retained for source-level queries.
    module: chl_parser::ast::Module,
    /// Sink bindings discovered during lowering. Drained before the sources,
    /// which is the order [`LoweringContext`] requires.
    sink_bindings: HashMap<String, Arc<dyn DataSink>>,
    /// Every lowered node's `SourceAttribution`, the base every later fold
    /// bottoms out in and the source release `InferError` diagnostics resolve
    /// against one-hop.
    lowering_projection: SourceProjection,
    /// Open when the run recorded. The caller drains it once nothing else will
    /// record, so the timing matches a compile that never split.
    table_session: Option<TableSession>,
}

/// Capture `phase`'s output if asked for, and say whether the run stops here.
///
/// The one place a phase boundary is expressed, so "capture a pane" and "stop
/// for a diff" are the same event at the same position. The stop test is `>=`
/// over [`Phase`]'s declaration order, which is pipeline order.
fn at_phase_output(
    phase: Phase,
    expr: &Expr,
    stop: Phase,
    capture: &[Phase],
    panes: &mut BTreeMap<Phase, Expr>,
) -> bool {
    if capture.contains(&phase) {
        // A pane observes the live tree at a point in time, so it preserves ids.
        // A freshening clone would hand the pane a structurally identical
        // program sharing no identity with the one it is meant to snapshot.
        panes.insert(phase, expr.clone_preserving_ids());
    }
    phase >= stop
}

/// The compiler frontend: source in, a CCL tree at `stop`'s output out.
///
/// **This is the only place the phase sequence and its checks are written.**
/// [`compile_program`] runs it to [`Phase::Planning`] and continues into
/// operator conversion; [`compile_to`] runs it to whichever phase a diff is
/// being taken at and stops. A check added here therefore lands on both, which
/// is what keeps a stopped tree from being one the real pipeline would have
/// rejected.
///
/// `capture` names the phase outputs to retain as panes; `record` selects
/// whether the run installs the provenance table and opens the per-phase
/// recorder scopes. Nothing else about the two callers differs.
fn run_frontend(
    ctx: &mut GlobalContext,
    code: &str,
    stop: Phase,
    capture: &[Phase],
    record: bool,
) -> Result<Frontend, Vec<CompileError>> {
    // The parse and lower stages accumulate errors before bailing: when the
    // parser recovers from a syntax error it still produces a partial AST, which
    // lowering can run on and report its own errors against, so the user sees
    // everything at once. Inference and below assume a well-typed tree with no
    // `Error` placeholders, so they are skipped when anything earlier failed.
    let mut errors: Vec<CompileError> = Vec::new();

    // The node table spans the **whole compile**, not a phase: its rows are keyed
    // by `NodeId`, which is unique for the life of the process, so every phase
    // session's flushes mirror into one table with no possibility of collision.
    // Installed before the first session opens (the lowering one) and drained
    // below; every early return drops it, clearing the slot.
    let table_session = record.then(TableSession::install);

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
    // projection. It must fully drain before the first phase (`Infer`) session opens.
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
    let sink_bindings = ctx.lowering_ctx().take_sink_bindings();

    // Drain the lowering log and fold it once, at the lowering→pipeline
    // handoff (before uniquify/inference, so the release `InferError` read timing
    // is unchanged), into the always-on **lowering projection**: every lowered
    // node's [`SourceAttribution`], keyed by NodeId. It is the base every later
    // pane fold bottoms out in, and the source the release `InferError`
    // diagnostics resolve against one-hop. `uniquify` preserves every id in
    // place, so the projection's keys survive into the pre-inference pane.
    //
    // The fold's leak taxonomy enforces mint coverage: an unrecorded lowering
    // mint surfaces as `Leak::Unrecorded` (every output-tree node must be
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
        let (projection, leaks) = fold_lowering(&lowering_log, &output_ids);
        gate_leaks(&leaks, "lowering");
        projection
    };

    debug!("Lowered (pre-channelize):\n{}", symbolic(&expr));

    let mut panes = BTreeMap::new();
    if at_phase_output(Phase::Lower, &expr, stop, capture, &mut panes) {
        return Ok(Frontend {
            expr,
            panes,
            module,
            sink_bindings,
            lowering_projection,
            table_session,
        });
    }

    // α-uniquify all binders (Barendregt convention): every binding site gets
    // a globally fresh `Name` uid, so shadowing ceases to exist before any
    // phase that compares names. Must run before channelization — channelize's
    // rewrites splice and rename terms under the assumption that distinct
    // binders are distinct names. (Channelize now runs after inference; see below.)
    expr = uniquify::run(expr);

    let expr = run_passes(
        ctx,
        expr,
        stop,
        capture,
        record,
        &lowering_projection,
        &mut panes,
    )?;
    Ok(Frontend {
        expr,
        panes,
        module,
        sink_bindings,
        lowering_projection,
        table_session,
    })
}

/// The phase sequence, from the α-uniquified tree to `stop`'s output.
///
/// Split out of [`run_frontend`] only so each phase boundary can `return` the
/// tree; the two are one pipeline. Every phase ends with one
/// [`at_phase_output`] call, which is both where a pane is taken and where a
/// stop happens.
fn run_passes(
    ctx: &mut GlobalContext,
    mut expr: Expr,
    stop: Phase,
    capture: &[Phase],
    record: bool,
    lowering_projection: &SourceProjection,
    panes: &mut BTreeMap<Phase, Expr>,
) -> Result<Expr, Vec<CompileError>> {
    // Phase recording for the rows the pane-pair folds read. One scope per
    // phase, opened and closed in place: a phase scope is per-thread and
    // non-reentrant, so the scopes are sequential, never nested.
    let capture_provenance = record && provenance_capture_enabled();

    if at_phase_output(Phase::Uniquify, &expr, stop, capture, panes) {
        return Ok(expr);
    }

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
    let infer_outcome = recorded(capture_provenance, Phase::Infer, || {
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
    pre_channelize_wall(&expr, "Inference")?;

    // Enforce the second-class `Mut` discipline (`src/ccl/design/mutability.md`,
    // "No aliasing: `Mut` values are second-class (downward-only)") on the
    // fully-typed, still-`Mut`-bearing tree — after the consistency wall,
    // before inlining. It needs the pre-inline `Apply`/parameter structure
    // (rule 1's argument check) and the coalesced `.ty` slots and
    // `user_annotation`s. Unlike the surrounding `check_pre_channelize` walls
    // (compiler-bug backstops), these are user errors: aliasing or nesting a
    // mutable reference.
    check_mut_rules(&expr)?;

    // Enforce that every `:=` / `+=` write targets a mutable variable (a write is
    // never a shadowing rebind of an immutable). Post-inference so binder types
    // are resolved, post-`uniquify` so write targets carry their binder's
    // α-unique name — see `check_mut_write_targets`. Load-bearing rather than a
    // formality: lowering emits a `MutWrite` for any `x := e` whose name is already in
    // scope, mutable variable or not (see `src/ccl/design/mutability.md`, "Mutability is the
    // type (no lowering registry)"), so this is what rejects a write to an immutable
    // binding — or to one monomorphization has since dropped.

    // Inline UDFs *before* channelize: a defer-mediating UDF (`λ out → out << e`)
    // or a cross-function writer is beta-reduced to its call site before
    // channelize routes feeds and before the unified letrec phase folds writers,
    // both of which need their targets lexically present. Inlining runs on the
    // still-defer-bearing tree (Defer/Feed nodes and `Feed` types present) via
    // the defer-aware `Subst` engine (which renames a fed-to handle on
    // beta-reduction) and preserves defer-returning generators, so the
    // post-inline wall is the relaxed `check_pre_channelize`, not strict
    // `typecheck`.
    // Inference mints predicates (`lit_singleton`) and clones a definition per
    // instantiation (`specialize_use`), so its output is checked before the pane
    // is taken off it.
    assert_unique_node_ids(&expr, "post-inference");

    // Retain the post-inference IR for the inspector before `inline` consumes
    // `expr`. This is the source-shaped, fully-typed anchor (lambdas intact, not
    // yet point-free; inline/transact/letrec/channelize/lambda_elim/planning have
    // not run). `ast` (`join_planned`) is the *wrong* tree for a source
    // view — `lambda_elim`/`planning` re-mint ids and produce execution shape.
    // See `CompiledProgram::post_inference_ir`.
    // A pane snapshot; see `pre_inference_ir`.
    if at_phase_output(Phase::Infer, &expr, stop, capture, panes) {
        return Ok(expr);
    }

    // Driver-capture audit span: post-inference pane in, and out at the **last
    // instrumented pane**, which is now the last pane — `join-planned`, covering
    // inline, transact, mut_elim, channelize, the as-of-read rewrite, lambda
    // elimination and planning.
    //
    // The endpoint is chosen rather than inherited. An audit measures what the
    // recordings explain, so a span running past the last instrumented phase
    // reports every node the uninstrumented tail mints as a defect — a number
    // that cannot reach zero however correct the recording is, which makes the
    // audit read as a broken gate instead of a measurement. Every phase that
    // rewrites expression nodes now records, so the span reaches the end of the
    // pipeline; operator conversion is past it and has no node identity to
    // record against.
    let audit = ProvenanceAudit::start("full", "post-inference..join-planned", &expr);
    // A narrower audit span over just the mutability phases (inline, transact,
    // mut_elim), which is where the fate-prediction question lives.
    let audit_letrec = ProvenanceAudit::start("letrec", "post-inference..post-letrec", &expr);

    expr = recorded(capture_provenance, Phase::Inline, || {
        inline::inline_capability_lambdas(expr)
    });
    assert_unique_node_ids(&expr, "post-inline");
    debug!("UDFs inlined CCL:\n{}", symbolic(&expr));
    pre_channelize_wall(&expr, "UDF inlining")?;
    if at_phase_output(Phase::Inline, &expr, stop, capture, panes) {
        return Ok(expr);
    }

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
    check_transact_rejections(&expr, &txn_mut_vars)?;

    expr = recorded(capture_provenance, Phase::Transact, || {
        transact_phase::run(expr, &txn_mut_vars)
    })
    .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    assert_unique_node_ids(&expr, "post-transact");
    debug!("Transact phase CCL:\n{}", symbolic(&expr));
    check_pre_channelize(&expr).expect("transact phase produced an inconsistent tree");
    if at_phase_output(Phase::Transact, &expr, stop, capture, panes) {
        return Ok(expr);
    }

    // The unified letrec phase: direct-mirror mutation loops (`For` /
    // `MutWrite`) become causal `LetRec` groups — mutable histories over
    // the induction domain, per src/ccl/design/mutability.md. Runs after
    // inlining (so cross-function writers land at their call sites) and
    // *before* channelize, so a per-iteration feed inside a loop is
    // hoisted to an ordinary feed of the loop's history for channelize to route.
    // The tree still carries Defer/Feed here, so the check is the relaxed
    // pre-channelize one.
    // An audit span over `mut_elim` alone — the phase whose fate prediction driver
    // capture is meant to delete.
    let audit_mutelim = ProvenanceAudit::start("mutelim", "post-transact..post-letrec", &expr);
    let phase_out = recorded(capture_provenance, Phase::Letrec, || mut_elim::run(expr));
    audit_mutelim.finish(&phase_out);
    assert_unique_node_ids(&phase_out, "post-letrec-run");
    audit_letrec.finish(&phase_out);
    debug!("Letrec phase CCL:\n{}", symbolic(&phase_out));
    check_pre_channelize(&phase_out).expect("letrec phase produced an inconsistent tree");
    if at_phase_output(Phase::Letrec, &phase_out, stop, capture, panes) {
        return Ok(phase_out);
    }

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
    let mut channelized = recorded(capture_provenance, Phase::Channelize, || {
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
    if at_phase_output(Phase::Channelize, &channelized, stop, capture, panes) {
        return Ok(channelized);
    }

    // Fed-out mutable variable reads: rewrite a read-only reply that reads a mutable variable out of
    // its block into an outer-indexed as-of join (an as-of read at the reading
    // transaction's arbitrary commit position), *before* lambda elimination — so a
    // computed reply (`resp << balance + 1`) stays a lambda the elim phase point-frees,
    // rather than a point-free `const` a planning-time recognizer would have to
    // reject. Uniform across the reading loop's domain. See
    // `transact_phase::rewrite_as_of_reads`.
    recorded(capture_provenance, Phase::AsOfRead, || {
        transact_phase::rewrite_as_of_reads(&mut channelized)
    })
    .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    assert_unique_node_ids(&channelized, "post-as-of-read");
    typecheck(&channelized).expect("as-of-read rewrite produced an ill-typed tree");
    if at_phase_output(Phase::AsOfRead, &channelized, stop, capture, panes) {
        return Ok(channelized);
    }

    let lambda_elim = recorded(capture_provenance, Phase::LambdaElim, || {
        lambda_elim::run(channelized)
    })
    .errs()?;
    assert_unique_node_ids(&lambda_elim, "post-lambda-elim");
    debug!("λ-eliminated CCL:\n{}", symbolic(&lambda_elim));
    debug!("λ-eliminated typed CCL:\n{}", symbolic_typed(&lambda_elim));

    // `typecheck` enforces hole-freeness as its first phase, so this call
    // alone covers both checks.
    typecheck(&lambda_elim).expect("type error after lambda elimination");
    if at_phase_output(Phase::LambdaElim, &lambda_elim, stop, capture, panes) {
        return Ok(lambda_elim);
    }

    // Recognition: lower each causal group — now in its point-free normal
    // form — onto the domain-parameterized `Transact` carrier (a
    // `get_prev_txn` transaction group → `Transact{Txn}`; a `get_prev_seq`
    // induction group → `Transact{iteration extent}`) so planning stages the
    // writer sources and operator conversion picks the engine on the domain.
    // Running post-elim is what keeps ONE letrec representation through
    // channelize and lambda_elim; the point-free guard matcher re-checks
    // causality at this wall. See the `mut_elim` recognition docs.
    // One scope over both halves of planning: they tag identically, and the
    // typecheck between them mints nothing, so splitting would buy a window in
    // which a recording writes nothing and nothing says why.
    let join_planned = recorded(capture_provenance, Phase::Planning, || {
        let recognized = planning::plan_loops(lambda_elim);
        debug!("Letrec recognized CCL:\n{}", symbolic(&recognized));
        typecheck(&recognized).expect("letrec recognition produced an ill-typed tree");
        planning::run(recognized)
    });
    // The last instrumented pane: see the span's own note at `ProvenanceAudit::start`.
    audit.finish(&join_planned);
    assert_unique_node_ids(&join_planned, "post-planning");
    debug!(
        "Join-planned CCL:\n{} : {}",
        symbolic(&join_planned),
        join_planned.ty
    );
    debug!("Join-planned CCL:\n{}", symbolic_typed(&join_planned));

    // Planning is the one phase that introduces `iterate` / `restrict` /
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

    at_phase_output(Phase::Planning, &join_planned, stop, capture, panes);
    Ok(join_planned)
}

/// Compile `code` through `phase`, ready to pass to [`crate::ccl::diff::diff`].
///
/// Runs [`run_frontend`] — the same phases and the same checks
/// [`compile_program`] runs — stopping at `phase`'s output rather than
/// continuing into the operator graph, and retaining no panes and no provenance.
/// A program `compile_program` refuses therefore yields no tree here.
///
/// Every phase output is a consistent tree (each has a wall after it), so any
/// `Phase` is a legal stop. Which ones answer which question — and which ones a
/// diff should be taken at — is `src/ccl/design/diffing.md`, "Which phase to diff".
pub fn compile_to(code: &str, phase: Phase) -> Result<Expr, Vec<CompileError>> {
    let mut ctx = GlobalContext::new();
    Ok(run_frontend(&mut ctx, code, phase, &[], false)?.expr)
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
    // The frontend is [], shared with []: parse through
    // join planning, every check between, and the three panes the inspector
    // reads — each of which is a captured phase output.
    //
    // Phase-internal consistency checks (, )
    // keep their  inside the frontend because firing them means the
    // compiler itself is wrong, not the user's input.
    const PANES: [Phase; 5] = [
        Phase::Uniquify,
        Phase::Infer,
        Phase::Channelize,
        Phase::AsOfRead,
        Phase::LambdaElim,
    ];
    let Frontend {
        expr: join_planned,
        mut panes,
        module,
        sink_bindings: sink_bindings_registry,
        lowering_projection,
        table_session,
    } = run_frontend(ctx, code, Phase::Planning, &PANES, true)?;
    // The frontend ran to , which is past every pane boundary.
    let mut pane = |phase: Phase| {
        panes
            .remove(&phase)
            .unwrap_or_else(|| unreachable!("a run to  passes {phase:?}'s output"))
    };
    let (
        pre_inference_ir,
        post_inference_ir,
        post_channelize_ir,
        post_as_of_read_ir,
        post_lambda_elim_ir,
    ) = (
        pane(Phase::Uniquify),
        pane(Phase::Infer),
        pane(Phase::Channelize),
        pane(Phase::AsOfRead),
        pane(Phase::LambdaElim),
    );
    let table_session =
        table_session.unwrap_or_else(|| unreachable!("a recording run installs the table"));

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
        post_as_of_read_ir,
        post_lambda_elim_ir,
        provenance_table,
        source_ast: module,
        source: code.to_string(),
    };

    // Every compile its own gate — see `provenance_gate_every_compile` for why this
    // is opt-in and what it covers that the sampled gate does not.
    if provenance_gate_every_compile() {
        for pair in program.materialize_panes().gated_pane_pairs() {
            gate_leaks(&pair.leaks, &pair.name);
        }
    }

    Ok(program)
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

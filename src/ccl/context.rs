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
        lineage::{
            Leak, LineageLog, LineageMap, RecorderSession, SourceProjection, collapse,
            collapse_lowering,
        },
        lower::{LoweringContext, LoweringError, lower_stmts},
        mut_elim, planning,
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
    /// lowering boundary, never mutated incrementally. It is the base every later
    /// pane fold bottoms out in, and the release `InferError` diagnostics read it
    /// one-hop (spans of the blame node). The downstream pane projections
    /// (post-inference, post-desugar) are **not** stored here — they are folded
    /// from this projection + [`pass_lineage`](Self::pass_lineage) at
    /// snapshot-serve time by [`materialize_panes`](Self::materialize_panes),
    /// keyed on the ids of each retained snapshot tree.
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
    /// snapshot holds the pre-mono **originals**. Its fan-out to the post-mono
    /// [`post_inference_ir`](Self::post_inference_ir) is exactly the
    /// [`Pass::Mono`] lineage log in [`pass_lineage`](Self::pass_lineage) (one
    /// upstream def → N downstream clones); every ordinary node keeps its id
    /// identical across the pair. Its ids resolve against the
    /// [`lowering_projection`](Self::lowering_projection) (they are the pre-mono originals, keyed by lowering's
    /// directly-lowered attributions).
    pub pre_inference_ir: Expr,
    /// The post-inference IR snapshot — the program inspector's anchor.
    ///
    /// This is `expr` captured **right after `infer`/`typecheck` and before
    /// `inline::inline_non_iterable_lambdas` consumes it**: fully typed, but
    /// still *source-shaped* (lambdas intact, not yet point-free — `inline`,
    /// `lambda_elim`, and `planning` have not run). Its node ids are the input
    /// pane of the post-inference → post-desugar fold and resolve against the
    /// materialized post-inference projection (see
    /// [`materialize_panes`](Self::materialize_panes)).
    ///
    /// Distinct from [`ast`](Self::ast), which holds `join_planned` (the
    /// *post-planning* tree): `lambda_elim`/`planning` re-mint every `NodeId`,
    /// so `ast`'s ids resolve to `None` in the table, and it is
    /// execution-shaped (point-free, fused) — the wrong tree for a source-level
    /// view. The inspector anchors here instead.
    pub post_inference_ir: Expr,
    /// The post-desugar IR snapshot — the inspector's **downstream** pane, one
    /// pipeline stage *below* [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// This is `expr` captured **right after `channelize`** (which now runs
    /// after `infer`/`inline`/`transact`/`letrec`): fully typed and structurally
    /// final for the source view — no Defer/Feed/Define nodes remain, and the
    /// channelization artifacts (`Compose` wrapper chains, `CollectionUnion`
    /// fan-ins) are present. Because monomorphization ran earlier (inside
    /// `infer`), this tree is post-mono like [`post_inference_ir`](Self::post_inference_ir).
    ///
    /// The post-inference ⇄ post-desugar adjacency is folded from the
    /// [`Pass::Inline`] + [`Pass::Desugar`] entries of
    /// [`pass_lineage`](Self::pass_lineage) at snapshot-serve time (see
    /// [`materialize_panes`](Self::materialize_panes)); every id preserved
    /// through inline/transact/letrec/desugar is shared with
    /// [`post_inference_ir`](Self::post_inference_ir) (a self-edge).
    pub post_desugar_ir: Expr,
    /// Per-pass [`LineageLog`]s recorded by the lineage recorder
    /// ([`crate::ccl::lineage`]), in pipeline order:
    ///
    /// * [`Pass::Mono`] — monomorphization's per-clone `Copy` steps and the
    ///   `coalesce_generalized_let` wrapper `Transform` (bridges the
    ///   pre-inference ⇄ post-inference panes),
    /// * [`Pass::Inline`] — inline's beta/alias discard `Transform`s and fan-out
    ///   `Copy` steps,
    /// * [`Pass::Transact`] — the transaction rewrite's `transact.commit`
    ///   Transform (consuming the `with begin():` markers) plus its commit-`LetRec`
    ///   scaffolding births and `subst_env` snapshot copies,
    /// * [`Pass::Letrec`] — the induction phase's `letrec.loop` Transform
    ///   (consuming the loop spine) plus its history/decision births and copies,
    ///   and
    /// * [`Pass::Desugar`] — channelize's cluster/feed-union/lift/drop rewrites
    ///   (Inline + Transact + Letrec + Desugar together bridge post-inference ⇄
    ///   post-desugar, fully recorded — no catch-all).
    ///
    /// This is the **authoritative** lineage surface. [`materialize_panes`](Self::materialize_panes)
    /// folds it at each pane boundary into the per-pane
    /// [`SourceProjection`](crate::ccl::lineage::SourceProjection)s and pane-pair
    /// [`LineageMap`](crate::ccl::lineage::LineageMap)s the inspector consumes.
    // Consumed by the inspector model; unused within the compiler itself.
    #[allow(dead_code)]
    pub(crate) pass_lineage: Vec<(Pass, LineageLog)>,
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

    /// Fold [`pass_lineage`](Self::pass_lineage) at the two pane boundaries into
    /// the per-pane [`SourceProjection`]s and pane-pair [`LineageMap`]s the
    /// inspector consumes. Cold path (snapshot-serve only), never called by
    /// `compile_program`:
    ///
    /// * pre-inference pane = the lowering projection (uniquify preserves ids);
    /// * post-inference pane = fold the Mono log (lowering projection →
    ///   post-inference ids);
    /// * post-desugar pane = fold the concatenated Inline + Desugar logs
    ///   (post-inference → post-desugar ids). Both boundaries are fully recorded.
    // Consumed by the inspector model (a later commit in this stack).
    #[allow(dead_code)]
    pub(crate) fn materialize_panes(&self) -> MaterializedPanes {
        debug_assert_eq!(
            self.pass_lineage.first().map(|(p, _)| *p),
            Some(Pass::Mono),
            "pass_lineage must retain the Mono log first (the pre→post-inference boundary)"
        );
        let pre_ids = collect_tree_ids(&self.pre_inference_ir);
        let post_inf_ids = collect_tree_ids(&self.post_inference_ir);
        let post_des_ids = collect_tree_ids(&self.post_desugar_ir);

        // Boundary 1: the Mono log (first entry) bridges pre → post-inference.
        let (mono_map, post_inference, mono_leaks) = collapse(
            &self.pass_lineage[..1],
            &pre_ids,
            &post_inf_ids,
            &self.lowering_projection,
        );
        // The Mono boundary is fully recorded (mono Copy steps + the coalesce
        // wrapper Transform consuming the whole original def subtree).
        assert_leaks_clean(&mono_leaks, "pre-inference → post-inference (Mono)");

        // Boundary 2: the Inline + Transact + Letrec + Desugar logs bridge
        // post-inference → post-desugar. All four passes record their rewrites, so
        // this boundary is fully recorded too — zero-leak, no catch-all bridge.
        let (desugar_map, post_desugar, desugar_leaks) = collapse(
            &self.pass_lineage[1..],
            &post_inf_ids,
            &post_des_ids,
            &post_inference,
        );
        assert_leaks_clean(
            &desugar_leaks,
            "post-inference → post-desugar (Inline+Transact+Letrec+Desugar)",
        );

        MaterializedPanes {
            pre_inference: self.lowering_projection.clone(),
            post_inference,
            post_desugar,
            mono_map,
            desugar_map,
        }
    }
}

/// The per-pane projections and pane-pair lineage maps materialized from
/// [`CompiledProgram::pass_lineage`] — see
/// [`CompiledProgram::materialize_panes`]. Inspector-facing; the pane
/// projections drive `hover`/`resolve`/`spanIndex`/`build_inspect_tree`, and the
/// maps drive the cross-pane `paneLinks` (shipped dense, self-edges included).
// Consumed by the inspector model; unused within the compiler itself.
#[allow(dead_code)]
pub(crate) struct MaterializedPanes {
    /// pre-inference pane projection (= the lowering projection).
    pub(crate) pre_inference: SourceProjection,
    /// post-inference pane projection.
    pub(crate) post_inference: SourceProjection,
    /// post-desugar pane projection.
    pub(crate) post_desugar: SourceProjection,
    /// pre-inference → post-inference lineage map (Mono fan-out). Dense: shipped
    /// verbatim on the `paneLinks` wire, self-edges included.
    pub(crate) mono_map: LineageMap<NodeId, NodeId>,
    /// post-inference → post-desugar lineage map (Inline + Desugar).
    pub(crate) desugar_map: LineageMap<NodeId, NodeId>,
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

/// The boundary leak gate.
///
/// Both inspector pane boundaries are now **fully recorded** — every pass between
/// two retained panes (Mono at boundary 1; Inline + Transact + Letrec + Desugar
/// at boundary 2) emits its mints/consumes/copies as [`RewriteStep`]s — so the
/// fold must explain every node with **no** leak of any class. There is no
/// catch-all bridge — every node is explained by a recorded step: an
/// `Unexplained` (an uncaptured mint) or a `Dropped`
/// (an unconsumed vanishing node) is a recording bug, not tolerated residue.
/// Debug/test only (the fold is the cold snapshot-serve path).
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
    // still-hole-typed tree; its fan-out to the post-inference snapshot (mono
    // freshens clone ids inside `infer`) is recorded in the `Pass::Mono` lineage
    // log captured below. Its ids resolve against the `lowering_projection` (the
    // pre-mono originals). See `CompiledProgram::pre_inference_ir`.
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
    // channelized rewrite. Monomorphization runs *inside* `infer`; a
    // `RecorderSession` installed across the boundary captures its per-clone
    // `Copy` steps and the `coalesce_generalized_let` wrapper `Transform` into
    // the `Pass::Mono` lineage log (the pre → post-inference pane bridge).
    let mono_session = RecorderSession::new();
    let infer_outcome = infer(&mut expr, ctx.inference_ctx());
    let mono_lineage = mono_session.into_log();
    // On failure, resolve each error's own blame node to a source span *here* —
    // the lowering projection is in scope and holds the lowered attribution (this
    // is the always-on release read: one hop, no fold, before any pane exists).
    // Infer errors occur before the panes are materialized, so the lowering
    // projection is the only lineage layer they can consult. Every error names a
    // node; an id the projection doesn't cover (a node minted after lowering,
    // e.g. by monomorphization) degrades to a span-less diagnostic.
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
    // α-unique name — see `check_mut_write_targets`. (Currently satisfied by
    // construction, since lowering only emits `MutWrite` for registered mutable variables;
    // it becomes load-bearing once lowering emits writes uniformly and drops the
    // registry — see src/ccl/design/mutability.md, "Mutability is the type (no lowering registry)".)
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
    // not run). Its node ids are the input pane of the post-inference →
    // post-desugar fold. `ast` (`join_planned`) is the *wrong* tree for a source
    // view — `lambda_elim`/`planning` re-mint ids and produce execution shape.
    // See `CompiledProgram::post_inference_ir`.
    let post_inference_ir = expr.clone();

    // Runs inline under a `RecorderSession` so its construction steps (beta/alias
    // discard `Transform`s + fan-out `Copy`s) are captured into a `LineageLog`
    // retained on `CompiledProgram::pass_lineage` (`Pass::Inline`).
    let (inlined, inline_lineage) = inline::inline_with_lineage(expr);
    expr = inlined;
    // Id-uniqueness tripwire at the inline boundary. Order-agnostic tree
    // invariant; see `assert_unique_node_ids`.
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
    // writer of a `Mut(_, Txn)` register into a `get_prev_txn`-guarded `LetRec`
    // (histories + commit records over the commit domain), which
    // `planning::plan_loops` destructures into the `Transact{…, Txn}` node
    // op-conversion compiles to the commit engine — unifying the transaction and
    // induction paths on one `LetRec` + recognition representation. Runs *before*
    // `mut_elim` so the induction phase never sees a transaction loop. See
    // src/ccl/design/mutability.md.
    //
    // Register-ness is the `Mut(_, Txn)` type; register identity is the α-unique
    // binder `Name`. Both are read off the *inlined, typed* tree — so a
    // cross-function writer's registers (its `transfer(a, b)` writes already
    // beta-reduced to name `a`/`b`) are seen, and an unrelated local merely spelled
    // like a register is not (its binder is a distinct `Name`). This replaces the
    // lowering-time base-name registry.
    let txn_registers = transact_phase::collect_txn_registers(&expr);
    // A transactional writer reaching a `with begin():` block via a function call
    // is a nested transaction — the callee's inlined `For` would otherwise be
    // silently absorbed into the outer block's read-your-writes env, dropping its
    // commit. Reject it before the phase strips the sites.
    transact_phase::check_no_nested_transactions(&expr, &txn_registers)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    // An induction accumulator written inside a block with no register write is a
    // no-atomicity transaction — rejected here (type-aware), not at lowering.
    transact_phase::check_no_induction_only_transactions(&expr, &txn_registers)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    // A *guarded* in-block induction write (`if q: cnt += 1`) has no commit-gated
    // lifting yet — reject it cleanly here rather than let it reach the phase's
    // internal invariant assert (only a bare top-level in-block induction write is
    // supported, and it is exactly the out-of-block form).
    transact_phase::check_no_guarded_induction_writes(&expr, &txn_registers)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    // Runs the transact phase under a `RecorderSession` so its rewrite steps
    // (site strips → commit `LetRec`, decision/history/tap mints, `subst_env`
    // copies) are captured into a `LineageLog` retained on
    // `CompiledProgram::pass_lineage` (`Pass::Transact`).
    let transact_session = RecorderSession::new();
    expr = transact_phase::run(expr, &txn_registers);
    let transact_lineage = transact_session.into_log();
    assert_unique_node_ids(&expr, "post-transact");
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
    // Runs the mut-elim (induction) phase under a `RecorderSession` so its rewrite
    // steps (loop → causal `LetRec`, decision/history mints, `subst_env` copies)
    // are captured into a `LineageLog` retained on `CompiledProgram::pass_lineage`
    // (`Pass::Letrec`).
    let letrec_session = RecorderSession::new();
    let phase_out = mut_elim::run(expr);
    let letrec_lineage = letrec_session.into_log();
    assert_unique_node_ids(&phase_out, "post-letrec-run");
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
    // Runs channelize under a `RecorderSession` so its construction steps
    // (cluster/feed-union/lift/drop `RewriteStep`s) are captured into a
    // `LineageLog` retained on `CompiledProgram::pass_lineage` (`Pass::Desugar`).
    let (channelize_result, desugar_lineage) =
        channelize::run_with_lineage(phase_out, /* input_typed= */ true);
    let mut desugared = channelize_result.errs()?;
    debug!("Channelized:\n{}", symbolic(&desugared));
    typecheck(&desugared).expect("channelize produced an ill-typed tree");
    // Id-uniqueness tripwire on the post-channelize tree. Freshen-at-duplication
    // (inline's `Subst` clones + channelize's fan-out source clones) makes this
    // hold unconditionally now — before that migration channelize's bare
    // `.clone()`s left genuine duplicate ids here, so no such assert could
    // exist. Order-agnostic tree invariant; see `assert_unique_node_ids`.
    assert_unique_node_ids(&desugared, "post-desugar");

    // Desugar-stage provenance is folded from the `Pass::Inline` + `Pass::Transact`
    // + `Pass::Letrec` + `Pass::Desugar` lineage logs at snapshot-serve time
    // (`CompiledProgram::materialize_panes`) — every pass fully recorded. Nothing
    // is applied here.

    // Retain the post-channelize tree for the inspector's downstream pane. On the
    // post-inference desugar order this snapshot is *downstream* of
    // `post_inference_ir` (post-inline/transact/letrec/channelize); see the doc
    // comment on `post_desugar_ir`.
    let post_desugar_ir = desugared.clone();

    // Fed-out register reads: rewrite a read-only reply that reads a register out of
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
    // surfaces each iterated / join-satisfying extent on its producer's
    // codomain (`refine_codomain` / `set_codomain`) and the strict checker
    // matches the fresh refinement witnesses it mints by structural predicate
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
        // Pipeline order — Mono FIRST (bridges pre→post-inference), then Inline +
        // Transact + Letrec + Desugar (bridge post-inference→post-desugar), in the
        // order the passes run. `materialize_panes` relies on Mono being index 0
        // (it folds `[..1]` for boundary 1 and `[1..]` for boundary 2).
        pass_lineage: vec![
            (Pass::Mono, mono_lineage),
            (Pass::Inline, inline_lineage),
            (Pass::Transact, transact_lineage),
            (Pass::Letrec, letrec_lineage),
            (Pass::Desugar, desugar_lineage),
        ],
        source_ast: module,
        source: code.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::lineage::{Nature, SourceAttribution};

    /// Compile a program for provenance inspection, returning the whole
    /// [`CompiledProgram`].
    fn compile_ok(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        compile_program(&mut ctx, code, consumer).expect("program compiles")
    }

    /// Provenance census of a stage tree against its materialized pane
    /// [`SourceProjection`]: a count of every **main-tree** node (the
    /// `walk_children` node-set) by attribution category — `Source`,
    /// `Derived(<pass>)`, `Synthetic(<pass>)` (via [`attr_category`]),
    /// or `unresolved` (no projection entry). A `BTreeMap` so the pinned rows are
    /// order-stable and diff cleanly.
    ///
    /// This is the guardrail that converts a future pass churning ids without
    /// recording into a *forced visible diff*: it shows up as `Synthetic`
    /// inflation and fails the pinned row. With every pane boundary fully
    /// recorded AND the lowering fold covering every node (each a `Source`
    /// direct image or a `Synthetic(Lower)` plumbing leaf — an unrecorded mint
    /// would be a `Leak::Unexplained` at `collapse_lowering`), `unresolved` is a
    /// hard zero at every pane — asserted structurally in `census_ratchet`, not
    /// ratcheted per row.
    /// The flat provenance category string for a node's attribution — the
    /// census row key and the label the mono/inline/desugar tests match on.
    ///
    /// Test-only: schema 3 ships the native `{via, nature, label}` tag on the
    /// wire, so this categorization no longer lives on `SourceAttribution`. It
    /// folds the two-axis tag back into the flat `Source` / `Derived(<via>)` /
    /// `Synthetic(<via>)` vocabulary these ratchets pin.
    fn attr_category(attr: &SourceAttribution) -> String {
        match attr.rewritten.nature {
            // A direct image (`Nature::Source`) is the census `Source` row — the
            // wire null-compresses it, and the ratchet pins it unmoved.
            Nature::Source => "Source".to_string(),
            Nature::Expansion => format!("Derived({:?})", attr.rewritten.via),
            Nature::Machinery => format!("Synthetic({:?})", attr.rewritten.via),
        }
    }

    fn provenance_census(
        stage_ir: &Expr,
        projection: &SourceProjection,
    ) -> std::collections::BTreeMap<String, usize> {
        fn label(projection: &SourceProjection, id: NodeId) -> String {
            match projection.get(&id) {
                None => "unresolved".to_string(),
                Some(attr) => attr_category(attr),
            }
        }
        fn walk(
            e: &Expr,
            projection: &SourceProjection,
            out: &mut std::collections::BTreeMap<String, usize>,
        ) {
            *out.entry(label(projection, e.node_id())).or_default() += 1;
            e.walk_children(|c| walk(c, projection, out));
        }
        let mut out = std::collections::BTreeMap::new();
        walk(stage_ir, projection, &mut out);
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

    /// Compile-time canary for the always-on lowering session cost (a
    /// *measurement hook*, not a gate — nothing is asserted here). The lowering
    /// session installs in every
    /// build now, recording at leaf grain (ordinary mints open no frame, so
    /// `on_mint` stays a no-op) plus a copy frame per uncurry/compare-chain site,
    /// followed by one O(nodes) fold. This times a representative compile so a
    /// regression in that overhead is observable.
    ///
    /// Run manually (release, the meaningful configuration):
    /// `cargo test --release -- --ignored lowering_session_cost_canary --nocapture`.
    #[test]
    #[ignore = "benchmark hook (not a gate); run manually with --release --nocapture"]
    fn lowering_session_cost_canary() {
        use std::time::Instant;
        // A program exercising leaf recording (arithmetic/loop plumbing) plus a
        // copy frame (the chained comparison's shared operand).
        let code = "x := 0\nfor i in [1, 2, 3]:\n    x += i\n1 < x < 3\nx\n";
        let iters = 2_000u32;
        let start = Instant::now();
        for _ in 0..iters {
            let _ = compile_ok(code);
        }
        let elapsed = start.elapsed();
        eprintln!(
            "lowering-session canary: {iters} compiles in {elapsed:?} \
             ({:?}/compile)",
            elapsed / iters,
        );
    }

    /// RT-4c: the provenance-census ratchet. Pins the exact per-category node
    /// counts for a corpus of representative programs at each retained stage. A
    /// future pass that churns ids without recording shows up as `Synthetic` /
    /// `unresolved` inflation and fails the matching row; a deliberate provenance
    /// improvement (e.g. a desugar lift-preserve that turns a swept node into a
    /// tracked one) *moves* a row, and that diff is itself the commit's
    /// provenance-impact statement.
    ///
    /// The txn/loop rows show the **fully-recorded** state: their post-desugar
    /// trees are `Derived(Transact)`/`Derived(Letrec)`/`Derived(Desugar)` — the
    /// commit `LetRec` scaffolding and the loop→`LetRec` rewrite are recorded as
    /// real lineage steps (every node resolves through a recorded lineage
    /// step). The lowering fold covers
    /// every node, so `unresolved` is a hard zero at
    /// every pane — asserted structurally in the loop below, on top of the
    /// per-row pins. These counts are **structural** (nodes counted by tree
    /// position); this test's job is the forward ratchet and pinning the
    /// attribution shape.
    ///
    /// The `Source` / `Synthetic(Lower)` split follows the structural rule on
    /// `LoweringContext::tag_source`: `Source` marks a lowered *expression root*,
    /// so an image that is not a root — a callee `Var`, an interior comparison of
    /// a chain, a statement-level `Let` — counts as `Synthetic(Lower)` while still
    /// carrying the `"lower.image"` label. A row that moves count between those
    /// two categories with its **total unchanged** is a reclassification, not a
    /// coverage change; a total that moves, or an `unresolved` appearing, is not.
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
                    // `let x = (1 + 2) in x`: the four expression roots (`1`, `2`,
                    // the `+`, the trailing `x`) are `Source`; the `Let` images the
                    // *assignment statement*, and a statement is not a
                    // `Spanned<ChlExpr>`, so under the structural rule it is
                    // `Synthetic(Lower)` carrying the `"lower.image"` label.
                    bt(&[("Source", 4), ("Synthetic(Lower)", 1)]),
                    bt(&[("Source", 4), ("Synthetic(Lower)", 1)]),
                    bt(&[("Source", 4), ("Synthetic(Lower)", 1)]),
                ],
            ),
            (
                "polymorphic",
                "dup = \\x -> (x, x)\n(dup(1), dup(2 == 2))\n",
                [
                    // Full lowering-projection coverage. The three
                    // `Synthetic(Lower)` nodes are images that are not expression
                    // *roots*: the two call-site callee `Var`s (images of the
                    // written function names) and the `def`'s statement-level
                    // `Let`. They keep the `"lower.image"` label.
                    bt(&[("Source", 11), ("Synthetic(Lower)", 3)]),
                    bt(&[
                        ("Derived(Mono)", 10),
                        ("Source", 7),
                        ("Synthetic(Lower)", 2),
                    ]),
                    // Freshen-at-duplication: inline copies every
                    // occurrence of a fanned-out UDF body, so the formerly
                    // keep-first-preserved occurrence (Mono/Source) is now a
                    // freshened `Derived(Inline)` copy too. Structural count is
                    // unchanged (11); the attribution shifts Mono+Source → Inline.
                    bt(&[("Derived(Inline)", 10), ("Source", 1)]),
                ],
            ),
            (
                "udf_fanout",
                "def inc(n):\n    n + 1\na = inc(1)\nb = inc(2)\na + b\n",
                [
                    // Six non-root images: the `def` and two `a`/`b` assignment
                    // `Let`s, and the three callee `Var`s.
                    bt(&[("Source", 10), ("Synthetic(Lower)", 6)]),
                    bt(&[("Derived(Mono)", 5), ("Source", 7), ("Synthetic(Lower)", 4)]),
                    // See `polymorphic`: freshen-at-duplication reattributes the
                    // formerly-preserved inlined occurrences to `Derived(Inline)`.
                    bt(&[
                        ("Derived(Inline)", 6),
                        ("Source", 3),
                        ("Synthetic(Lower)", 2),
                    ]),
                ],
            ),
            (
                "compare_chain",
                // Chained comparison — the keep-first duplicate-NodeId
                // regression program. The outermost AND glue is re-tagged as the
                // whole expression's image (`Source`); each *pair* BinOp images
                // its own `<` but is interior, so it is `Synthetic(Lower)` under
                // the structural rule, as are the `x = 2` assignment `Let` and the
                // statement-sequencing `ExprStmt`. The freshened second use of the
                // shared middle operand still mirrors its origin's attribution.
                "x = 2\n1 < x < 3\nx\n",
                [
                    bt(&[("Source", 7), ("Synthetic(Lower)", 4)]),
                    bt(&[("Source", 7), ("Synthetic(Lower)", 4)]),
                    // Inline substitutes the single-use `x` binding and drops
                    // the effect-free comparison statement, leaving the small
                    // surviving spine.
                    bt(&[("Source", 2), ("Synthetic(Lower)", 1)]),
                ],
            ),
            (
                "mutation_loop",
                "x := 0\nfor i in [1, 2, 3]:\n    x += i\nx\n",
                [
                    // Lowering-manufactured plumbing (the `+=` expansion's
                    // read/arithmetic, the loop-body chain terminal, the loop's
                    // sequencing `ExprStmt`) is attributed `Synthetic(Lower)` by
                    // lowering at its mint site; everything the user wrote images
                    // as `Source`.
                    bt(&[("Source", 7), ("Synthetic(Lower)", 8)]),
                    bt(&[("Source", 7), ("Synthetic(Lower)", 8)]),
                    // post-desugar: the letrec phase records its
                    // loop→`LetRec` rewrite as honest `Derived(Letrec)`
                    // (Expansion); the lowering-manufactured survivors keep
                    // their `Synthetic(Lower)` attributions.
                    bt(&[
                        ("Derived(Letrec)", 38),
                        ("Source", 7),
                        ("Synthetic(Lower)", 3),
                    ]),
                ],
            ),
            (
                "txn_begin",
                "out = defer()\npool: Mut(Int, Txn) := 100\nfor r in [10, 20, 30]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
                [
                    bt(&[("Source", 12), ("Synthetic(Lower)", 19)]),
                    bt(&[("Source", 12), ("Synthetic(Lower)", 19)]),
                    // post-desugar: the transaction rewrite is recorded, so
                    // the formerly bridge-swept commit `LetRec` scaffolding is
                    // honest `Derived(Transact)` (54 — was 59 before the per-key
                    // commit view was retired for allocate-on-commit, dropping
                    // the decision copy + `commit` projection per writer); the
                    // transaction-emptied `For` retired by the mut-elim phase is
                    // `Derived(Letrec)` (2); channelize's feed-union/cluster
                    // steps attribute 7 nodes `Derived(Desugar)`. The 2
                    // `Synthetic(Lower)` survivors are the standalone
                    // transaction's singleton `[unit]` source — manufactured by
                    // lowering and attributed at the mint site.
                    bt(&[
                        ("Derived(Desugar)", 7),
                        ("Derived(Letrec)", 2),
                        ("Derived(Transact)", 54),
                        ("Source", 6),
                        ("Synthetic(Lower)", 2),
                    ]),
                ],
            ),
        ];

        for (name, code, expected) in cases {
            let p = compile_ok(code);
            let panes = p.materialize_panes();
            let actual = [
                provenance_census(&p.pre_inference_ir, &panes.pre_inference),
                provenance_census(&p.post_inference_ir, &panes.post_inference),
                provenance_census(&p.post_desugar_ir, &panes.post_desugar),
            ];
            let stages = ["pre_inference_ir", "post_inference_ir", "post_desugar_ir"];
            for i in 0..3 {
                // Structural invariant, not a per-row ratchet: with the lowering
                // fold covering every node (an unrecorded mint would be a
                // `Leak::Unexplained` at `collapse_lowering`) and every pane
                // boundary fully recorded, NO census at ANY pane may contain an
                // `unresolved` row — a node the pane projection knows nothing
                // about no longer exists.
                assert!(
                    !actual[i].contains_key("unresolved"),
                    "`{name}` at {}: census contains `unresolved` rows ({:?}) — a node \
                     escaped the lowering projection or a pass rewrote without recording",
                    stages[i],
                    actual[i]
                );
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

    /// Monomorphization end-to-end: a generalized definition used at two
    /// distinct types is monomorphized into two specializations. Each
    /// specialization's cloned nodes get fresh `NodeId`s (so they no longer
    /// collide on the original definition's ids), and the folded post-inference
    /// projection attributes them `Derived(Mono)` with spans tracing — through
    /// the per-clone `Copy` steps and the wrapper `Transform` — back to the
    /// original lowered node's source span (within the def's first line).
    #[test]
    fn monomorphization_tags_specializations_with_mono_provenance() {
        // `dup` is bound to a polymorphic lambda and applied at Int and String,
        // forcing two specializations. A non-trivial body (`(x, x)`) keeps the
        // definition from being beta-reduced away before inference (a plain
        // `\x -> x` is inlined during lowering, leaving nothing to
        // monomorphize). The trailing tuple is the program's value.
        let code = "\
dup = \\x -> (x, x)
(dup(1), dup(\"a\"))
";
        let compiled = compile_ok(code);
        let panes = compiled.materialize_panes();

        // The `dup = \x -> (x, x)` statement is the first line; its nodes
        // were attributed `Source` within that span by lowering, and the mono Copy /
        // wrapper Transform steps carry those spans onto the specialization
        // nodes as `Derived(Mono)`.
        let def_line_end = code.find('\n').expect("two-line program");

        // Walk the post-inference pane; collect every node whose attribution is
        // `Derived(Mono)`.
        fn collect_mono<'a>(
            e: &Expr,
            proj: &'a SourceProjection,
            out: &mut Vec<&'a SourceAttribution>,
        ) {
            if let Some(attr) = proj.get(&e.node_id())
                && attr_category(attr) == "Derived(Mono)"
            {
                out.push(attr);
            }
            e.walk_children(|c| collect_mono(c, proj, out));
        }
        let mut mono = Vec::new();
        collect_mono(
            &compiled.post_inference_ir,
            &panes.post_inference,
            &mut mono,
        );
        assert!(
            !mono.is_empty(),
            "monomorphization must attribute specialization nodes Derived(Mono)"
        );
        for attr in &mono {
            assert!(
                !attr.spans.is_empty(),
                "a mono specialization resolves to its original def's source span(s)"
            );
            for span in &attr.spans {
                assert!(
                    span.end <= def_line_end,
                    "mono origin span {span:?} traces back to the `dup` definition \
                     (within the first line, bytes 0..{def_line_end})"
                );
            }
        }
    }

    /// The inline fan-out copies resolve `Derived(Inline)` with real spans.
    ///
    /// A scalar UDF called at two sites *at the same type* fans its body out
    /// during inlining (one specialization from mono, N freshened copies from
    /// inline, each recorded as a `Copy` step). Each freshened body copy mirrors
    /// the original body node's spans — so it resolves to that body's source
    /// span in the post-desugar projection, attributed `Derived(Inline)`.
    #[test]
    fn inline_fanout_copies_resolve_via_inline_copy() {
        // `add1` is a scalar UDF (Int → Int, non-iterable domain → inlined),
        // called at two sites both at `Int`, so mono produces ONE specialization
        // and the two-site fan-out is inline's. The body `x + 1` is duplicated
        // into freshened copies (recorded as `Copy` steps).
        let code = "\
add1 = \\x -> x + 1
a = add1(10)
b = add1(20)
a + b
";
        let compiled = compile_ok(code);
        let panes = compiled.materialize_panes();

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

        let proj = &panes.post_desugar;
        let derived_inline: Vec<NodeId> = new_ids
            .iter()
            .copied()
            .filter(|id| {
                proj.get(id)
                    .is_some_and(|a| attr_category(a) == "Derived(Inline)" && !a.spans.is_empty())
            })
            .collect();
        assert!(
            !derived_inline.is_empty(),
            "at least one inline fan-out copy must resolve Derived(Inline) \
             with non-empty spans; new ids resolved as: {:?}",
            new_ids
                .iter()
                .map(|id| (*id, proj.get(id).map(attr_category)))
                .collect::<Vec<_>>()
        );

        // Mislabel regression guard: no inline fan-out copy is attributed
        // `Synthetic(Desugar)` — the `Copy` steps recorded them.
        for id in &new_ids {
            if let Some(a) = proj.get(id) {
                assert_ne!(
                    attr_category(a),
                    "Synthetic(Desugar)",
                    "inline fan-out copy {id:?} was left to the bridge (Synthetic(Desugar))"
                );
            }
        }
    }

    /// Channelize's rewrites surface as `Desugar`-attributed nodes in the
    /// post-desugar projection: a defer program compiles end-to-end and the
    /// folded projection carries `Pass::Desugar` attributions — the recorded
    /// feed-union/cluster steps (`Derived(Desugar)`, blaming the fed values) and
    /// channelize's `Machinery` steps.
    #[test]
    fn desugar_tags_channelized_plumbing_with_desugar_provenance() {
        // A for-loop feed: channelize routes the feed into a channel union +
        // companion-source fan-out, recording those rewrites as Desugar steps.
        let code = "\
x = defer()
for i in [1, 2, 3]:
  x << i
x
";
        let compiled = compile_ok(code);
        let panes = compiled.materialize_panes();
        let proj = &panes.post_desugar;

        fn count_desugar(e: &Expr, proj: &SourceProjection, n: &mut usize) {
            if proj.get(&e.node_id()).is_some_and(|a| {
                let l = attr_category(a);
                l == "Synthetic(Desugar)" || l == "Derived(Desugar)"
            }) {
                *n += 1;
            }
            e.walk_children(|c| count_desugar(c, proj, n));
        }
        let mut desugar = 0;
        count_desugar(&compiled.post_desugar_ir, proj, &mut desugar);
        assert!(
            desugar >= 1,
            "channelize's rewrites must be attributed via Pass::Desugar"
        );
    }

    // -----------------------------------------------------------------------
    // The construction-step logs retained on
    // `CompiledProgram::pass_lineage`. These assert on log *structure* (labels,
    // op shapes, channel emptiness) — never on absolute NodeId values.
    // -----------------------------------------------------------------------
    mod lineage_adoption {
        use super::*;
        use crate::ccl::lineage::{Leak, LineageLog, Op, SourceProjection, collapse};
        use std::collections::HashSet;

        fn log_for(prog: &CompiledProgram, pass: Pass) -> &LineageLog {
            prog.pass_lineage
                .iter()
                .find(|(p, _)| *p == pass)
                .map(|(_, l)| l)
                .expect("pass has a retained lineage log")
        }

        /// Every main-tree node id of `e` (skips type-predicate interiors, the
        /// node set the steps reason about).
        fn tree_ids(e: &Expr) -> HashSet<NodeId> {
            fn go(e: &Expr, s: &mut HashSet<NodeId>) {
                s.insert(e.node_id());
                e.walk_children(|c| go(c, s));
            }
            let mut s = HashSet::new();
            go(e, &mut s);
            s
        }

        /// A top-level two-feed defer cluster: no loop (so no companion-channel
        /// duplication) and no mutation (so transact/letrec are inert). Exercises
        /// the cluster step and the feed-union fan-in.
        const DEFER_CLUSTER: &str = "x = defer()\nx << [1, 2]\nx << [3, 4]\nx\n";

        #[test]
        fn defer_cluster_logs_cluster_and_feed_union_steps() {
            let prog = compile_ok(DEFER_CLUSTER);
            let log = log_for(&prog, Pass::Desugar);

            let cluster = log
                .iter()
                .find(|s| s.label == "channelize.cluster")
                .expect("a channelize.cluster step");
            match &cluster.op {
                Op::Transform { consumed, produced } => {
                    assert!(
                        !consumed.is_empty(),
                        "cluster consumes the defer scaffolding: {:?}",
                        cluster.op
                    );
                    assert!(
                        !produced.is_empty(),
                        "cluster produces the carrier letrec: {:?}",
                        cluster.op
                    );
                }
                other => panic!("cluster step must be a Transform, got {other:?}"),
            }

            let feed_union = log
                .iter()
                .find(|s| s.label == "channelize.feed_union")
                .expect("a channelize.feed_union step");
            match &feed_union.op {
                Op::Transform { consumed, .. } => assert!(
                    consumed.is_empty(),
                    "feed_union is a pure insertion (empty consumed): {:?}",
                    feed_union.op
                ),
                other => panic!("feed_union step must be a Transform, got {other:?}"),
            }
            assert!(
                !feed_union.blame.is_empty(),
                "feed_union blames the surviving fed-value roots",
            );
        }

        #[test]
        fn inline_fanout_logs_copy_steps() {
            // `inc` is called twice: its body fans out to both sites; each
            // freshened copy (now minted at the duplication site, not by a
            // post-hoc dedup sweep) is captured as a Copy step.
            let prog = compile_ok("def inc(n):\n    n + 1\na = inc(1)\nb = inc(2)\na + b\n");
            let log = log_for(&prog, Pass::Inline);
            let copies = log
                .iter()
                .filter(|s| matches!(s.op, Op::Copy { .. }))
                .count();
            assert!(
                copies >= 1,
                "inline fan-out must record at least one Copy step; log: {log:?}"
            );
        }

        #[test]
        fn defer_free_program_has_near_empty_channelize_log() {
            // No defers ⇒ channelize rewrites nothing; its log carries no cluster,
            // feed-union, lift, or drop steps.
            let prog = compile_ok("a = 1\nb = 2\na + b\n");
            let log = log_for(&prog, Pass::Desugar);
            assert!(
                log.iter().all(|s| !s.label.starts_with("channelize.")),
                "defer-free program should log no channelize rewrites; got {log:?}"
            );
        }

        /// An unconditional loop feeding a defer: `channelize` fans the feed out
        /// over a *cloned iteration source* (the compose-fanout companion). Its
        /// source clones were bare `.clone()`s sharing NodeIds before
        /// freshen-at-duplication — a genuine duplicate-id class in
        /// `post_desugar_ir`. The transact/letrec phases are inert on a pure
        /// defer loop (no mutation), so the pane pair is fully explained.
        const LOOP_FED_DEFER: &str = "x = defer()\nfor i in [1, 2, 3]:\n  x << i\nx\n";

        /// A guarded loop feed lowers to a `Case` with a `true → unit`
        /// fallthrough, taking the case-fanout arm.
        const CASE_FED_DEFER: &str =
            "x = defer()\nfor i in [1, 2, 3]:\n  if i > 1:\n    x << i\nx\n";

        #[test]
        fn case_and_loop_fed_defer_post_desugar_ids_are_unique() {
            // The tree-invariant tripwire (`assert_unique_node_ids`) runs inside
            // `compile_program`; assert the same here, focused on the fan-out
            // classes that produced genuine duplicate ids before this migration
            // (channelize's source clones fed a loop / `Case`).
            for code in [LOOP_FED_DEFER, CASE_FED_DEFER] {
                let prog = compile_ok(code);
                let dups = duplicate_node_ids(&prog.post_desugar_ir);
                assert!(
                    dups.is_empty(),
                    "post_desugar_ir must carry unique ids for `{code}`; dups: {dups:?}"
                );
            }
        }

        #[test]
        fn loop_fed_defer_records_source_copies_and_has_no_leaks() {
            let prog = compile_ok(LOOP_FED_DEFER);
            let log = log_for(&prog, Pass::Desugar);

            // The freshened iteration-source clones are recorded as Copy steps
            // (they were invisible shared-id clones before freshen-at-source).
            let copies = log
                .iter()
                .filter(|s| matches!(s.op, Op::Copy { .. }))
                .count();
            assert!(
                copies >= 1,
                "loop-fed fan-out must record source Copy steps; log: {log:?}"
            );

            let input_ids = tree_ids(&prog.post_inference_ir);
            let output_ids = tree_ids(&prog.post_desugar_ir);
            // The post-inference → post-desugar boundary is the Inline + Desugar
            // logs (`pass_lineage[1..]`); the leading Mono log bridges the
            // pre → post-inference boundary and would reference pre-inference ids
            // absent from this input pane.
            let (_map, _proj, leaks) = collapse(
                &prog.pass_lineage[1..],
                &input_ids,
                &output_ids,
                &SourceProjection::new(),
            );
            // A pure defer loop keeps transact/letrec inert (the documented
            // tolerance would apply on a *mutation* loop), so the channelize
            // steps — now including the source Copy steps — fully explain the
            // pane pair with no residual leak of any kind.
            assert!(
                leaks.is_empty(),
                "loop-fed defer pane pair must be fully explained; leaks: {leaks:?}"
            );
        }

        #[test]
        fn collapse_over_real_panes_has_no_channelize_attributable_leaks() {
            let prog = compile_ok(DEFER_CLUSTER);
            let input_ids = tree_ids(&prog.post_inference_ir);
            let output_ids = tree_ids(&prog.post_desugar_ir);

            // Inline + Desugar logs bridge this pane pair; the Mono log
            // (`pass_lineage[0]`) belongs to the pre → post-inference boundary.
            let (_map, _proj, leaks) = collapse(
                &prog.pass_lineage[1..],
                &input_ids,
                &output_ids,
                &SourceProjection::new(),
            );

            // A recording *bug* would surface as one of these structural leaks
            // (an ordering/attribution error inside a step). Their absence is the
            // real invariant: the channelize steps consume/produce live ids only.
            let bug_leaks: Vec<&Leak> = leaks
                .iter()
                .filter(|l| {
                    matches!(
                        l,
                        Leak::ConsumedUnknown { .. }
                            | Leak::CopyOfUnknown { .. }
                            | Leak::ProducedLive { .. }
                            | Leak::EmptyConsumed { .. }
                    )
                })
                .collect();
            assert!(
                bug_leaks.is_empty(),
                "no channelize-attributable recording bug leaks; got {bug_leaks:?}"
            );

            // Unexplained/Dropped leaks that remain are NOT channelize's: the
            // transact/letrec phases run between the two panes and mint/consume
            // nodes without recording steps until the next increment. This
            // program keeps them inert (no mutation, no loop), so in practice the
            // list is empty — assert that to catch a channelize regression, while
            // documenting why a residual would be tolerable.
            let residual: Vec<&Leak> = leaks
                .iter()
                .filter(|l| matches!(l, Leak::Unexplained { .. } | Leak::Dropped { .. }))
                .collect();
            assert!(
                residual.is_empty(),
                "this program keeps transact/letrec inert, so channelize's steps \
                 should fully explain the pane pair; residual leaks: {residual:?}"
            );
        }

        /// A mutation loop (`x := 0; for i: x += i; x`).
        const MUTATION_LOOP: &str = "x := 0\nfor i in [1, 2, 3]:\n    x += i\nx\n";
        /// A transaction program: a `with begin():` writer loop + a fed-out read.
        const TXN: &str = "out = defer()\npool: Mut(Int, Txn) := 100\n\
             for r in [10, 20, 30]:\n    with begin():\n        pool := pool - r\n\
             with begin():\n    out << pool\nout";

        #[test]
        fn letrec_loop_records_a_consuming_transform_step() {
            // The induction phase records its loop → guarded `LetRec` rewrite as a
            // `letrec.loop` Transform consuming the loop statement's spine.
            let prog = compile_ok(MUTATION_LOOP);
            let log = log_for(&prog, Pass::Letrec);
            let loop_step = log
                .iter()
                .find(|s| s.label == "letrec.loop")
                .expect("a letrec.loop step");
            match &loop_step.op {
                Op::Transform { consumed, produced } => {
                    assert!(
                        !consumed.is_empty(),
                        "the loop rewrite consumes the loop spine: {:?}",
                        loop_step.op
                    );
                    assert!(
                        !produced.is_empty(),
                        "the loop rewrite mints the carrier LetRec scaffolding: {:?}",
                        loop_step.op
                    );
                }
                other => panic!("letrec.loop must be a Transform, got {other:?}"),
            }
        }

        #[test]
        fn transact_records_a_commit_transform_step() {
            // The transaction phase records its whole rewrite as a
            // `transact.commit` Transform consuming the `with begin():` markers.
            let prog = compile_ok(TXN);
            let log = log_for(&prog, Pass::Transact);
            let commit = log
                .iter()
                .find(|s| s.label == "transact.commit")
                .expect("a transact.commit step");
            match &commit.op {
                Op::Transform { consumed, produced } => {
                    assert!(
                        !consumed.is_empty(),
                        "the transaction rewrite consumes the `with begin():` markers: {:?}",
                        commit.op
                    );
                    assert!(
                        !produced.is_empty(),
                        "the transaction rewrite mints the commit LetRec scaffolding: {:?}",
                        commit.op
                    );
                }
                other => panic!("transact.commit must be a Transform, got {other:?}"),
            }
        }

        /// The mutation-loop and transaction pane pairs fold with **no** leak of
        /// any class — the whole post-inference → post-desugar boundary (Inline +
        /// Transact + Letrec + Desugar) is fully recorded.
        #[test]
        fn recorded_phases_leave_the_pane_pair_leak_free() {
            for code in [MUTATION_LOOP, TXN] {
                let prog = compile_ok(code);
                let input_ids = tree_ids(&prog.post_inference_ir);
                let output_ids = tree_ids(&prog.post_desugar_ir);
                let (_map, _proj, leaks) = collapse(
                    &prog.pass_lineage[1..],
                    &input_ids,
                    &output_ids,
                    &SourceProjection::new(),
                );
                assert!(
                    leaks.is_empty(),
                    "fully-recorded pane pair must be leak-free for `{code}`; leaks: {leaks:?}"
                );
            }
        }
    }
}

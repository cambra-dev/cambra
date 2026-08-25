// ---------------------------------------------------------------------------
// Context object for state shared across all phases of compilation like
// builtins
// ---------------------------------------------------------------------------

use std::collections::{HashMap, HashSet};
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
    /// This is `expr` captured at the [`Channelized`](CompileStage::Channelized)
    /// boundary — after `channelize` and the as-of-read rewrite that completes
    /// it: fully typed and structurally final for the source view, with no
    /// Defer/Feed/Define nodes left and the channelization artifacts (`Compose`
    /// wrapper chains, `Copair` fan-ins) present. Because monomorphization ran
    /// earlier (inside `infer`), this tree is post-mono like
    /// [`post_inference_ir`](Self::post_inference_ir).
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
pub(crate) fn collect_tree_ids(expr: &Expr) -> HashSet<NodeId> {
    fn go(e: &Expr, acc: &mut HashSet<NodeId>) {
        acc.insert(e.node_id());
        e.walk_children(|c| go(c, acc));
    }
    let mut acc = HashSet::new();
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

/// `check_pre_desugar` as a wall between two passes. It is the relaxed
/// pre-desugar check, which permits the transient `Feed` / `Infer`-channel-domain
/// types only channelization erases.
///
/// A failure is a compiler bug, with one exception: residual `Type::Infer`
/// variables, which inference deliberately tolerates for a generalized
/// definition the program never exercises at a concrete type (see
/// `Type::Infer`'s invariant). That residue is an *ambiguous program* — a user
/// error — so it is rendered as a diagnostic; anything else panics, naming
/// `produced_by`.
fn pre_desugar_wall(expr: &Expr, produced_by: &str) -> Result<(), Vec<CompileError>> {
    check_pre_desugar(expr).map_err(|errs| {
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
/// still-`Mut`-bearing tree — after [`pre_desugar_wall`], before inlining.
///
/// Both need the pre-inline `Apply`/parameter structure and the coalesced `.ty`
/// slots and `user_annotation`s. Unlike the surrounding [`pre_desugar_wall`]
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
///   Rejected here, type-aware, rather than at lowering.
/// - `check_no_guarded_induction_write_in_block` — a *guarded* induction write
///   inside a committing block (`balance := …; if p: cnt += 1`) is not liftable
///   and would be silently dropped from the decision record. A debug-only assert
///   would miss it in release.
/// - `check_await_final_linearity` — `await_final` consumes its mutable variable:
///   no mention may follow its await. A statement-order rule lowering cannot see,
///   since it builds its chain right-to-left, and a callee's mention only becomes
///   a read, a write, or a `Begin` once inlined. (The companion rule, that a commit
///   store may not depend on the completion of that same store, is decided per
///   store and so lives inside the phase.)
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

/// A pipeline stage a program can be compiled to for diffing; the differ
/// ([`crate::ccl::diff`]) accepts an [`Expr`] at any of them. See
/// `src/ccl/design/diffing.md`, "Which stage to diff".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileStage {
    /// Lowered CCL: `Raw` names, pre-α-uniquification, pre-inference. Closest
    /// to source; most node types are still `Type::Hole`.
    Lowered,
    /// Type-inferred CCL: α-uniquified, every node annotated with its resolved
    /// type — reflects type-level differences a `Lowered` diff cannot see.
    /// Still carries the transient surface nodes (`Defer`/`Feed`/`For`/
    /// `Begin`) and their `History` types, which the mutability and
    /// channelization phases below this stage erase.
    Inferred,
    /// Type-inferred, then **UDF-inlined**: every call to a user-defined
    /// function is replaced by its beta-reduced body, so function boundaries
    /// stop being part of the program's identity.
    ///
    /// This is the pipeline's own [`inline`] pass used as a normalization, and
    /// it is a deliberate trade, not a strict improvement. Extracting a
    /// subexpression into a `def` (or inlining one back) becomes invisible —
    /// the two versions compile to the same tree. In exchange, an edit *inside*
    /// a function called `n` times is reported `n` times, because the body it
    /// changed now appears `n` times. Pick this stage when refactoring across
    /// function boundaries is the noise you want gone; pick [`Inferred`] when
    /// locality inside shared helpers matters more.
    ///
    /// That last recommendation is weaker than it sounds. Monomorphization runs
    /// inside `infer`, so [`Inferred`] has *already* cloned a definition once
    /// per distinct instantiation identity: two calls that key apart — literal
    /// arguments do, since a `SpecKey` sees their singletons — are two bodies
    /// before inlining is even reached. `Inferred` preserves locality across
    /// call sites that share a specialization, not across call sites generally.
    /// Measured both ways in `src/ccl/design/diffing.md`, "How much to
    /// normalize".
    ///
    /// [`Inferred`]: CompileStage::Inferred
    Inlined,
    /// Mutability eliminated: `with begin():` blocks and mutation loops have
    /// become causal `LetRec` recurrences over their sequencing domain, and
    /// feeds have been routed into channels. `For`/`MutWrite`/`Begin`/`Defer`
    /// are gone.
    Channelized,
    /// Point-free: lambdas replaced by combinators, so binders no longer appear
    /// in the term at all.
    LambdaElim,
    /// Recurrences lowered onto the `Transact` carrier and joins planned — the
    /// shape operator conversion consumes. The last stage before the tile
    /// graph, and the one where compute sharing is decided.
    Planned,
}

/// What a frontend run hands back besides the tree at its stop stage.
struct Frontend {
    /// The tree at the requested [`CompileStage`].
    expr: Expr,
    /// The surface AST lowering consumed, retained for source-level queries.
    module: chl_parser::ast::Module,
    /// Sink bindings discovered during lowering. Drained before the sources,
    /// which is the order [`LoweringContext`] requires.
    sink_bindings: HashMap<String, Arc<dyn DataSink>>,
}

/// The provenance a frontend run records when asked for it: the lowering
/// projection every release `InferError` resolves its span against, and the IR
/// snapshots the inspector's panes read.
///
/// Recording is the whole difference between the two entry points besides where
/// they stop. [`compile_program`] asks for it; [`compile_to`] hands a tree to
/// the differ and renders no diagnostics, so it passes `None` and the frontend
/// skips the recorder session, the projection fold and the three clones.
#[derive(Default)]
struct FrontendRecord {
    /// See [`CompiledProgram::lowering_projection`].
    lowering_projection: SourceProjection,
    /// See [`CompiledProgram::pre_inference_ir`]; taken at the [`Lowered`]
    /// boundary, after α-uniquification.
    ///
    /// [`Lowered`]: CompileStage::Lowered
    pre_inference_ir: Option<Expr>,
    /// See [`CompiledProgram::post_inference_ir`]; taken at the [`Inferred`]
    /// boundary.
    ///
    /// [`Inferred`]: CompileStage::Inferred
    post_inference_ir: Option<Expr>,
    /// See [`CompiledProgram::post_desugar_ir`]; taken at the [`Channelized`]
    /// boundary.
    ///
    /// [`Channelized`]: CompileStage::Channelized
    post_desugar_ir: Option<Expr>,
}

/// The compiler frontend: source in, a CCL tree at `stop` out.
///
/// **This is the only place the pass sequence and its checks are written.**
/// [`compile_program`] runs it to `Planned` and continues into operator
/// conversion; [`compile_to`] runs it to whichever stage a diff is being taken
/// at and stops. A check added here therefore lands on both, which is what keeps
/// a staged snapshot from being a tree the real pipeline would have rejected.
///
/// `record` selects whether the run also builds the inspector's
/// [`FrontendRecord`]; nothing else about the two callers differs.
fn run_frontend(
    ctx: &mut GlobalContext,
    code: &str,
    stop: CompileStage,
    mut record: Option<&mut FrontendRecord>,
) -> Result<Frontend, Vec<CompileError>> {
    // The parse and lower stages accumulate errors before bailing: when the
    // parser recovers from a syntax error it still produces a partial AST, which
    // lowering can run on and report its own errors against, so the user sees
    // everything at once. Inference and below assume a well-typed tree with no
    // `Error` placeholders, so they are skipped when anything earlier failed.
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

    // The lowering session covers the whole of lowering. Its leaf entries
    // (`tag_source` / `tag_machinery`) and copy-frame flushes (uncurry,
    // compare-chain) record a `LoweringLog`, folded once at the handoff below
    // into the lowering projection. It must fully drain before the first pass
    // (Mono) session opens. Without a session installed the recorder is inert,
    // which is what a run that wants no projection gets.
    let session = record.is_some().then(RecorderSession::lowering);
    let lower_result = lower_stmts(&module.body, ctx.lowering_ctx());
    errors.extend(lower_result.errors.into_iter().map(CompileError::Lower));
    let Some(expr) = lower_result.value else {
        return Err(errors);
    };
    // Anything wrong earlier means `expr` may contain `TypedExprNode::Error`
    // placeholders; inference and below would panic on them via
    // [`crate::unexpected_error_node!`], and they are meaningless to diff.
    if !errors.is_empty() {
        return Err(errors);
    }

    // Drain sink bindings before taking sources.
    let sink_bindings = ctx.lowering_ctx().take_sink_bindings();

    if let (Some(rec), Some(session)) = (record.as_deref_mut(), session) {
        // Fold the lowering log once, at the lowering→pipeline handoff and
        // before uniquify/inference (so the release `InferError` read timing is
        // unchanged), into the **lowering projection**: every lowered node's
        // `SourceAttribution`, keyed by NodeId. It is the base every later pane
        // fold bottoms out in. `uniquify` preserves every id in place, so the
        // projection's keys survive into the pre-inference pane.
        //
        // Id uniqueness is the precondition for keying anything by `NodeId`, so
        // gate it before the fold that does exactly that: a duplicate here would
        // silently collapse two nodes' attributions into one projection entry.
        // Lowering's own copy sites (uncurry's template discharge, the
        // chained-comparison operand freshens) are what make this a live risk.
        assert_unique_node_ids(&expr, "post-lowering");
        let lowering_log = session.into_lowering_log();
        let output_ids = collect_tree_ids(&expr);
        let (projection, leaks) = collapse_lowering(&lowering_log, &output_ids);
        // The fold's leak taxonomy enforces mint coverage: an unrecorded
        // lowering mint surfaces as `Leak::Unexplained`. The checks are
        // debug/test gated; the fold itself is always-on, its product being
        // release-critical.
        assert_leaks_clean(&leaks, "lowering");
        rec.lowering_projection = projection;
    }

    let expr = run_passes(ctx, expr, stop, record)?;
    Ok(Frontend {
        expr,
        module,
        sink_bindings,
    })
}

/// The pass sequence, from the lowered tree to `stop`.
///
/// Split out of [`run_frontend`] only so each stage boundary can `return` the
/// tree; the two are one pipeline.
fn run_passes(
    ctx: &mut GlobalContext,
    mut expr: Expr,
    stop: CompileStage,
    mut record: Option<&mut FrontendRecord>,
) -> Result<Expr, Vec<CompileError>> {
    debug!("Lowered (pre-desugar):\n{}", symbolic(&expr));
    if stop == CompileStage::Lowered {
        return Ok(expr);
    }

    // α-uniquify all binders (Barendregt convention): every binding site gets a
    // globally fresh `Name` uid, so shadowing ceases to exist before any pass
    // that compares names. Must run before channelization, whose rewrites splice
    // and rename terms under the assumption that distinct binders are distinct
    // names.
    expr = uniquify::run(expr);
    if let Some(rec) = record.as_deref_mut() {
        rec.pre_inference_ir = Some(expr.clone());
    }

    // Register every source (pre-registered + discovered during lowering) with
    // inference and operator conversion now that the full source set is known.
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
    //
    // On failure, resolve each error's own blame node to a source span here
    // (the release read: one hop, no fold). Every error names a node; an id the
    // projection doesn't cover — a node minted after lowering, e.g. by
    // monomorphization — degrades to a span-less diagnostic, as does every error
    // on a run that recorded no projection.
    if let Err(errors) = infer(&mut expr, ctx.inference_ctx()) {
        let projection = record.as_deref().map(|rec| &rec.lowering_projection);
        return Err(errors
            .into_iter()
            .map(|located| CompileError::Infer {
                error: located.error,
                span: projection
                    .and_then(|p| p.get(&located.node_id))
                    .and_then(|attr| attr.spans.first().copied()),
            })
            .collect());
    }
    debug!("Inferred:\n{}", symbolic(&expr));
    debug!("Inferred (typed):\n{}", symbolic_typed(&expr));

    // Consistency wall between `infer` and `channelize`, then the two mutability
    // rules on the fully-typed, still-`Mut`-bearing tree.
    pre_desugar_wall(&expr, "Inference")?;
    check_mut_rules(&expr)?;
    if let Some(rec) = record.as_deref_mut() {
        rec.post_inference_ir = Some(expr.clone());
    }
    if stop == CompileStage::Inferred {
        return Ok(expr);
    }

    // Inline UDFs *before* channelization: a defer-mediating UDF (`λ out → out
    // << e`) or a cross-function writer is beta-reduced to its call site before
    // channelize routes feeds and before the unified letrec phase folds writers,
    // both of which need their targets lexically present. Inlining runs on the
    // still-defer-bearing tree (Defer/Feed nodes and `Feed` types present) via
    // the defer-aware `Subst` engine, which renames a fed-to handle on
    // beta-reduction, and preserves defer-returning generators — so the
    // post-inline wall is the relaxed `check_pre_desugar`, not strict
    // `typecheck`.
    let mut expr = inline::inline_capability_lambdas(expr);
    debug!("UDFs inlined CCL:\n{}", symbolic(&expr));
    pre_desugar_wall(&expr, "UDF inlining")?;
    if stop == CompileStage::Inlined {
        return Ok(expr);
    }

    // Transactional slice of the unified phase: rewrite every `with begin():`
    // writer of a `Mut(_, Txn)` mutable variable into a `get_prev_txn`-guarded
    // `LetRec` (histories + commit records over the commit domain), which
    // `planning::plan_loops` destructures into the `Transact{…, Txn}` node
    // op-conversion compiles to the commit engine — unifying the transaction and
    // induction paths on one `LetRec` + recognition representation. Runs *before*
    // `mut_elim` so the induction phase never sees a transaction loop. See
    // src/ccl/design/mutability.md.
    //
    // Being a transactional variable is the `Mut(_, Txn)` type; identity is the
    // α-unique binder `Name`. Both are read off the *inlined, typed* tree — so a
    // cross-function writer's mutable variables (its `transfer(a, b)` writes
    // already beta-reduced to name `a`/`b`) are seen, and an unrelated local
    // merely spelled like a mutable variable is not, its binder being a distinct
    // `Name`.
    let txn_mut_vars = transact_phase::collect_txn_mut_vars(&expr);
    check_transact_rejections(&expr, &txn_mut_vars)?;
    expr = transact_phase::run(expr, &txn_mut_vars)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    debug!("Transact phase CCL:\n{}", symbolic(&expr));
    check_pre_desugar(&expr).expect("transact phase produced an inconsistent tree");

    // The unified letrec phase: direct-mirror mutation loops (`For` /
    // `MutWrite`) become causal `LetRec` groups — mutable histories over the
    // induction domain, per src/ccl/design/mutability.md. Runs after inlining, so
    // cross-function writers land at their call sites, and *before* channelize,
    // so a per-iteration feed inside a loop is hoisted to an ordinary feed of the
    // loop's history for channelization to route. The tree still carries
    // Defer/Feed here, so the wall is the relaxed pre-desugar check.
    let expr = mut_elim::run(expr);
    debug!("Letrec phase CCL:\n{}", symbolic(&expr));
    check_pre_desugar(&expr).expect("letrec phase produced an inconsistent tree");

    // Feed channelization — the feed-routing step of the unified phase, run on
    // the phase-emitted `LetRec` tree (recognition happens *after* `lambda_elim`,
    // below). Every `let d = Defer in body` is rewritten to `let d = <channel> in
    // body`, where `<channel>` is the `++`-union of the defer's `<<` / `<<=`
    // contributions; a channel assembled from a group's taps binds inside the
    // letrec body, below the binders it captures. After this, no
    // Defer/Feed/Define nodes — and no `Feed`/`ChanDom` types — remain:
    // channelization is type-preserving by construction and closes channel
    // domains by substitution; the strict `typecheck` is the release-visible
    // enforcement.
    let mut expr = channelize::run(expr).errs()?;
    debug!("Channelized:\n{}", symbolic(&expr));
    typecheck(&expr).expect("channelize produced an ill-typed tree");

    // Fed-out mutable variable reads: rewrite a read-only reply that reads a
    // mutable variable out of its block into an outer-indexed as-of join (an
    // as-of read at the reading transaction's arbitrary commit position),
    // *before* lambda elimination — so a computed reply (`resp << balance + 1`)
    // stays a lambda the elim pass point-frees, rather than a point-free `const`
    // a planning-time recognizer would have to reject. Uniform across the reading
    // loop's domain. See `transact_phase::rewrite_as_of_reads`.
    transact_phase::rewrite_as_of_reads(&mut expr)
        .map_err(|msg| vec![CompileError::Unsupported(msg)])?;
    typecheck(&expr).expect("as-of-read rewrite produced an ill-typed tree");
    if let Some(rec) = record {
        rec.post_desugar_ir = Some(expr.clone());
    }
    if stop == CompileStage::Channelized {
        return Ok(expr);
    }

    let expr = lambda_elim::run(expr).errs()?;
    debug!("λ-eliminated CCL:\n{}", symbolic(&expr));
    debug!("λ-eliminated typed CCL:\n{}", symbolic_typed(&expr));
    // `typecheck` enforces hole-freeness as its first phase, so this call alone
    // covers both checks.
    typecheck(&expr).expect("type error after lambda elimination");
    if stop == CompileStage::LambdaElim {
        return Ok(expr);
    }

    // Recognition: lower each causal group — now in its point-free normal form —
    // onto the domain-parameterized `Transact` carrier (a `get_prev_txn`
    // transaction group → `Transact{Txn}`; a `get_prev_seq` induction group →
    // `Transact{iteration extent}`) so planning stages the writer sources and
    // operator conversion picks the engine on the domain. Running post-elim is
    // what keeps ONE letrec representation through channelize and lambda_elim;
    // the point-free guard matcher re-checks causality here. See the `mut_elim`
    // recognition docs.
    let expr = planning::plan_loops(expr);
    debug!("Letrec recognized CCL:\n{}", symbolic(&expr));
    typecheck(&expr).expect("letrec recognition produced an ill-typed tree");

    let expr = planning::run(expr);
    debug!("Join-planned CCL:\n{} : {}", symbolic(&expr), expr.ty);
    debug!("Join-planned CCL:\n{}", symbolic_typed(&expr));
    // Planning is the one pass that introduces `iterate` / `restrict` / `Compose`
    // staging, so re-checking its output catches a malformed tile graph an
    // adjacency that doesn't chain would otherwise hide. Planning surfaces each
    // iterated / join-satisfying extent on its producer (`refine_extent` /
    // `set_extent`) and the strict checker matches the fresh refinements it mints
    // by structural predicate equality, so the staging shapes validate without
    // re-blinding the check or peeling cast refinements.
    typecheck(&expr).expect("type error after join planning");
    // Invariant (debug): planning's `iterate`/`restrict` markers live in the term
    // tree, never inside a type's refinement predicates — the substitution
    // boundary strips the neutral `iterate` marker
    // (`ccl_utils::strip_iterate_markers`), and a `restrict` reaching a predicate
    // (a filtered source used in a refined domain) is unsupported and must
    // surface loudly, not miscompile.
    #[cfg(debug_assertions)]
    crate::ccl::ccl_utils::debug_assert_no_iteration_markers(&expr);

    debug_assert_eq!(
        stop,
        CompileStage::Planned,
        "every CompileStage must be handled before this point",
    );
    Ok(expr)
}

/// Compile `code` to the given [`CompileStage`], ready to pass to
/// [`crate::ccl::diff::diff`]. Sources — the pre-registered `stdin()` and any
/// discovered during lowering — are registered for inference, so the result is
/// reachable end-to-end from source.
///
/// Pair two results for a program diff (each tree must outlive the borrow), or
/// use [`crate::ccl::diff::diff_programs`] for the common case:
/// ```ignore
/// let (a, b) = (compile_to(s1, CompileStage::Inferred)?, compile_to(s2, CompileStage::Inferred)?);
/// let d = crate::ccl::diff::diff(&a, &b);
/// ```
///
/// This runs [`run_frontend`] — the same passes and the same checks
/// [`compile_program`] runs, stopping at `stage` rather than continuing into the
/// operator graph. A program `compile_program` refuses therefore yields no stage
/// snapshot here.
///
/// Choosing a stage is choosing how much of the compiler's own rewriting to diff
/// through, and it is a trade in both directions — a later stage normalizes more
/// away but spreads a single edit over more of the tree. See [`CompileStage`] and
/// `src/ccl/design/diffing.md`, "How much to normalize".
///
/// The transaction, mutability and channelization phases are not separately
/// selectable: they are one rewrite of the user's loops and feeds into `LetRec`
/// recurrences, and stopping between them exposes a half-rewritten tree no
/// consumer wants. [`Channelized`] is the point where that rewrite is complete.
///
/// [`Channelized`]: CompileStage::Channelized
pub fn compile_to(code: &str, stage: CompileStage) -> Result<Expr, Vec<CompileError>> {
    let mut ctx = GlobalContext::new();
    Ok(run_frontend(&mut ctx, code, stage, None)?.expr)
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
    // The frontend is [`run_frontend`], shared with [`compile_to`]: parse
    // through join planning, plus every check between. Only the recording and
    // the continuation past `Planned` are this function's own.
    //
    // Stage-internal consistency checks (`typecheck`, `check_pre_desugar`) keep
    // their `.expect` inside the frontend because firing them means the compiler
    // itself is wrong, not the user's input.
    let mut record = FrontendRecord::default();
    let frontend = run_frontend(ctx, code, CompileStage::Planned, Some(&mut record))?;
    let Frontend {
        expr: join_planned,
        module,
        sink_bindings: sink_bindings_registry,
    } = frontend;
    let FrontendRecord {
        lowering_projection,
        pre_inference_ir,
        post_inference_ir,
        post_desugar_ir,
    } = record;
    // The frontend fills all three whenever it is asked to record, and it ran to
    // `Planned`, which is past every snapshot point.
    let (Some(pre_inference_ir), Some(post_inference_ir), Some(post_desugar_ir)) =
        (pre_inference_ir, post_inference_ir, post_desugar_ir)
    else {
        unreachable!("a recorded run to `Planned` passes every snapshot boundary")
    };

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
    use indoc::indoc;
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
    fn both_entry_points_compile_to_one_tree() {
        // `compile_to` and `compile_program` are one frontend, so the tree at
        // `Planned` is the tree operator conversion consumes — node for node,
        // modulo the fresh binder uids two independent compilations mint. If a
        // pass or a check is ever added to only one of them, this diverges.
        for code in [
            indoc! {"
                a = 1
                b = 2
                a + b
            "},
            indoc! {"
                xs = [1, 2, 3]
                sum([x * 2 for x in xs if x > 1])
            "},
            indoc! {"
                acc := 0
                for i in [1, 2, 3]:
                    acc := acc + i
                acc
            "},
        ] {
            let mut ctx = GlobalContext::default();
            let consumer: Box<dyn Consumer> = Box::new(|| {});
            let program = compile_program(&mut ctx, code, consumer).expect(code);
            let staged = compile_to(code, CompileStage::Planned).expect(code);
            assert!(
                crate::ccl::diff::diff(&program.ast, &staged).is_identical(),
                "the two entry points disagree on:\n{code}\n{}",
                crate::ccl::diff::diff(&program.ast, &staged),
            );
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

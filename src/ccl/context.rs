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
        infer::{InferError, TypeInferenceContext, check_fully_typed, infer, typecheck},
        inline, join_plan, lambda_elim,
        lower::{LoweringContext, LoweringError, lower_stmts},
        symbolic::{symbolic, symbolic_typed},
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
/// Use [`eprint_errors`] for source-context rendering: parse errors get
/// ariadne reports with red/yellow underlines; the other variants render as
/// plain `error: …` lines. Source-aware spans for lowering/inference errors
/// are future work; this enum is shaped so those variants can be migrated to
/// a unified [`Diagnostic`]-style representation later without changing the
/// list-of-errors return contract.
///
/// [`Diagnostic`]: https://docs.rs/ariadne/latest/ariadne/
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
    DesugarDefers(desugar_defers::DeferError),
    /// Type inference rejected one expression.
    Infer(InferError),
    /// Lambda elimination failed.
    LambdaElim(lambda_elim::LambdaElimError),
    /// Operator-graph conversion failed.
    Conversion(ConversionError),
}

impl CompileError {
    /// Render this single error as a plain-ASCII string with source-code context.
    ///
    /// - [`CompileError::Parse`] is rendered via ariadne with colour
    ///   disabled (gutter, source line, underlines, labels — all rendered
    ///   in Unicode box-drawing). Suitable for inclusion in panic
    ///   messages, log files, snapshots, or piping through grep.
    /// - The other variants render as plain `error: …` lines because
    ///   they don't yet carry source spans.
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
            CompileError::Infer(e) => {
                buf.extend_from_slice(format!("error: type inference: {e:?}\n").as_bytes());
            }
            CompileError::LambdaElim(e) => {
                buf.extend_from_slice(format!("error: lambda elimination: {e:?}\n").as_bytes());
            }
            CompileError::Conversion(e) => {
                buf.extend_from_slice(
                    format!("error: operator-graph conversion: {e:?}\n").as_bytes(),
                );
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
            other => eprint!("{}", other.render(src_name, src)),
        }
    }
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
        self.into_iter().map(CompileError::Infer).collect()
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

    debug!("Lowered (pre-desugar):\n{}", symbolic(&expr));

    // Desugar Defer/Feed/Define before inference: every `let d = Defer in body`
    // gets rewritten so the body publishes its contribution to d via a
    // `Record({result, to_d})` at the body's terminal, with the defer-bind
    // site consuming the `to_d` projection.  After this, no Defer/Feed/Define
    // nodes remain.
    expr = desugar_defers::run(expr).errs()?;

    // Register every source (pre-registered + discovered during lowering) with
    // inference and operator-conversion now that the full source set is known.
    for (_name, source) in ctx.lowering_ctx().take_sources() {
        let name = source.borrow().get_id().to_string();
        let output_type = source.borrow().output_type();
        ctx.inference_ctx().register_source_type(
            &name,
            Type::Fun(
                Box::new(Type::DataSource(name.clone())),
                Box::new(output_type),
            ),
        );
        ctx.conversion_ctx().register_source(name, source);
    }

    debug!("Lowered:\n{}", symbolic(&expr));

    let infer_ctx = ctx.inference_ctx();
    infer(&mut expr, infer_ctx).errs()?;
    debug!("Inferred:\n{}", symbolic(&expr));
    debug!("Inferred (typed):\n{}", symbolic_typed(&expr));
    typecheck(&expr).expect("Inference created invalid expr");

    // Inline UDFs: substitute both scalar and list-producing UDF Let bindings
    // and beta-reduce at each call site before lambda elimination.  This
    // strips the outer user-parameter lambda from list-producing UDFs so the
    // remaining Lambda layer matches the list-comprehension shape that
    // lambda-elim handles, and avoids a runtime panic when operator conversion
    // would otherwise try to iterate over a scalar's infinite domain.
    let udfs_inlined = inline::inline_non_iterable_lambdas(expr);
    debug!("UDFs inlined CCL:\n{}", symbolic(&udfs_inlined));
    typecheck(&udfs_inlined).expect("type error after UDF inlining");

    let lambda_elim = lambda_elim::run(udfs_inlined).errs()?;
    debug!("λ-eliminated CCL:\n{}", symbolic(&lambda_elim));
    debug!("λ-eliminated typed CCL:\n{}", symbolic_typed(&lambda_elim));

    check_fully_typed(&lambda_elim).expect("missing types");
    typecheck(&lambda_elim).expect("type error after lambda elimination");

    let join_planned = join_plan::run(lambda_elim);
    debug!(
        "Join-planned CCL:\n{} : {}",
        symbolic(&join_planned),
        join_planned.ty
    );
    debug!("Join-planned CCL:\n{}", symbolic_typed(&join_planned));

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
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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
}

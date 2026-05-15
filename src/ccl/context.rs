// ---------------------------------------------------------------------------
// Context object for state shared across all phases of compilation like
// builtins
// ---------------------------------------------------------------------------

use std::{cell::RefCell, rc::Rc};

use crate::chl_parser;
use log::debug;

use crate::{
    ccl::{
        Expr, Type,
        infer::{InferError, TypeInferenceContext, check_fully_typed, infer, typecheck},
        inline, join_plan, lambda_elim,
        lower::{LoweringContext, LoweringError, lower_stmts},
        remove_defers,
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

/// Errors a user can hit when compiling a CHL program.
///
/// Bundles every pipeline stage that can fail on bad *user input*: parsing,
/// lowering (unsupported construct), type inference, and operator-graph
/// conversion. Stage-internal consistency checks (`typecheck`,
/// `check_fully_typed` between passes, lambda-elim of a typed tree) are
/// invariants — they panic with `.expect` because firing them indicates a
/// compiler bug, not user error.
///
/// Use [`Self::eprint`] for source-context rendering: parser errors get
/// ariadne reports with red/yellow underlines; the other variants render
/// as plain `error: …` lines. Source-aware spans for lowering/inference
/// errors are future work.
#[derive(Debug)]
pub enum CompileError {
    /// The parser rejected the input.
    Parse(Vec<chl_parser::ParseError>),
    /// The (parseable) AST uses a construct the lowering pass does not
    /// support yet.
    Lower(LoweringError),
    /// Type inference failed.
    Infer(Vec<InferError>),
    /// Lambda elimination failed.
    LambdaElim(lambda_elim::LambdaElimError),
    /// Defer/feed resolution failed (e.g. multiple definitions for one
    /// deferred output).
    RemoveDefers(remove_defers::DeferError),
    /// Operator-graph conversion failed.
    Conversion(ConversionError),
}

impl CompileError {
    /// Render this error as a plain-ASCII string with source-code context.
    ///
    /// - [`CompileError::Parse`] is rendered via ariadne with colour
    ///   disabled (gutter, source line, underlines, labels — all rendered
    ///   in Unicode box-drawing). Suitable for inclusion in panic
    ///   messages, log files, snapshots, or piping through grep.
    /// - The other variants render as plain `error: …` lines because
    ///   they don't yet carry source spans.
    pub fn render(&self, src_name: &str, src: &str) -> String {
        let mut buf: Vec<u8> = Vec::new();
        match self {
            CompileError::Parse(errs) => {
                for e in errs {
                    e.to_report_with_config(src_name, ariadne::Config::default().with_color(false))
                        .write((src_name, ariadne::Source::from(src)), &mut buf)
                        .expect("ariadne write should not fail on Vec<u8>");
                }
            }
            CompileError::Lower(LoweringError::Unsupported(msg)) => {
                buf.extend_from_slice(
                    format!("error: lowering rejected this program: {msg}\n").as_bytes(),
                );
            }
            CompileError::Infer(errs) => {
                for e in errs {
                    buf.extend_from_slice(format!("error: type inference: {e:?}\n").as_bytes());
                }
            }
            CompileError::LambdaElim(e) => {
                buf.extend_from_slice(format!("error: lambda elimination: {e:?}\n").as_bytes());
            }
            CompileError::RemoveDefers(e) => {
                buf.extend_from_slice(format!("error: defer/feed resolution: {e:?}\n").as_bytes());
            }
            CompileError::Conversion(e) => {
                buf.extend_from_slice(
                    format!("error: operator-graph conversion: {e:?}\n").as_bytes(),
                );
            }
        }
        String::from_utf8_lossy(&buf).into_owned()
    }

    /// Render and print this error to stderr.
    ///
    /// [`CompileError::Parse`] uses ariadne's coloured `eprint` (so
    /// terminal output is pretty); the other variants use plain
    /// `eprintln!`. For tests that want the rendering in a panic
    /// message (so cargo test groups it with the failing test's
    /// output), see [`CompileResultExt::unwrap_or_render`] which uses
    /// [`Self::render`] instead.
    pub fn eprint(&self, src_name: &str, src: &str) {
        match self {
            CompileError::Parse(errs) => {
                for e in errs {
                    e.to_report(src_name)
                        .eprint((src_name, ariadne::Source::from(src)))
                        .expect("ariadne eprint should not fail on stderr");
                }
            }
            other => eprint!("{}", other.render(src_name, src)),
        }
    }
}

impl From<Vec<chl_parser::ParseError>> for CompileError {
    fn from(v: Vec<chl_parser::ParseError>) -> Self {
        Self::Parse(v)
    }
}

impl From<LoweringError> for CompileError {
    fn from(e: LoweringError) -> Self {
        Self::Lower(e)
    }
}

impl From<Vec<InferError>> for CompileError {
    fn from(v: Vec<InferError>) -> Self {
        Self::Infer(v)
    }
}

impl From<lambda_elim::LambdaElimError> for CompileError {
    fn from(e: lambda_elim::LambdaElimError) -> Self {
        Self::LambdaElim(e)
    }
}

impl From<remove_defers::DeferError> for CompileError {
    fn from(e: remove_defers::DeferError) -> Self {
        Self::RemoveDefers(e)
    }
}

impl From<ConversionError> for CompileError {
    fn from(e: ConversionError) -> Self {
        Self::Conversion(e)
    }
}

/// Extension trait for `Result<T, CompileError>`.
///
/// Lets test code (or any non-prod caller) collapse the
/// `compile_program` result to its `T` while still getting ariadne-rendered
/// error output on failure. Use sparingly outside tests — production code
/// should match on the error variant and decide what to do.
///
/// ```ignore
/// use cambra::ccl::context::{compile_program, CompileResultExt};
/// let compiled = compile_program(&mut ctx, code, consumer)
///     .unwrap_or_render("<test>", code);
/// ```
pub trait CompileResultExt<T> {
    /// Return `Ok` payload, or pretty-print the error via
    /// [`CompileError::eprint`] (so it shows up in the test runner's
    /// captured stderr) and panic.
    fn unwrap_or_render(self, src_name: &str, src: &str) -> T;
}

impl<T> CompileResultExt<T> for Result<T, CompileError> {
    fn unwrap_or_render(self, src_name: &str, src: &str) -> T {
        self.unwrap_or_else(|e| {
            // Bundle the rendered output into the panic message rather
            // than writing to stderr directly: ariadne's `eprint` writes
            // raw to file-descriptor 2, which bypasses cargo test's
            // per-test output capture, so the error would show up
            // *outside* the failing test's output block. Putting it in
            // the panic message means cargo test groups it with the
            // test's `---- TEST stdout ----` section as expected.
            panic!("compilation failed:\n{}", e.render(src_name, src))
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
    /// operator that dispatches to the registered [`DataSink`].
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
) -> Result<CompiledProgram, CompileError> {
    // ---- User-facing failure points ----
    //
    // The four `?` returns below correspond to the four ways a user can
    // hand us a program we can't compile: a parse error, an unsupported
    // construct (lowering), a type error (inference), and a shape the
    // operator-graph builder can't realise (conversion). Stage-internal
    // consistency checks (`typecheck`, `check_fully_typed`) keep their
    // `.expect` because firing them means the compiler itself is wrong,
    // not the user's input.
    let module = chl_parser::parse_module(code).into_result()?;
    let mut expr = lower_stmts(&module.body, ctx.lowering_ctx())?;

    // Drain sink bindings discovered during lowering before taking sources.
    let sink_bindings_registry = ctx.lowering_ctx().take_sink_bindings();

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
    infer(&mut expr, infer_ctx)?;
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

    let lambda_elim = lambda_elim::run(udfs_inlined)?;
    debug!("λ-eliminated CCL:\n{}", symbolic(&lambda_elim));
    debug!("λ-eliminated typed CCL:\n{}", symbolic_typed(&lambda_elim));

    check_fully_typed(&lambda_elim).expect("missing types");
    typecheck(&lambda_elim).expect("type error after lambda elimination");

    let defers_removed = remove_defers::run(lambda_elim)?;
    debug!("Defers removed CCL:\n{}", symbolic(&defers_removed));
    debug!(
        "Defers removed typed CCL:\n{}",
        symbolic_typed(&defers_removed)
    );
    check_fully_typed(&defers_removed).expect("missing types after removing defers");
    typecheck(&defers_removed).expect("type error after removing defers");

    let join_planned = join_plan::run(defers_removed);
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
        let op = convert_to_operators(&join_planned, ctx.conversion_ctx())?;
        vec![("main".to_string(), op)]
    } else {
        convert_record_fields_to_operators(&join_planned, ctx.conversion_ctx())?
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

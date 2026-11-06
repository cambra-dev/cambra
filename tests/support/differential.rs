//! Running one program through the compiler and through the differential interpreter, each
//! observed through the sink `out`, and reading both answers in the interpreter's domain.
//!
//! The compiler's side of both differential suites, the hand-written cases
//! (`tests/it/differential_interp.rs`) and the generated grid (`tests/it/generated_pairs.rs`), is
//! a dispatched run ([`dispatch`]). [`run_compiled`] runs a program in pull mode, for the
//! compilation-pipeline tests' `check_sink`.

use cambra::ccl::Type;
use cambra::ccl::context::{CompiledProgram, GlobalContext, compile_program};
use cambra::interpreter::dispatcher::run_program;
use cambra::interpreter::{Consumer, SinkReadError, TestSink, Value as TileValue};
use chl_interp::{Collection, Value};

/// How many scheduler pulls a program gets to complete before it counts as not finishing.
const CAP: usize = 10_000;

/// What the compiler made of a program.
#[derive(Debug)]
pub enum Compiled {
    Value(Value),
    /// The compile errors, rendered.
    Rejected(String),
    /// The program completed and its sink could not state a value.
    Unreadable(SinkReadError),
    /// The program did not complete: within [`CAP`] pulls in pull mode, or by the end of a
    /// dispatched run.
    DidNotFinish,
}

impl std::fmt::Display for Compiled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Compiled::Value(v) => write!(f, "{v}"),
            Compiled::Rejected(errs) => write!(f, "rejected: {errs}"),
            Compiled::Unreadable(e) => write!(f, "sink unreadable: {e}"),
            Compiled::DidNotFinish => write!(f, "did not finish"),
        }
    }
}

/// Compile and run `source` in pull mode, answering what sink `out` observed.
pub fn run_compiled(source: &str) -> Compiled {
    let mut ctx = GlobalContext::default();
    let sink = ctx.register_test_sink("out");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let loaded = cambra::ccl::load::LoadedProgram::test(source);
    let program = match compile_program(&mut ctx, &loaded, consumer) {
        Ok(p) => p,
        Err(errs) => return Compiled::Rejected(format!("{errs:?}")),
    };
    let completed = (0..CAP).any(|_| {
        ctx.scheduler().check_for_notifications();
        program.done.try_recv().is_ok()
    });
    if !completed {
        return Compiled::DidNotFinish;
    }
    read_out(&program, &sink)
}

/// What `sink`, the sink `out` of `program`, holds, read as a value of its type.
fn read_out(program: &CompiledProgram, sink: &TestSink) -> Compiled {
    // The program's type is the record of its sinks' types.
    let Type::Record(sinks) = program.ast.ty.peel_refinements() else {
        panic!(
            "a program with a sink is typed as a record of sinks: {}",
            program.ast.ty
        );
    };
    let ty = sinks
        .iter()
        .find(|(name, _)| name.name() == "out")
        .map(|(_, ty)| ty.clone())
        .expect("the program's type names its sink `out`");
    match sink.value() {
        Ok(v) => Compiled::Value(convert(v, &ty)),
        Err(e) => Compiled::Unreadable(e),
    }
}

/// What a dispatched run made of a program.
pub enum Dispatched {
    /// What the run made of it, as [`run_compiled`] reports it.
    Ran(Compiled),
    /// Why the planner refused it.
    Refused(String),
    /// The runs at morsels of one row and of every row made different things of it, each
    /// rendered.
    MorselsDisagree { one: String, every: String },
}

impl std::fmt::Display for Dispatched {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Dispatched::Ran(ran) => ran.fmt(f),
            Dispatched::Refused(why) => write!(f, "refused: {why}"),
            Dispatched::MorselsDisagree { one, every } => write!(
                f,
                "the dispatched runs disagree: at morsels of 1 {one}, at morsels of every row \
                 {every}"
            ),
        }
    }
}

/// Compile `source` for a dispatched run and run its pipelines at morsels of `rows`
/// (`cambra::interpreter::dispatcher::run_program`), answering what sink `out` observed.
fn run_dispatched(source: &str, rows: usize) -> Dispatched {
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    let sink = ctx.register_test_sink("out");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let loaded = cambra::ccl::load::LoadedProgram::test(source);
    let mut program = match compile_program(&mut ctx, &loaded, consumer) {
        Ok(p) => p,
        Err(errs) => return Dispatched::Ran(Compiled::Rejected(format!("{errs:?}"))),
    };
    if let Err(refused) = run_program(&mut program, rows) {
        return Dispatched::Refused(refused.to_string());
    }
    if program.done.try_recv().is_err() {
        return Dispatched::Ran(Compiled::DidNotFinish);
    }
    Dispatched::Ran(read_out(&program, &sink))
}

/// What a dispatched run of `source` makes of it at morsels of one row, where a run at morsels
/// of every row makes the same of it, and [`Dispatched::MorselsDisagree`] otherwise.
///
/// Two values are the same where they compare equal, so a commit time compares by its rank
/// (`chl_interp::Value`); any other outcome is the same where it renders the same.
pub fn dispatch(source: &str) -> Dispatched {
    let one = run_dispatched(source, 1);
    let every = run_dispatched(source, usize::MAX);
    let same = match (&one, &every) {
        (Dispatched::Ran(Compiled::Value(a)), Dispatched::Ran(Compiled::Value(b))) => a == b,
        (a, b) => a.to_string() == b.to_string(),
    };
    match same {
        true => one,
        false => Dispatched::MorselsDisagree {
            one: one.to_string(),
            every: every.to_string(),
        },
    }
}

/// The tests whose programs the planner refuses, with the start of the refusal each expects:
/// one `<test name>\t<refusal>` line each, a test's name as its thread names it.
const DISPATCH_REFUSED: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/it/dispatch_refused.txt"
));

/// Check that a dispatched run of `source` ([`dispatch`]) completes with a value, or that the
/// planner refuses it as [`DISPATCH_REFUSED`] pins for the running test. For a test that checks
/// only that the compiler runs a program, whatever it answers.
///
/// # Panics
///
/// Where the run produces no value, or is refused where nothing pins it, or a pin names a refusal
/// the run no longer makes.
pub fn check_dispatched(source: &str) {
    let test = std::thread::current()
        .name()
        .unwrap_or("an unnamed thread")
        .to_string();
    let pin = DISPATCH_REFUSED
        .lines()
        .filter_map(|line| line.split_once('\t'))
        .find(|(name, _)| *name == test)
        .map(|(_, refusal)| refusal);
    match (dispatch(source), pin) {
        (Dispatched::Ran(Compiled::Value(_)), None) => {}
        (Dispatched::Refused(why), Some(refusal)) => assert!(
            why.starts_with(refusal),
            "{test}: the planner refuses the program as `{why}`, where \
             tests/it/dispatch_refused.txt pins `{refusal}`"
        ),
        (other, Some(refusal)) => panic!(
            "{test}: the dispatched run is no longer refused ({refusal}): {other}; remove its \
             line from tests/it/dispatch_refused.txt"
        ),
        (Dispatched::Refused(why), None) => {
            let line = why.lines().next().unwrap_or_default();
            panic!(
                "{test}: the planner refuses the program: {why}\n  pin it in \
                 tests/it/dispatch_refused.txt as `{test}<TAB>{line}`, or make it run"
            )
        }
        (other, None) => panic!("{test}: the dispatched run: {other}\n  program:\n{source}"),
    }
}

/// Run `source` through the differential interpreter, answering what sink `out` observed.
pub fn run_interpreted(source: &str) -> Result<Value, String> {
    let mut obs = chl_interp::run(source).map_err(|e| e.to_string())?;
    obs.remove("out")
        .ok_or_else(|| "the program declares no sink `out`".to_string())
}

/// Read a compiled value of type `ty` in the interpreter's domain.
///
/// `UInt` reads as `Int`: a key the compiler numbers is the key the interpreter numbers, and
/// the two integer types differ only in representation. A key of type `Txn` is a commit
/// time, which the runtime represents as a plain `UInt`.
pub fn convert(v: TileValue, ty: &Type) -> Value {
    match (v, ty.peel_refinements()) {
        (
            TileValue::Function(bindings),
            Type::Fun {
                domain, codomain, ..
            },
        ) => Value::Collection(Collection::from_entries(
            bindings
                .into_iter()
                .map(|b| (convert(b.input, domain), convert(b.output, codomain)))
                .collect(),
        )),
        (TileValue::UInt(u), Type::Txn) => Value::CommitTime(u as i64),
        (TileValue::Union { tag, inner }, Type::Variant(arms, _)) => {
            let arm = arms
                .iter()
                .find(|(k, _)| *k == tag)
                .map(|(_, t)| t.clone())
                .unwrap_or(Type::Hole);
            Value::Variant {
                tag: tag.to_string(),
                payload: Box::new(convert(*inner, &arm)),
            }
        }
        // A nominal value is held as the variant of its constructors; the type says which
        // declaration's constructor the tag is.
        (TileValue::Union { tag, inner }, Type::Nominal(decl, args)) => {
            let ctor = tag.to_string();
            let payload = decl
                .ctor(&ctor)
                .map(|c| decl.instantiate(&c.payload(), args))
                .unwrap_or(Type::Hole);
            Value::Nominal {
                ty: decl.name.to_string(),
                ctor,
                payload: Box::new(convert(*inner, &payload)),
            }
        }
        // A tuple is held as a record keyed by position, `_0`, `_1`, ….
        (TileValue::Record(fields), Type::Tuple(tys)) => Value::Record(
            fields
                .into_iter()
                .map(|(n, v)| {
                    let t = n
                        .strip_prefix('_')
                        .and_then(|i| i.parse::<usize>().ok())
                        .and_then(|i| tys.get(i).cloned());
                    (n.to_string(), convert(v, &t.unwrap_or(Type::Hole)))
                })
                .collect(),
        ),
        (TileValue::Record(fields), Type::Record(tys)) => Value::Record(
            fields
                .into_iter()
                .map(|(n, v)| {
                    let t = tys
                        .iter()
                        .find(|(f, _)| f.to_string() == n.as_str())
                        .map(|(_, t)| t.clone());
                    (n.to_string(), convert(v, &t.unwrap_or(Type::Hole)))
                })
                .collect(),
        ),
        (v, _) => convert_untyped(v),
    }
}

/// [`convert`] where the type says nothing more than the value does.
fn convert_untyped(v: TileValue) -> Value {
    match v {
        TileValue::Int(i) => Value::Int(i),
        TileValue::UInt(u) => Value::Int(u as i64),
        TileValue::String(s) => Value::Str(s.to_string()),
        TileValue::Bool(b) => Value::Bool(b),
        TileValue::Unit => Value::Unit,
        TileValue::Record(fields) => Value::Record(
            fields
                .into_iter()
                .map(|(n, v)| (n.to_string(), convert_untyped(v)))
                .collect(),
        ),
        TileValue::Union { tag, inner } => Value::Variant {
            tag: tag.to_string(),
            payload: Box::new(convert_untyped(*inner)),
        },
        TileValue::Function(bindings) => Value::Collection(Collection::from_entries(
            bindings
                .into_iter()
                .map(|b| (convert_untyped(b.input), convert_untyped(b.output)))
                .collect(),
        )),
        TileValue::ComputableFunction(_) => {
            panic!("a function value reached a sink, which cannot happen")
        }
    }
}

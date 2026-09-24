//! Running one program through the compiler and through the differential interpreter, each
//! observed through the sink `out`, and reading both answers in the interpreter's domain.
//!
//! Compiled into the differential suite `tests/differential_interp.rs`.

use cambra::ccl::Type;
use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::interpreter::{Consumer, SinkReadError, Value as TileValue};
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
    /// The program did not complete within [`CAP`] pulls.
    DidNotFinish,
}

impl std::fmt::Display for Compiled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Compiled::Value(v) => write!(f, "{v}"),
            Compiled::Rejected(errs) => write!(f, "rejected: {errs}"),
            Compiled::Unreadable(e) => write!(f, "sink unreadable: {e}"),
            Compiled::DidNotFinish => write!(f, "did not finish within {CAP} pulls"),
        }
    }
}

/// Compile and run `source`, answering what sink `out` observed.
pub fn run_compiled(source: &str) -> Compiled {
    let mut ctx = GlobalContext::default();
    let sink = ctx.register_test_sink("out");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let program = match compile_program(&mut ctx, source, consumer) {
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
    // The program's type is the record of its sinks' types.
    let Type::Record(sinks) = program.ast.ty.peel_refinements() else {
        panic!(
            "a program with a sink is typed as a record of sinks: {}",
            program.ast.ty
        );
    };
    let ty = sinks
        .iter()
        .find(|(name, _)| name == "out")
        .map(|(_, ty)| ty.clone())
        .expect("the program's type names its sink `out`");
    match sink.value() {
        Ok(v) => Compiled::Value(convert(v, &ty)),
        Err(e) => Compiled::Unreadable(e),
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
/// `UInt` is `Int`: a key the compiler numbers is the same key the
/// interpreter numbers, and keeping two integer types apart here would make every
/// positional collection differ for a reason that is about representation. And a key
/// of type `Txn` is a commit time, which the runtime represents as a plain `UInt`.
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
        (TileValue::Record(fields), Type::Record(tys)) => Value::Record(
            fields
                .into_iter()
                .map(|(n, v)| {
                    let t = tys.iter().find(|(f, _)| *f == n).map(|(_, t)| t.clone());
                    (n, convert(v, &t.unwrap_or(Type::Hole)))
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
                .map(|(n, v)| (n, convert_untyped(v)))
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

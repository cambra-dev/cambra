//! Replacing a running program with a new version of its source.
//!
//! A [`LiveProgram`] is a compiled program plus the operation that swaps it for
//! another. The new version inherits the running one's sources and sinks and
//! whichever of its operators compute the same thing; everything else is rebuilt.
//!
//! # What an update may change
//!
//! Its logic freely, and its sources and sinks by addition: a version may open a
//! source or a sink the running program does not have and serves it as soon as
//! the swap completes, and one it stops serving is retired. What it may not do is
//! break the continuity of state — see [`update`](LiveProgram::update).
//!
//! # What survives it
//!
//! Every `Let` binding and every `Transact` store whose computation is
//! unchanged, together with what that computation has accumulated. Conversion
//! identifies each by the α-invariant
//! [`resolved_hash`](crate::ccl::content_hash::resolved_hash) of the term it
//! realizes and adopts the operator behind a matching one, so an accumulator the
//! update did not touch keeps its accumulation. Reuse is hereditary: an operator
//! is adopted only when every binding it reads was adopted too, so a
//! carried-forward operator is never left reading a subgraph the update rebuilt.
//! How much an update reuses does not depend on how many updates preceded it.
//!
//! A variable whose logic *was* edited keeps its value too. Its store is rebuilt,
//! and each variable it still declares is seeded from what the retired version
//! left it holding, so the new rule governs from the swap onwards without
//! discarding what came before.
//!
//! A binding compiled under an iteration is rebuilt regardless. Its operator is
//! parameterized by an iteration input that is not part of the term, so the term
//! does not identify it.

use std::sync::mpsc;

use crate::ccl::{
    context::{CompileError, CompiledProgram, GlobalContext, Phase, compile_program},
    diff::diff,
};
use crate::interpreter::{
    Consumer, Value,
    operator_conversion::{ReuseTally, StateConflict, TRANSACTION_STORE_ID},
    tile_operators::TileProducer,
};

/// Builds the consumer that wakes the driver for a program's `main` output.
///
/// Called once per version: each compilation subscribes its own.
pub type MainConsumerFactory<'a> = &'a dyn Fn() -> Box<dyn Consumer>;

/// Name a mutable variable the way its author can recognize it.
///
/// Both kinds carry their own spelling as their key: a transactional variable
/// always did, and an induction accumulator does now that the write set is
/// keyed by the variable written. A loop's accumulator is qualified by the
/// source its loop reads, which is what tells two loops' variables apart when
/// they share a name.
fn describe_variable(store_id: &str, key: &Value) -> String {
    let key = match key {
        Value::String(name) => name.to_string(),
        other => format!("{other:?}"),
    };
    if store_id == TRANSACTION_STORE_ID {
        format!("transactional variable `{key}`")
    } else {
        format!("`{key}`, of the loop over `{store_id}`")
    }
}

/// A compiled program being driven, and the version-swap operation over it.
pub struct LiveProgram {
    program: CompiledProgram,
    /// The `main` output's producer, held out of `program.outputs` so the other
    /// outputs stay borrowable while the driver pulls it.
    main_producer: Option<Box<dyn TileProducer>>,
}

/// What one accepted [`LiveProgram::update`] did.
pub struct UpdateReport {
    /// The rendered difference between the two versions.
    pub diff: String,
    /// How much of the replaced version the new one adopted.
    pub reuse: ReuseTally,
}

impl LiveProgram {
    /// Compile `code` and subscribe it.
    pub fn start(
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Self, Vec<CompileError>> {
        let mut program = compile_program(ctx, code, main_consumer())?;
        let main_producer = program.main_mut().and_then(|o| o.producer.take());
        Ok(LiveProgram {
            program,
            main_producer,
        })
    }

    /// The compiled program.
    pub fn program(&self) -> &CompiledProgram {
        &self.program
    }

    /// The `main` output's producer, for inspection.
    pub fn main_producer(&self) -> Option<&dyn TileProducer> {
        self.main_producer.as_deref()
    }

    /// The `main` output's producer, for a driver to pull.
    pub fn main_producer_mut(&mut self) -> Option<&mut Box<dyn TileProducer>> {
        self.main_producer.as_mut()
    }

    /// Whether this program has a `main` output to drive.
    pub fn has_main(&self) -> bool {
        self.main_producer.is_some()
    }

    /// Fires once every sink output has reached a terminal tile.
    pub fn done(&self) -> &mpsc::Receiver<()> {
        &self.program.done
    }

    /// The source this version was compiled from.
    pub fn source(&self) -> &str {
        &self.program.source
    }

    /// Render how `code` differs from this version, comparing at `phase`.
    ///
    /// Compiles both sides against the running sources and sinks, which opens nothing
    /// and leaves the running program untouched. Compiling the new version in a
    /// fresh [`GlobalContext`] instead would try to bind a port this program
    /// already holds.
    pub fn diff_against(
        &self,
        ctx: &GlobalContext,
        code: &str,
        phase: Phase,
    ) -> Result<String, Vec<CompileError>> {
        let old = ctx.sources_and_sinks().compile_to(self.source(), phase)?;
        let new = ctx.sources_and_sinks().compile_to(code, phase)?;
        let d = diff(&old, &new);
        if d.is_identical() {
            return Ok(format!("no difference at phase {phase:?}\n"));
        }
        Ok(format!(
            "phase {phase:?}: {} divergence(s), {} shared root(s)\n\n{d}",
            d.divergences().len(),
            d.shared_roots().len(),
        ))
    }

    /// Replace this program with the version `code` describes.
    ///
    /// Rejected when the new version cannot **take over the state**: every
    /// mutable variable the running program holds a value for must be one the
    /// new version still declares, at the same type and under the same store, so
    /// that its value is seeded rather than discarded. Those are the three
    /// refusals [`StateConflict`] names. Everything else is allowed: logic
    /// freely, and sources and sinks by addition.
    ///
    /// That is the whole guard, and it is narrower than it first looks. A
    /// version that adds an `http_serve` route serves it as soon as the swap
    /// completes, and one that stops serving a route retires it, so that address
    /// answers 404 rather than hanging. Only a value with nowhere to be seeded
    /// from is refused, because that is the one outcome an author cannot see
    /// having happened: the program carries on answering and only the
    /// accumulated history is gone.
    ///
    /// On `Err` the running program is untouched and still serving: both the
    /// compile to [`Phase::Planning`] and this check run before anything is torn
    /// down.
    ///
    /// # Panics
    ///
    /// Panics if the real compile fails after the [`Phase::Planning`] one
    /// succeeded. The two run the same passes over the same sources and sinks, so
    /// disagreement is a compiler bug — and one that has already taken the program down, which is
    /// not a state to hand back to a caller as a rejection.
    pub fn update(
        &mut self,
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<UpdateReport, Vec<CompileError>> {
        let diff = self.diff_against(ctx, code, Phase::AsOfRead)?;
        let planned = ctx.sources_and_sinks().compile_to(code, Phase::Planning)?;

        // What the new version can take over is read off its planned tree,
        // before anything is built from it, so a version that would lose a value
        // or change its type is refused while the running program is whole.
        let conflicts = ctx.state_conflicts(&planned);
        if !conflicts.is_empty() {
            let mut lines: Vec<String> = conflicts
                .iter()
                .map(|c| {
                    let what = describe_variable(c.store(), c.key());
                    match c {
                        StateConflict::Dropped { .. } => {
                            format!("{what} is no longer declared")
                        }
                        StateConflict::Moved { now, .. } => {
                            format!("{what} now belongs to `{now}` instead")
                        }
                        StateConflict::Retyped { held, declared, .. } => {
                            format!("{what} is now {declared} rather than {held}")
                        }
                    }
                })
                .collect();
            lines.sort();
            return Err(vec![CompileError::Unsupported(format!(
                "this version cannot take over state the running program is holding: {}. \
A value has nowhere to be seeded from unless the new version declares the same \
variable at the same type.",
                lines.join(", "),
            ))]);
        }

        self.tear_down();
        ctx.retire_version();
        let next = LiveProgram::start(ctx, code, main_consumer)
            .expect("a version that compiled to Planned must compile to operators");
        *self = next;
        Ok(UpdateReport {
            diff,
            reuse: ctx.reuse(),
        })
    }

    /// Drop this version's operator graph.
    ///
    /// Detaching the sinks is what ends this version's dispatch, and dropping
    /// the outputs alone does not achieve it: an operator the next version
    /// carries forward still holds the notification closure that reaches this
    /// version's sink consumers, so they would keep being woken and keep writing
    /// to sinks the next version now owns
    /// ([`SinkConsumer::detach`](crate::interpreter::SinkConsumer::detach)).
    fn tear_down(&mut self) {
        self.main_producer = None;
        for output in &self.program.outputs {
            if let Some(consumer) = &output.sink_consumer {
                consumer.borrow_mut().detach();
            }
        }
        self.program.outputs.clear();
    }
}

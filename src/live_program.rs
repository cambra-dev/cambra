//! Replacing a running program with a new version of its source.
//!
//! A [`LiveProgram`] is a compiled program plus the operation that swaps it for
//! another. The new version inherits the running one's external endpoints and
//! whichever of its operators compute the same thing; everything else is rebuilt.
//!
//! # What an update may change
//!
//! The logic between the existing sources and sinks, and nothing else. The new
//! version compiles with its endpoints [`Inherited`](Endpoints::Inherited), so
//! naming a source or a sink the running program does not hold is a compile
//! error rather than a second listener on the same port.
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
//! A rebuilt operator is not thereby empty: it draws on the operators it reads,
//! and a reused source still holds what it has not released, so a rebuilt store
//! re-derives its history from those retained inputs. See
//! `src/ccl/design/live-update.md`, "What an update does not do".
//!
//! A binding compiled under an iteration is rebuilt regardless. Its operator is
//! parameterized by an iteration input that is not part of the term, so the term
//! does not identify it.

use std::sync::mpsc;

use crate::ccl::{
    context::{
        CompileError, CompileStage, CompiledProgram, Endpoints, GlobalContext,
        compile_to_inherited, compile_version,
    },
    diff::diff,
};
use crate::interpreter::{Consumer, tile_operators::TileProducer};

/// Builds the consumer that wakes the driver for a program's `main` output.
///
/// Called once per version: each compilation subscribes its own.
pub type MainConsumerFactory<'a> = &'a dyn Fn() -> Box<dyn Consumer>;

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
    /// How many `Let` bindings the new version reused, against how many it bound.
    pub reuse: (usize, usize),
}

impl LiveProgram {
    /// Compile `code` and subscribe it.
    ///
    /// `endpoints` is [`Open`](Endpoints::Open) for a program's first version,
    /// which opens the sources and sinks every later version inherits.
    pub fn start(
        ctx: &mut GlobalContext,
        code: &str,
        endpoints: Endpoints,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Self, Vec<CompileError>> {
        let mut program = compile_version(ctx, code, main_consumer(), endpoints)?;
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

    /// Render how `code` differs from this version, comparing at `stage`.
    ///
    /// Compiles both sides against the running endpoints, which opens nothing
    /// and leaves the running program untouched. Compiling the new version in a
    /// fresh [`GlobalContext`] instead would try to bind a port this program
    /// already holds.
    pub fn diff_against(
        &self,
        ctx: &GlobalContext,
        code: &str,
        stage: CompileStage,
    ) -> Result<String, Vec<CompileError>> {
        let old = compile_to_inherited(ctx.endpoints(), self.source(), stage)?;
        let new = compile_to_inherited(ctx.endpoints(), code, stage)?;
        let d = diff(&old, &new);
        if d.is_identical() {
            return Ok(format!("no difference at stage {stage:?}\n"));
        }
        Ok(format!(
            "stage {stage:?}: {} divergence(s), {} shared root(s)\n\n{d}",
            d.divergences().len(),
            d.shared_roots().len(),
        ))
    }

    /// Replace this program with the version `code` describes.
    ///
    /// On `Err` the running program is untouched and still serving: the whole
    /// frontend runs against a scratch context first, and that staged compile
    /// builds no operators and opens no endpoints. Only once it succeeds is the
    /// running graph torn down.
    ///
    /// # Panics
    ///
    /// Panics if the real compile fails after the staged one succeeded. The two
    /// run the same passes over the same endpoints, so disagreement is a
    /// compiler bug — and one that has already taken the program down, which is
    /// not a state to hand back to a caller as a rejection.
    pub fn update(
        &mut self,
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<UpdateReport, Vec<CompileError>> {
        let diff = self.diff_against(ctx, code, CompileStage::Channelized)?;
        compile_to_inherited(ctx.endpoints(), code, CompileStage::Planned)?;

        self.tear_down();
        ctx.retire_version();
        let next = LiveProgram::start(ctx, code, Endpoints::Inherited, main_consumer)
            .expect("a version that compiled to Planned must compile to operators");
        *self = next;
        Ok(UpdateReport {
            diff,
            reuse: ctx.reuse_tally(),
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

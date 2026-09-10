//! Replacing a running program with a new version of its source.
//!
//! A [`LiveProgram`] is a compiled program plus the operation that swaps it for
//! another. The new version inherits the running one's sources and sinks and
//! whichever of its operators compute the same thing; everything else is rebuilt.
//!
//! # What a reload may change
//!
//! Its logic freely, and its sources and sinks by addition: a version may open a
//! source or a sink the running program does not have and serves it as soon as
//! the swap completes, and one it stops serving is retired. What it may not do is
//! break the continuity of state — see [`reload`](LiveProgram::reload).
//!
//! # What survives it
//!
//! Every `Let` binding, every `Transact` store and every iteration input whose
//! computation is unchanged, together with what that computation has
//! accumulated. The structural diff of the two versions' trees
//! ([`diff`](crate::ccl::diff::diff)) says which node of the new tree stands
//! where each node of the old one did, and conversion keeps the operator
//! recorded at a corresponding node rather than building a second one — so an
//! accumulator the reload did not touch keeps its accumulation, and a fold
//! partway through a collection keeps its place. Reuse is hereditary: an
//! operator is kept only when every binding it reads was kept too, so a
//! carried-forward operator is never left reading a subgraph the reload rebuilt.
//!
//! A variable keeps its value even where its logic was edited. Its store is
//! rebuilt, and each variable it still declares is seeded from what the retired
//! version left it holding, so the new rule governs from the swap onwards without
//! discarding what came before. Neither how much a reload reuses nor what it
//! carries depends on how many reloads preceded it: a kept binding hands on
//! everything recorded under it, which is what keeps a variable declared inside a
//! function body carried across a reload that rebuilt nothing around it.
//!
//! A binding compiled under an iteration is rebuilt regardless. Its operator is
//! parameterized by an iteration input that is not part of the term, so the term
//! does not identify it.

use std::sync::mpsc;

use crate::ccl::{
    context::{
        CompileError, CompiledProgram, GlobalContext, Phase, compile_program, compile_replacement,
    },
    diff::diff,
};
use crate::interpreter::{
    Consumer,
    operator_conversion::{ReuseTally, StateConflict},
    tile_operators::TileProducer,
};

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

/// What one accepted [`LiveProgram::reload`] did.
pub struct ReloadReport {
    /// The rendered difference between the two versions.
    pub diff: String,
    /// How much of the replaced version's graph the new one kept.
    pub reuse: ReuseTally,
}

impl LiveProgram {
    /// Compile `code` and subscribe it.
    pub fn start(
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Self, Vec<CompileError>> {
        Ok(Self::driving(compile_program(ctx, code, main_consumer())?))
    }

    /// Hold `program`, with its `main` producer moved out of the outputs so the
    /// driver can pull it while the other outputs stay borrowable.
    fn driving(mut program: CompiledProgram) -> Self {
        let main_producer = program.main_mut().and_then(|o| o.producer.take());
        LiveProgram {
            program,
            main_producer,
        }
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
    /// Compiles both sides against the running sources and sinks, which opens
    /// nothing and leaves the running program untouched: a route the registry does
    /// not hold is named rather than opened
    /// ([`Endpoints::Inherited`](crate::ccl::lower::Endpoints::Inherited)).
    /// Compiling the new version in a fresh [`GlobalContext`] instead would try to
    /// bind a port this program already holds.
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
    /// new version still declares, at the same type, so that its value is seeded
    /// rather than discarded. Those are the refusals [`StateConflict`] names.
    /// Everything else is allowed: logic freely, sources and sinks by addition,
    /// and a variable moving to another loop, which seeds with the value it held
    /// and counts positions in whatever it now iterates.
    ///
    /// That is the whole guard, and it is narrower than it first looks. A
    /// version that adds an `http_serve` route serves it as soon as the swap
    /// completes, and one that stops serving a route retires it, so that address
    /// answers 404 rather than hanging. What is refused is a value that cannot
    /// be seeded, or cannot be seeded into a decided place, because that is the
    /// one outcome an author cannot see having happened: the program carries on
    /// answering and only the accumulated history is wrong.
    ///
    /// On `Err` the running program is untouched and still serving: both the
    /// compile to [`Phase::Planning`] and this check run before anything is torn
    /// down. That compile opens the endpoints the new version adds, so an address
    /// it cannot bind is one of the errors raised here rather than a failure of
    /// the compile that installs the version — which runs after the teardown and
    /// has nothing to reject to. A refusal hands those ports back.
    ///
    /// The guard's tree is compiled separately from the one that gets built.
    /// `run_frontend` goes from source to a stop phase and nothing continues a
    /// stopped tree into operator conversion, so checking before tearing down
    /// means compiling twice — see `src/ccl/design/hot-reload.md`, "Order of a
    /// reload".
    ///
    /// # Panics
    ///
    /// Panics if the real compile fails after the [`Phase::Planning`] one
    /// succeeded. The two run the same passes over the same sources and sinks,
    /// and the `Planning` one has already taken every port the version needs, so
    /// disagreement is a compiler bug — and one that has already taken the
    /// program down, which is not a state to hand back to a caller as a
    /// rejection.
    pub fn reload(
        &mut self,
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<ReloadReport, Vec<CompileError>> {
        let diff = self.diff_against(ctx, code, Phase::AsOfRead)?;
        // This compile opens the endpoints the new version adds and keeps them,
        // because binding is the one step it and the compile that installs the
        // version would otherwise not share: a port already in use would fail
        // only after the running graph was torn down. Refusing below hands the
        // ports back.
        let planned = ctx
            .sources_and_sinks_mut()
            .compile_to_opening(code, Phase::Planning)
            .inspect_err(|_| ctx.sources_and_sinks_mut().release_unrouted_ports())?;

        // What the new version can take over is read off its planned tree,
        // before anything is built from it, so a version that would lose a value
        // or change its type is refused while the running program is whole.
        let conflicts = ctx.state_conflicts(&planned);
        if !conflicts.is_empty() {
            ctx.sources_and_sinks_mut().release_unrouted_ports();
            let mut lines: Vec<String> = conflicts.iter().map(StateConflict::to_string).collect();
            lines.sort();
            // A swap reports both of its directions, and they render the same.
            lines.dedup();
            // Naming the declarations is the fix for a positional clash, and it is
            // not one an author would guess from the other two refusals.
            let remedy = if conflicts
                .iter()
                .any(|c| matches!(c, StateConflict::Moved { .. }))
            {
                "\nBind each of those declarations to its own name — `a = f(…)` rather than a \
                 bare `f(…)` — and a reload can follow them wherever they move."
            } else {
                ""
            };
            return Err(vec![CompileError::Unsupported(format!(
                "this version cannot take over state the running program is holding: {}. \
A value carries forward only into the same variable, at the same type, and only where the source \
says which variable that is.\n\
Nothing else is refused: logic may change freely, endpoints may come and go, and a variable \
may move between loops.{remedy}",
                lines.join(", "),
            ))]);
        }

        self.tear_down();
        ctx.retire_version();
        // The tree the running graph was built from is still here — `tear_down`
        // drops the producers, not the program — so the compile below can be told
        // which of its nodes this version already has an operator for.
        let next = Self::driving(
            compile_replacement(ctx, code, main_consumer(), &self.program.ast)
                .expect("a version that compiled to Planned must compile to operators"),
        );
        *self = next;
        Ok(ReloadReport {
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

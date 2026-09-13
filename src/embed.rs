//! Embedding a Cambra program in another program.
//!
//! [`Host`] is the whole surface: compile a program against declared channels,
//! push rows into its sources, tick it, and read what its sinks produced. The
//! host owns the clock — nothing here blocks, sleeps or spawns — so the same
//! type drives the `cambra` binary's run loop and a WebAssembly module in a
//! browser tab.
//!
//! ```no_run
//! use cambra::ccl::channels::ChannelDecl;
//! use cambra::embed::Host;
//! use cambra::interpreter::Value;
//!
//! let decls = [
//!     ChannelDecl::source("ticks", "{ticker: String, price: Int}"),
//!     ChannelDecl::sink("out", "Int"),
//! ];
//! let mut host = Host::compile("prog.cambra", "…", &decls)?;
//! host.push("ticks", [Value::Int(1)])?;
//! let produced = host.tick();
//! for (sink, rows) in produced.outputs {
//!     println!("{sink}: {rows:?}");
//! }
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Design: `src/interpreter/design-host-channels.md`.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use crate::ccl::channels::{ChannelDecl, ChannelError, Channels};
use crate::ccl::context::{CompileError, GlobalContext};
use crate::ccl::lower::SocketSubscription;
use crate::ccl::provenance::NodeId;
use crate::inspector_model::{render_frame, snapshot_json};
use crate::interpreter::operator_graph::source_nodes;
use crate::interpreter::value_recorder::{
    DEFAULT_ROWS_PER_RECORDING, SourceWindow, ValueRecorder, render_source_window,
};
use crate::interpreter::{Consumer, Value};
use crate::live_program::LiveProgram;

/// Why a program could not be embedded.
#[derive(Debug)]
pub enum EmbedError {
    /// The channel declarations were rejected.
    Channels(ChannelError),
    /// The program did not compile.
    Compile(Vec<CompileError>),
    /// A row was pushed to a name no source has.
    UnknownSource(String),
    /// A call was made against an address no route serves.
    UnknownRoute { method: String, path: String },
}

impl std::fmt::Display for EmbedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmbedError::Channels(e) => write!(f, "{e}"),
            EmbedError::Compile(errors) => write!(f, "the program did not compile: {errors:?}"),
            EmbedError::UnknownSource(name) => write!(f, "no source named '{name}'"),
            EmbedError::UnknownRoute { method, path } => {
                write!(f, "no route serves '{method} {path}'")
            }
        }
    }
}

impl std::error::Error for EmbedError {}

/// What one [`tick`](Host::tick) produced.
#[derive(Debug, Default)]
pub struct TickResult {
    /// The rows each sink received, for the sinks that received any.
    pub outputs: Vec<(String, Vec<Value>)>,
    /// Whether any operator recorded a value, which is when a frame is worth
    /// rendering.
    pub produced: bool,
    /// Whether every sink has reached a terminal tile. A program reading a live
    /// stream never does.
    pub done: bool,
}

/// A compiled program and everything needed to drive it.
pub struct Host {
    ctx: GlobalContext,
    live: LiveProgram,
    channels: Channels,

    /// Which version is running, counting from `0`. Shipped on the payload and
    /// on every frame so a reader can tell the two apart across a reload.
    generation: Cell<u64>,

    /// The `/api/snapshot` payload for the running version.
    ///
    /// One compile feeds both the payload and the run: `NodeId`s come from a
    /// process-global counter, so compiling again for the payload would name
    /// different nodes than the graph being driven. [`Host::reload`] re-renders
    /// it from the version it installed, for the same reason.
    snapshot: String,

    /// The recorder, installed for the whole subscribe.
    ///
    /// A producer takes its handle when its `ProducerBase` is built, inside
    /// `compile_program`, and there is no traversal of the live graph to hand
    /// one out afterwards — so a host that might ever want a frame installs one
    /// at compile time or never has one.
    recorder: Rc<RefCell<ValueRecorder>>,

    /// The graph node each source belongs to, so a window can name it and a
    /// click in a pane resolves.
    source_nodes: HashMap<String, NodeId>,

    /// Recordings published so far, to tell a tick that produced something from
    /// one that only polled.
    published_through: Cell<u64>,

    /// Frames rendered so far. A reader that reconnects can tell it is behind.
    published: Cell<u64>,

    tick: Cell<u64>,

    /// The windows sampled on the last producing tick, so `frame` renders what
    /// that tick delivered rather than what a later poll has since released.
    last_windows: RefCell<Vec<SourceWindow>>,
}

impl Host {
    /// Compile `code` against `channels`, ready to be driven.
    ///
    /// `name` labels the program in the inspector payload and in diagnostics.
    pub fn compile(
        name: &str,
        code: &str,
        channels: &[ChannelDecl],
    ) -> Result<Self, Box<EmbedError>> {
        let mut ctx = GlobalContext::default();
        let channels = ctx
            .register_channels(channels)
            .map_err(|e| Box::new(EmbedError::Channels(e)))?;
        let recorder = Rc::new(RefCell::new(ValueRecorder::with_defaults()));
        // An embedded host is pulled by `tick` rather than woken, so it wants no
        // notification of its own.
        let main_consumer = || -> Box<dyn Consumer> { Box::new(|| {}) };
        let live = {
            let _session = crate::interpreter::value_recorder::install(recorder.clone());
            LiveProgram::start(&mut ctx, code, &main_consumer)
                .map_err(|errors| Box::new(EmbedError::Compile(errors)))?
        };
        let snapshot = snapshot_json(live.program(), name, 0);
        channels.observe(&recorder, &live.program().operator_graph);
        let source_nodes = source_nodes(&live.program().operator_graph);
        Ok(Self {
            ctx,
            live,
            generation: Cell::new(0),
            channels,
            snapshot,
            recorder,
            source_nodes,
            published_through: Cell::new(0),
            published: Cell::new(0),
            tick: Cell::new(0),
            last_windows: RefCell::new(Vec::new()),
        })
    }

    /// Replace the running program with a new version of its source.
    ///
    /// The same operation the binary's `/reload` performs, so an embedding host
    /// carries state across a version the way the runtime does rather than by
    /// replaying what it pushed: every operator whose computation is unchanged
    /// keeps running and every mutable variable resumes from the value it held.
    ///
    /// The recorder session is held across it because the replacement rebuilds
    /// the operators it could not keep, and a producer takes its handle when it
    /// is built. The payload and the source-node map are re-rendered from the
    /// version that is now running, since a rebuilt operator is a new `NodeId`.
    pub fn reload(&mut self, name: &str, code: &str) -> Result<(), Box<EmbedError>> {
        let main_consumer = || -> Box<dyn Consumer> { Box::new(|| {}) };
        {
            let _session = crate::interpreter::value_recorder::install(self.recorder.clone());
            self.live
                .reload(&mut self.ctx, code, &main_consumer)
                .map_err(|errors| Box::new(EmbedError::Compile(errors)))?;
        }
        self.generation.set(self.generation.get() + 1);
        self.snapshot = snapshot_json(self.live.program(), name, self.generation.get());
        self.source_nodes = source_nodes(&self.live.program().operator_graph);
        Ok(())
    }

    /// The `/api/snapshot` payload for this program.
    pub fn snapshot(&self) -> &str {
        &self.snapshot
    }

    /// The channels this program was compiled against.
    pub fn channels(&self) -> &Channels {
        &self.channels
    }

    /// What this program subscribes to, for the host to connect on its behalf.
    ///
    /// A `wasm_socket_subscribe` binds a declared source and says where its
    /// rows come from; the host owns the socket — the browser's `WebSocket` in
    /// a page, `tungstenite` in a native driver, a recorded slice replayed
    /// offline — and pushes what it decodes into the named source through
    /// [`push`](Self::push), exactly as it pushes any other source. Nothing in
    /// here connects, which is what lets the construct exist in a module with
    /// no sockets at all.
    ///
    /// Read after a [`compile`](Self::compile) or a [`reload`](Self::reload):
    /// the list is the running version's, so a version that stops reading a
    /// feed drops it and the host closes the socket it was holding.
    pub fn socket_subscriptions(&self) -> &[SocketSubscription] {
        self.ctx.socket_subscriptions()
    }

    /// Append `rows` to the source named `source`.
    pub fn push(
        &mut self,
        source: &str,
        rows: impl IntoIterator<Item = Value>,
    ) -> Result<(), Box<EmbedError>> {
        let handle = self
            .channels
            .source(source)
            .ok_or_else(|| Box::new(EmbedError::UnknownSource(source.to_string())))?;
        handle.borrow_mut().push(rows);
        Ok(())
    }

    /// Make one call against the route `method path`, as `rows`.
    ///
    /// The ingress half of what a `wasm_serve` in the program binds. The reply
    /// leaves through the route's sink, so it arrives in the
    /// [`outputs`](TickResult::outputs) of the tick that computes it, named by
    /// the route — the host correlates a reply to its call by that name and by
    /// arrival order, which is all a single-threaded program can permute.
    ///
    /// A call is a row like any other, which is why this is [`push`](Self::push)
    /// with the route spelled for the caller rather than a second ingress path.
    pub fn request(
        &mut self,
        method: &str,
        path: &str,
        rows: impl IntoIterator<Item = Value>,
    ) -> Result<(), Box<EmbedError>> {
        let (source, _) = self.channels.route(method, path).ok_or_else(|| {
            Box::new(EmbedError::UnknownRoute {
                method: method.to_string(),
                path: path.to_string(),
            })
        })?;
        source.borrow_mut().push(rows);
        Ok(())
    }

    /// Say that no further rows will arrive on `source`.
    pub fn close(&mut self, source: &str) -> Result<(), Box<EmbedError>> {
        let handle = self
            .channels
            .source(source)
            .ok_or_else(|| Box::new(EmbedError::UnknownSource(source.to_string())))?;
        handle.borrow_mut().close();
        Ok(())
    }

    /// Advance the program once and collect what its sinks produced.
    ///
    /// One scheduler pass and one drain per sink. Non-blocking by construction:
    /// `check_for_notifications` polls, and a sink's outbox is read rather than
    /// waited on. A host calls this on whatever clock it has.
    pub fn tick(&mut self) -> TickResult {
        self.recorder.borrow_mut().set_tick(self.tick.get());

        // Sampled before the pull, not after. A `Memo` releases its input from
        // inside `get_impl`, so the release cascade reaches the source buffer
        // partway through the pull — sampling afterwards reads a buffer the pull
        // already drained.
        let windows = self.source_windows();
        self.ctx.scheduler().check_for_notifications();

        // Production rather than recordings: every producer the pull touches
        // records an answer whether or not it carried rows, so a quiet tick
        // counted as production would replace `last_windows` with a window
        // sampled when there was nothing in the buffer.
        let recorded = self.recorder.borrow().produced();
        let produced = recorded != self.published_through.get();
        if produced {
            self.published_through.set(recorded);
            self.last_windows.replace(windows);
            self.tick.set(self.tick.get() + 1);
        }

        let mut outputs = Vec::new();
        let names: Vec<String> = self
            .channels
            .sinks()
            .map(|(name, _)| name.to_string())
            .collect();
        for name in names {
            let rows = self.channels.drain_sink(&name);
            if !rows.is_empty() {
                outputs.push((name, rows));
            }
        }
        // A stable order, because `Channels` holds its sinks in a map and a host
        // comparing two runs' outputs should not see them permute.
        outputs.sort_by(|a, b| a.0.cmp(&b.0));

        TickResult {
            outputs,
            produced,
            done: self.live.done().try_recv().is_ok(),
        }
    }

    /// The live frame for what the program has produced, or `None` if nothing
    /// has been recorded since the last frame.
    ///
    /// `final_frame` marks the last frame of a finished run, so a reader can
    /// tell a converged program from an idle one.
    pub fn frame(&self, final_frame: bool) -> String {
        self.published.set(self.published.get() + 1);
        render_frame(
            &self.recorder,
            &self.last_windows.borrow(),
            self.tick.get(),
            self.generation.get(),
            self.published.get(),
            final_frame,
        )
    }

    /// Each source's retained window, for the frame.
    ///
    /// Over the scheduler's handles rather than the context's sources: a handle
    /// is registered when the program subscribes the source, so a source the
    /// program does not read — `stdin`, which every context registers — reports
    /// no window rather than an empty one.
    fn source_windows(&self) -> Vec<SourceWindow> {
        self.ctx
            .scheduler_ref()
            .sources()
            .filter_map(|(name, handle)| {
                let source = handle.borrow();
                let keys = source.retained_keys()?;
                let values = source.get(keys.clone());
                Some(render_source_window(
                    self.source_nodes.get(name).copied(),
                    name,
                    &keys,
                    &values,
                    source.first_position_for_a_new_producer(),
                    DEFAULT_ROWS_PER_RECORDING,
                ))
            })
            .collect()
    }
}

use std::{collections::HashMap, ops::ControlFlow, path::Path, thread, time::Duration};

use cambra::{
    ccl::{
        context::{GlobalContext, compile_program, eprint_errors},
        load::LoadedProgram,
        provenance::NodeId,
    },
    control_port::{ControlMessage, ControlPort, ControlReply, ControlRequest, service},
    inspector_server::{ServedSnapshot, live::LiveChannel, serve_compiled},
    interpreter::{
        ColumnValue, Consumer, DataSink, SourceRegistry,
        dispatcher::{self, Ended, RunObserver},
        operator_graph::source_nodes,
        tile_operators::Tile,
        value_probe::{
            ProbeSlot, ProbeTable, ROWS_PER_READING, SourceWindow, render_source_window,
            window_tail,
        },
    },
    live_program::{LiveProgram, MAIN_BRANCH},
};
/// Keep retirement, inspector version advancement and source windows in one publication boundary.
fn service_inspected(
    request: &ControlRequest,
    ctx: &mut GlobalContext,
    live: &mut LiveProgram,
    main_consumer: &dyn Fn() -> Box<dyn Consumer>,
    inspection: Option<&mut Inspection>,
    publisher: Option<&Publisher>,
) -> ControlReply {
    let mut publication = publisher.map(|publisher| {
        #[cfg(test)]
        if publisher.shared.windows.try_lock().is_err()
            && let Some(hook) = publisher.shared.handover_blocked.lock().unwrap().take()
        {
            hook();
        }
        publisher
            .shared
            .windows
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    });
    let reply = service(request, ctx, live, main_consumer);
    if let Some(inspection) = inspection
        && inspection.follow(live)
        && let Some(publisher) = publisher
    {
        publisher.followed();
        if let Some(windows) = publication.as_mut() {
            **windows = inspection.sample_sources(ctx.source_registry());
        }
    }
    reply
}

/// The variable that sets the most rows a dispatched run's work package names.
const MORSEL_ROWS_VAR: &str = "CAMBRA_MORSEL_ROWS";

/// The most rows a dispatched run's work package names where [`MORSEL_ROWS_VAR`] is unset.
const DEFAULT_MORSEL_ROWS: usize = 1024;

/// Compile and run `loaded` through the dispatcher, printing its `main` output.
/// Compilation or planning errors return `Err(())`.
///
/// # Panics
///
/// Where [`MORSEL_ROWS_VAR`] is set to anything but a positive count.
fn run_dispatched(loaded: &LoadedProgram) -> Result<(), ()> {
    let rows = morsel_rows();
    let mut ctx = GlobalContext::default();
    let mut program = match compile_program(&mut ctx, loaded, Box::new(|| {})) {
        Ok(program) => program,
        Err(errs) => {
            eprint_errors(&errs, loaded.sources());
            return Err(());
        }
    };
    if let Err(refused) = dispatcher::run_program_into(
        &mut program,
        rows,
        std::sync::Arc::new(PrintedMain),
        &mut || thread::sleep(Duration::from_millis(1)),
    ) {
        eprintln!("error: {refused}");
        return Err(());
    }
    Ok(())
}

/// The most rows a dispatched run's work package names: [`MORSEL_ROWS_VAR`], or
/// [`DEFAULT_MORSEL_ROWS`] where it is unset.
///
/// # Panics
///
/// Where [`MORSEL_ROWS_VAR`] is set to anything but a positive count.
fn morsel_rows() -> usize {
    match std::env::var(MORSEL_ROWS_VAR) {
        Ok(rows) => rows
            .parse::<usize>()
            .ok()
            .filter(|rows| *rows > 0)
            .unwrap_or_else(|| panic!("{MORSEL_ROWS_VAR} is a positive count of rows: {rows}")),
        Err(_) => DEFAULT_MORSEL_ROWS,
    }
}

/// Prints each `main` answer that holds a key or value, or states terminality.
struct PrintedMain;

impl DataSink for PrintedMain {
    fn process(&self, tile: &Tile) {
        if !tile_is_empty(tile) || tile.is_terminal() {
            println!("Got value: {tile:#?}");
        }
    }
}

/// Prints a non-main branch's answers as `Got value from <branch>: …`.
struct PrintedBranch(String);

impl DataSink for PrintedBranch {
    fn process(&self, tile: &Tile) {
        if !tile_is_empty(tile) || tile.is_terminal() {
            println!("Got value from {}: {tile:#?}", self.0);
        }
    }
}

/// The printer of a branch's `main` answers in a dispatched run.
fn print_main(branch: &str) -> std::sync::Arc<dyn DataSink> {
    match branch == MAIN_BRANCH {
        true => std::sync::Arc::new(PrintedMain),
        false => std::sync::Arc::new(PrintedBranch(branch.to_string())),
    }
}

/// The observer of a dispatched run under `--control` or `--inspect`: it records the source
/// windows where a pass has polled, for the publisher ([`Publisher`]) to send with its next frame,
/// and ends the run at the first drained boundary after a control request arrives, which the
/// driver services between two runs.
struct Driver<'a> {
    control: Option<&'a ControlPort>,
    pending: &'a mut Option<ControlMessage>,
    inspection: Option<&'a Inspection>,
    publisher: Option<&'a Publisher>,
    sources: &'a SourceRegistry,
}

impl RunObserver for Driver<'_> {
    /// Probing switches on here where a client watches, as well as on the publisher's timer, and
    /// only the publisher switches it off. `LiveServer::accept` counts a client as watching before
    /// it answers the handshake, so input the client sends after it is taken by a poll that sees
    /// the count, and its readings are recorded.
    ///
    /// The source windows are sampled here, between the poll and the pass's consumes, so a window
    /// holds the arrivals the poll took. The handles are `Rc`, so the run's thread samples them.
    fn polled(&mut self) {
        let (Some(inspection), Some(publisher)) = (self.inspection, self.publisher) else {
            return;
        };
        if inspection.channel.is_watched() && !inspection.probes.is_enabled() {
            inspection.probes.enable();
        }
        if inspection.probes.is_enabled() {
            publisher.record_windows(inspection.sample_sources(self.sources));
        }
    }

    fn drained(&mut self, changed: bool) -> ControlFlow<()> {
        if let Some(message) = self.control.and_then(ControlPort::poll) {
            *self.pending = Some(message);
            return ControlFlow::Break(());
        }
        if !changed {
            thread::sleep(Duration::from_millis(1));
        }
        ControlFlow::Continue(())
    }
}

/// How often the [`Publisher`] reads the probe table.
const PUBLISH_INTERVAL: Duration = Duration::from_millis(100);

/// A thread that publishes probe frames on a timer, independent of a dispatched run's boundaries
/// (`src/inspector_model/design.md`, "Probing follows the live route").
///
/// It switches probing to match whether a client is connected, and sends a frame where a probe took
/// a reading that carried rows since the last frame, or where `main`'s version changed since it. It
/// renders each frame from a copy of the table ([`ProbeSlot::snapshot`]), so no `get` waits on a
/// render.
struct Publisher {
    shared: std::sync::Arc<Published>,
    thread: Option<thread::JoinHandle<()>>,
}

/// What the run's thread shares with the publisher's.
struct Published {
    probes: ProbeSlot,
    channel: LiveChannel,
    /// Source windows and the publication boundary. Reload holds this lock through teardown,
    /// snapshot replacement and version advancement; a publisher holds it through publication.
    windows: std::sync::Mutex<Vec<SourceWindow>>,
    /// Set where [`Inspection::follow`] took up a new version: the next frame is sent whatever the
    /// table holds.
    followed: std::sync::atomic::AtomicBool,
    stop: std::sync::atomic::AtomicBool,
    #[cfg(test)]
    after_snapshot: std::sync::Mutex<Option<Box<dyn FnOnce() + Send>>>,
    #[cfg(test)]
    handover_blocked: std::sync::Mutex<Option<Box<dyn FnOnce() + Send>>>,
}

impl Publisher {
    fn start(probes: ProbeSlot, channel: LiveChannel) -> Self {
        let shared = std::sync::Arc::new(Published {
            probes,
            channel,
            windows: std::sync::Mutex::new(Vec::new()),
            followed: std::sync::atomic::AtomicBool::new(false),
            stop: std::sync::atomic::AtomicBool::new(false),
            #[cfg(test)]
            after_snapshot: std::sync::Mutex::new(None),
            #[cfg(test)]
            handover_blocked: std::sync::Mutex::new(None),
        });
        let publishing = shared.clone();
        let thread = thread::spawn(move || publishing.run());
        Self {
            shared,
            thread: Some(thread),
        }
    }

    fn record_windows(&self, windows: Vec<SourceWindow>) {
        *self
            .shared
            .windows
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = windows;
    }

    fn followed(&self) {
        self.shared
            .followed
            .store(true, std::sync::atomic::Ordering::Release);
    }

    /// Stop the thread and wait for it, so a frame published after this is the driver's. A
    /// publisher dropped without this, as on an error return, stops the same way.
    fn stop(self) {}
}

impl Drop for Publisher {
    fn drop(&mut self) {
        self.shared
            .stop
            .store(true, std::sync::atomic::Ordering::Release);
        if let Some(thread) = self.thread.take() {
            thread.join().expect("the publisher thread does not panic");
        }
    }
}

impl Published {
    fn run(&self) {
        use std::sync::atomic::Ordering;
        // The last published flow count; a new version forces its first frame.
        let mut published_through = Some(0);
        // Whether probing was on at the last tick. The run's poll can switch it on between two
        // ticks (`Driver::polled`), which starts a fresh table as a switch here does.
        let mut was_enabled = self.probes.is_enabled();
        while !self.stop.load(Ordering::Acquire) {
            let mut windows = self
                .windows
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if self.followed.swap(false, Ordering::AcqRel) {
                published_through = None;
            }
            let watched = self.channel.is_watched();
            if watched != self.probes.is_enabled() {
                if watched {
                    self.probes.enable();
                } else {
                    self.probes.disable();
                    self.channel.forget_frame();
                    windows.clear();
                }
            }
            let enabled = self.probes.is_enabled();
            if enabled != was_enabled && published_through.is_some() {
                published_through = Some(0);
            }
            was_enabled = enabled;
            if watched
                && let Some(table) = self.probes.snapshot()
                && Some(table.flows()) != published_through
            {
                #[cfg(test)]
                if let Some(hook) = self.after_snapshot.lock().unwrap().take() {
                    hook();
                }
                published_through = Some(table.flows());
                self.channel.publish_probes(&table, &windows);
            }
            drop(windows);
            thread::sleep(PUBLISH_INTERVAL);
        }
    }
}

/// Runs a loaded Cambra program.
///
/// Returns `Err(())` if compilation failed; the errors have already been
/// rendered to stderr by [`eprint_errors`], so the caller's job is just to exit
/// non-zero.
///
/// Runs every branch through [`LiveProgram::run`] with packages of at most `rows` rows.
fn run_program(
    loaded: &LoadedProgram,
    inspect_port: Option<u16>,
    control_port: Option<u16>,
    rows: usize,
) -> Result<(), ()> {
    let main_consumer = || -> Box<dyn Consumer> { Box::new(|| {}) };

    let mut ctx = GlobalContext::default();
    let mut live = match LiveProgram::start(&mut ctx, loaded, &main_consumer) {
        Ok(p) => p,
        Err(errs) => {
            eprint_errors(&errs, loaded.sources());
            return Err(());
        }
    };

    // Serve the panes from the same compile that is about to be driven, so a
    // click in a pane names a node the running graph actually built. A reload
    // of `main` replaces both through `Inspection::follow`: see
    // `src/inspector_model/design.md`, "A reload of main is followed".
    let mut inspection = match inspect_port {
        Some(port) => {
            let (version, program) = live
                .program(MAIN_BRANCH)
                .expect("the process starts with `main`");
            let src_name = loaded.sources().path(loaded.sources().root());
            match serve_compiled(program, src_name, port, version) {
                Ok((channel, snapshot)) => Some(Inspection::new(
                    channel,
                    snapshot,
                    src_name,
                    version,
                    ctx.subscribe_context().probes().clone(),
                    source_nodes(&program.operator_graph),
                )),
                Err(e) => {
                    eprintln!("error: serving the inspector: {e}");
                    return Err(());
                }
            }
        }
        None => None,
    };

    let control = match control_port.map(ControlPort::new).transpose() {
        Ok(control) => control,
        Err(e) => {
            eprintln!("error: could not start the control port: {e}");
            return Err(());
        }
    };

    // Control requests are serviced only at drained dispatcher boundaries.
    {
        let mut pending: Option<ControlMessage> = None;
        let publisher = inspection.as_ref().map(|inspection| {
            Publisher::start(inspection.probes.clone(), inspection.channel.clone())
        });
        loop {
            if let Some(message) = pending.take() {
                let reply = service_inspected(
                    message.request(),
                    &mut ctx,
                    &mut live,
                    &main_consumer,
                    inspection.as_mut(),
                    publisher.as_ref(),
                );
                message.answer(reply);
            }
            let mut driver = Driver {
                control: control.as_ref(),
                pending: &mut pending,
                inspection: inspection.as_ref(),
                publisher: publisher.as_ref(),
                sources: ctx.source_registry(),
            };
            let ended = live.run(rows, &print_main, &mut driver);
            match ended {
                Ok(Ended::Paused(_)) => {}
                Ok(Ended::Done(_)) if pending.is_none() && live.poll_finished() => break,
                // Nothing runs until a request changes the table.
                Ok(Ended::Done(_)) => {
                    if pending.is_none() {
                        pending = control.as_ref().and_then(ControlPort::poll);
                    }
                    if pending.is_none() {
                        thread::sleep(Duration::from_millis(10));
                    }
                }
                Err(refused) => {
                    eprintln!("error: {refused}");
                    return Err(());
                }
            }
        }
        if let Some(publisher) = publisher {
            publisher.stop();
        }
        if let Some(inspection) = inspection.as_ref() {
            inspection.publish_final(ctx.source_registry());
        }
        Ok(())
    }
}

fn tile_is_empty(tile: &Tile) -> bool {
    match tile {
        Tile::Scalar(cv) => cv.is_empty(),
        Tile::DataFunction { domain, .. } => domain.is_empty(),
        Tile::Record { fields, .. } => fields.values().all(tile_is_empty),
        _ => false,
    }
}

/// The `--inspect` side of a run: the channel frames go out on, and the probe
/// slot a connected client switches on.
///
/// Probing is all or nothing, and follows `/api/live`: every producer takes
/// readings while at least one client is connected, and none while no client
/// is. See `src/inspector_model/design.md`, "Probing follows the live route".
struct Inspection {
    channel: LiveChannel,
    /// The `/api/snapshot` body, replaced whenever `main`'s version changes.
    snapshot: ServedSnapshot,
    /// The program's name, which every payload rendered for it carries.
    name: String,
    /// The `main` version the snapshot, the anchors and the frames describe.
    following: u64,
    probes: ProbeSlot,
    /// The `IterateExtent`s over each source, which is where a click on its
    /// window resolves. Re-derived with the snapshot: every compile mints its
    /// own.
    source_node_ids: HashMap<String, Vec<NodeId>>,
}

impl Inspection {
    fn new(
        channel: LiveChannel,
        snapshot: ServedSnapshot,
        name: &str,
        following: u64,
        probes: ProbeSlot,
        source_node_ids: HashMap<String, Vec<NodeId>>,
    ) -> Self {
        Self {
            channel,
            snapshot,
            name: name.to_string(),
            following,
            probes,
            source_node_ids,
        }
    }

    /// Describe the version `main` now runs, if a reload changed it.
    ///
    /// Everything the inspector ships is named by `NodeId`, and a reload mints
    /// fresh ids for every operator it rebuilt, so the payload, the anchors and
    /// the frame stamp move together. The frame stamp moves last: a frame naming
    /// a version the server cannot yet answer `/api/snapshot` with would send a
    /// client to refetch the old one. The pass's `publish` sends a frame whether
    /// or not a flow arrived: until then the newest frame carries the old
    /// version's stamp and source anchors, and a client that connects is handed
    /// it. Another branch's reload changes nothing here, and neither does
    /// deleting `main`: the panes keep describing the last version it ran
    /// (`src/inspector_model/design.md`, "A reload of main is followed").
    ///
    /// Answers whether it took up a new version, which a [`Publisher`] sends a frame for.
    fn follow(&mut self, live: &LiveProgram) -> bool {
        let Some((version, program)) = live.program(MAIN_BRANCH) else {
            return false;
        };
        if version == self.following {
            return false;
        }
        self.snapshot.replace(program, &self.name, version);
        self.source_node_ids = source_nodes(&program.operator_graph);
        self.channel.follow(version);
        self.following = version;
        true
    }

    /// The last probe frame, marked `final`, so a reader can tell a finished
    /// run from an idle one. Published whether or not a client is connected: a
    /// client connecting later is handed it, and with probing off it carries
    /// the source windows and no readings. The process parks afterwards, so
    /// the socket stays open.
    fn publish_final(&self, sources: &SourceRegistry) {
        let sources = self.sample_sources(sources);
        let published = self
            .probes
            .with_table(|table| self.channel.publish_final_probes(table, &sources));
        if published.is_none() {
            self.channel
                .publish_final_probes(&ProbeTable::with_defaults(), &sources);
        }
    }

    /// The last [`ROWS_PER_READING`] keys of each source's retained window,
    /// read on the thread that owns the graph: the handles are `Rc`, and
    /// `retained_window`/`get` are `&self`, so sampling releases nothing.
    ///
    /// Only the tail is fetched, so a pass costs the same however much a source
    /// retains: a program accumulating every stdin line keeps its whole input.
    ///
    /// The sources's handles are the sources the program reads: a handle is
    /// registered when an `IterateExtent` over the source is subscribed. Every
    /// context registers `stdin` whether or not the program mentions it, so
    /// iterating the context's sources instead would report a window for a
    /// source that is not part of the program.
    fn sample_sources(&self, sources: &SourceRegistry) -> Vec<SourceWindow> {
        sources
            .sources()
            .filter_map(|(name, handle)| {
                let source = handle.borrow();
                let window = source.retained_window()?;
                let keys = ColumnValue::from_uints(
                    window_tail(window.clone(), ROWS_PER_READING).collect(),
                );
                let values = source.get(keys.clone());
                Some(render_source_window(
                    self.source_node_ids.get(name).cloned().unwrap_or_default(),
                    name,
                    cambra::interpreter::row_index(window.end - window.start),
                    &keys,
                    &values,
                ))
            })
            .collect()
    }
}

/// The default port for every inspector surface. `Run` and `InspectOnly` are
/// mutually exclusive, so the shared default binds one server at a time.
const DEFAULT_INSPECT_PORT: u16 = 8080;

/// The default port for the control port, which a run may bind alongside the
/// inspector's.
const DEFAULT_CONTROL_PORT: u16 = 8081;

/// What the binary does with the program it was given.
///
/// The modes are mutually exclusive by construction rather than by a check on
/// two flags that each mean something: a program is either run or it is not, and
/// `--inspect-only` is the not.
enum Mode {
    /// Run the program. With an inspect port, serve its panes and stream the
    /// values flowing through its operators; with a control port, accept the
    /// branch verbs against the running program (`src/control_port.rs`).
    Run {
        inspect_port: Option<u16>,
        control_port: Option<u16>,
    },
    /// Compile the program and serve its panes, without running it — the
    /// read-only program inspector. Answers what the program *is*, so there is
    /// no execution to attach to.
    InspectOnly { port: u16 },
    /// Print the `/api/snapshot` payload for the program and exit. The one-shot
    /// form of `InspectOnly`, for the golden-fixture corpus (whose server would
    /// never exit).
    DumpSnapshot,
}

/// Runs a given Cambra file, specified as the first command-line argument.
fn main() {
    env_logger::init();
    let args: Vec<String> = std::env::args().collect();

    // The language server speaks on stdout, so it runs before anything else
    // could print there.
    if args.get(1).is_some_and(|arg| arg == "--lsp") {
        if args.len() > 2 {
            eprintln!("error: --lsp takes no other arguments");
            std::process::exit(1);
        }
        let status = match cambra_lsp::run_stdio() {
            Ok(cambra_lsp::Ended::Shutdown) => 0,
            Ok(cambra_lsp::Ended::WithoutShutdown) => 1,
            Err(e) => {
                eprintln!("error: cambra --lsp: {e}");
                1
            }
        };
        std::process::exit(status);
    }
    // `cambra check <file>` checks the file on its own and prints its interface
    // (`docs/chl-spec.md`, "9.14 Checking a module on its own").
    if args.get(1).map(String::as_str) == Some("check") {
        let [_, _, file] = args.as_slice() else {
            eprintln!("Usage: cambra check <input_file>");
            std::process::exit(1);
        };
        let loaded = LoadedProgram::read(Path::new(file)).unwrap_or_else(|e| {
            eprintln!("error: {e}");
            std::process::exit(1);
        });
        match cambra::ccl::context::check_program(&mut GlobalContext::default(), &loaded) {
            Ok(interface) => print!("{interface}"),
            Err(errors) => {
                eprint_errors(&errors, loaded.sources());
                std::process::exit(1);
            }
        }
        return;
    }

    let mut input_file = None;
    let mut inspect_port: Option<u16> = None;
    let mut control_port: Option<u16> = None;
    let mut inspect_only_port: Option<u16> = None;
    let mut dump_snapshot = false;

    for arg in &args[1..] {
        if arg == "--inspect" {
            inspect_port = Some(DEFAULT_INSPECT_PORT);
        } else if let Some(port_str) = arg.strip_prefix("--inspect=") {
            inspect_port = Some(port_str.parse().expect("Invalid port for --inspect"));
        } else if arg == "--control" {
            control_port = Some(DEFAULT_CONTROL_PORT);
        } else if let Some(port_str) = arg.strip_prefix("--control=") {
            control_port = Some(port_str.parse().expect("Invalid port for --control"));
        } else if arg == "--inspect-only" {
            inspect_only_port = Some(DEFAULT_INSPECT_PORT);
        } else if let Some(port_str) = arg.strip_prefix("--inspect-only=") {
            inspect_only_port = Some(port_str.parse().expect("Invalid port for --inspect-only"));
        } else if arg == "--dump-snapshot" {
            dump_snapshot = true;
        } else {
            input_file = Some(arg.clone());
        }
    }

    let usage = "Usage: cambra [[--inspect[=PORT]] [--control[=PORT]] \
| --inspect-only[=PORT] | --dump-snapshot] <input_file>\n       cambra check <input_file>\n       cambra --lsp";
    let mode = match (inspect_port, control_port, inspect_only_port, dump_snapshot) {
        (None, None, Some(port), false) => Mode::InspectOnly { port },
        (None, None, None, true) => Mode::DumpSnapshot,
        (inspect_port, control_port, None, false) => Mode::Run {
            inspect_port,
            control_port,
        },
        _ => {
            eprintln!(
                "error: --inspect-only and --dump-snapshot are exclusive with each other \
                 and with the flags that run a program"
            );
            eprintln!("{usage}");
            std::process::exit(1);
        }
    };

    let input_file = input_file.unwrap_or_else(|| {
        eprintln!("{usage}");
        std::process::exit(1);
    });

    let loaded = LoadedProgram::read(Path::new(&input_file)).unwrap_or_else(|e| {
        eprintln!("error: {e}");
        std::process::exit(1);
    });

    match mode {
        Mode::DumpSnapshot => {
            println!(
                "{}",
                cambra::inspector_server::snapshot_body_pretty(&loaded)
            );
        }
        Mode::InspectOnly { port } => {
            if let Err(e) = cambra::inspector_server::serve(&loaded, port) {
                eprintln!("error: serving the inspector: {e}");
                std::process::exit(1);
            }
        }
        Mode::Run {
            inspect_port,
            control_port,
        } => {
            let served = inspect_port.is_some() || control_port.is_some();
            let result = if served {
                run_program(&loaded, inspect_port, control_port, morsel_rows())
            } else {
                run_dispatched(&loaded)
            };
            if result.is_err() {
                std::process::exit(1);
            }

            if let Some(port) = inspect_port {
                eprintln!(
                    "Program finished. Inspector at http://localhost:{port} — press Ctrl+C to exit."
                );
                loop {
                    std::thread::park();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::run_program;
    use cambra::ccl::load::LoadedProgram;
    use test_log::test;

    #[test]
    fn a_reload_waits_for_an_in_flight_probe_snapshot() {
        use super::*;
        use cambra::inspector_server::live::LiveServer;
        use std::sync::{
            Arc, Mutex,
            atomic::{AtomicBool, Ordering},
            mpsc,
        };
        use tungstenite::Message;

        let mut ctx = GlobalContext::default();
        let probes = ctx.subscribe_context().probes().clone();
        probes.enable();
        let loaded = LoadedProgram::test("42");
        let consumer = || -> Box<dyn Consumer> { Box::new(|| {}) };
        let mut program = LiveProgram::start(&mut ctx, &loaded, &consumer).unwrap();
        let producer = program.main_producer_mut(MAIN_BRANCH).unwrap();
        producer.get(producer.tiling().universal_guard());
        let live = Arc::new(LiveServer::start());
        let channel = live.channel();
        channel.follow(1);
        let (_, compiled) = program.program(MAIN_BRANCH).unwrap();
        let (_, served) = serve_compiled(compiled, "test", 0, 1).unwrap();
        let mut inspection = Inspection::new(
            channel.clone(),
            served,
            "test",
            1,
            probes.clone(),
            source_nodes(&compiled.operator_graph),
        );
        let server = tiny_http::Server::http("127.0.0.1:0").unwrap();
        let port = server.server_addr().to_ip().unwrap().port();
        let serving = live.clone();
        let server_thread = thread::spawn(move || serving.accept(server.recv().unwrap()).unwrap());
        let stream = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        let (mut socket, _) =
            tungstenite::client::client(format!("ws://127.0.0.1:{port}/api/live"), stream).unwrap();
        // A previous source's anchors and window must not survive a scalar replacement.
        inspection
            .source_node_ids
            .insert("retired-source".into(), Vec::new());
        let stale_window = SourceWindow {
            node_ids: Vec::new(),
            name: "retired-source".into(),
            rows: Vec::new(),
            total: 1,
        };
        let (copied, snapshot) = mpsc::sync_channel(0);
        let (resume, proceed) = mpsc::sync_channel(0);
        let (contended, contention) = mpsc::sync_channel(0);
        let published = Arc::new(Published {
            probes: probes.clone(),
            channel: channel.clone(),
            windows: Mutex::new(vec![stale_window]),
            followed: AtomicBool::new(false),
            stop: AtomicBool::new(false),
            after_snapshot: Mutex::new(Some(Box::new(move || {
                copied.send(()).unwrap();
                proceed.recv_timeout(Duration::from_secs(5)).unwrap();
            }))),
            handover_blocked: Mutex::new(Some(Box::new(move || {
                contended.send(()).unwrap();
            }))),
        });
        let worker = published.clone();
        let publishing = thread::spawn(move || worker.run());
        snapshot.recv_timeout(Duration::from_secs(5)).unwrap();
        let publisher = Publisher {
            shared: published.clone(),
            thread: Some(publishing),
        };
        published.stop.store(true, Ordering::Release);
        let resume_publication = thread::spawn(move || {
            contention.recv_timeout(Duration::from_secs(5)).unwrap();
            resume.send(()).unwrap();
        });
        let reply = service_inspected(
            &ControlRequest::Reload {
                branch: MAIN_BRANCH.into(),
                code: "43".into(),
            },
            &mut ctx,
            &mut program,
            &consumer,
            Some(&mut inspection),
            Some(&publisher),
        );
        assert_eq!(reply.status, 200, "{}", reply.body);
        resume_publication.join().unwrap();
        publisher.stop();
        assert_eq!(inspection.following, 2);
        let (_, compiled) = program.program(MAIN_BRANCH).unwrap();
        assert_eq!(
            inspection.source_node_ids,
            source_nodes(&compiled.operator_graph)
        );
        assert_eq!(
            *published.windows.lock().unwrap(),
            inspection.sample_sources(ctx.source_registry())
        );
        let Message::Text(text) = socket.read().unwrap() else {
            panic!("probe frame")
        };
        let frame: serde_json::Value = serde_json::from_str(&text).unwrap();
        assert_eq!(frame["version"], 1);
        assert!(!frame["nodes"].as_array().unwrap().is_empty());
        {
            let windows = published.windows.lock().unwrap();
            channel.publish_probes(&probes.snapshot().unwrap(), &windows);
        }
        let Message::Text(text) = socket.read().unwrap() else {
            panic!("probe frame")
        };
        let frame: serde_json::Value = serde_json::from_str(&text).unwrap();
        assert_eq!(frame["version"], 2);
        assert!(frame["nodes"].as_array().unwrap().is_empty());
        drop(socket);
        server_thread.join().unwrap();
    }

    #[test]
    fn test_run_program() {
        run_program(&LoadedProgram::test("x = 1; x"), None, None, 1).unwrap();
    }
}

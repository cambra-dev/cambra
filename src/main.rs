use std::{collections::HashMap, ops::ControlFlow, path::Path, thread, time::Duration};

use cambra::{
    ccl::{
        context::{CompiledProgram, GlobalContext, compile_program, eprint_errors},
        load::LoadedProgram,
        provenance::NodeId,
    },
    control_port::{ControlMessage, ControlPort, service},
    inspector_server::{ServedSnapshot, live::LiveChannel, serve_compiled},
    interpreter::{
        ColumnValue, Consumer, DataSink, Scheduler,
        dispatcher::{self, Ended, RunObserver},
        operator_graph::source_nodes,
        tile_operators::{FunctionGuard, Tile, TileGuard, TileProducer},
        value_probe::{
            ProbeSlot, ProbeTable, ROWS_PER_READING, SourceWindow, render_source_window,
            window_tail,
        },
    },
    live_program::{LiveProgram, MAIN_BRANCH},
};
use log::debug;

/// Service at most one pending control request.
///
/// One request per call rather than draining the queue: an accepted `/reload`
/// replaces a branch's version, so the requests behind it would be answered
/// against a version that no longer exists.
fn poll_control(
    control: Option<&ControlPort>,
    ctx: &mut GlobalContext,
    live: &mut LiveProgram,
    main_consumer: &dyn Fn() -> Box<dyn Consumer>,
) {
    let Some(port) = control else { return };
    let Some(message) = port.poll() else { return };
    let reply = service(message.request(), ctx, live, main_consumer);
    message.answer(reply);
}

/// Pull one branch's `main` output once, print what it delivered, and answer
/// whether it has now finished.
///
/// `main`'s value prints as `Got value: …` and every other
/// branch's as `Got value from <branch>: …`
/// (`src/ccl/design/program-evolution.md`, "A reload changes no other branch").
fn pull_main(branch: &str, producer: &mut dyn TileProducer) -> bool {
    debug!("Main calling get on {branch}");
    let tile = producer.get(producer.tiling().universal_guard());

    let release_guard = release_guard_for(&tile);
    debug!("Main releasing with {release_guard:?}");
    let done = release_guard.is_universal();
    producer.release(release_guard);
    // Producers can return empty tiles, but still have more data.
    if !tile_is_empty(&tile) || done {
        if branch == MAIN_BRANCH {
            println!("Got value: {tile:#?}");
        } else {
            println!("Got value from {branch}: {tile:#?}");
        }
    }
    done
}

/// The variable that runs a program through the dispatcher where it is set and not `0`
/// ([`run_dispatched`]).
const DISPATCH_VAR: &str = "CAMBRA_DISPATCH";

/// The variable that sets the most rows a dispatched run's work package names.
const MORSEL_ROWS_VAR: &str = "CAMBRA_MORSEL_ROWS";

/// The most rows a dispatched run's work package names where [`MORSEL_ROWS_VAR`] is unset.
const DEFAULT_MORSEL_ROWS: usize = 1024;

/// Whether [`DISPATCH_VAR`] asks for a dispatched run.
fn dispatch_requested() -> bool {
    std::env::var(DISPATCH_VAR).is_ok_and(|value| !value.is_empty() && value != "0")
}

/// Runs `loaded` through the dispatcher on the calling thread ([`dispatcher::run_program_into`]),
/// printing each answer of the `main` output ([`PrintedMain`]), as pull mode prints each pull's
/// answer. A program the planner refuses runs in pull mode in the same context, after a
/// note on stderr: its compile has opened its sources and sinks, a port bound or stdin taken, so a
/// second compile could open none of them. `Err(())` where it does not compile.
///
/// # Panics
///
/// Where [`MORSEL_ROWS_VAR`] is set to anything but a positive count.
fn run_dispatched(loaded: &LoadedProgram) -> Result<(), ()> {
    let rows = morsel_rows();
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
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
        eprintln!("note: {DISPATCH_VAR}: {refused}; running in pull mode");
        run_in_pull_mode(&mut ctx, &mut program);
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

/// The `main` output of a dispatched run, which prints each answer it is handed as
/// [`pull_main`] prints a pull's: one that holds a key or a value, or that is terminal.
struct PrintedMain;

impl DataSink for PrintedMain {
    fn process(&self, tile: &Tile) {
        if !tile_is_empty(tile) || tile.is_terminal() {
            println!("Got value: {tile:#?}");
        }
    }
}

/// [`PrintedMain`] for a branch other than `main`, printing `Got value from <branch>: …` as
/// [`pull_main`] does.
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
    scheduler: &'a Scheduler,
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
            publisher.record_windows(inspection.sample_sources(self.scheduler));
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
    /// The source windows the run sampled at its last poll with probing on.
    windows: std::sync::Mutex<Vec<SourceWindow>>,
    /// Set where [`Inspection::follow`] took up a new version: the next frame is sent whatever the
    /// table holds.
    followed: std::sync::atomic::AtomicBool,
    stop: std::sync::atomic::AtomicBool,
}

impl Publisher {
    fn start(probes: ProbeSlot, channel: LiveChannel) -> Self {
        let shared = std::sync::Arc::new(Published {
            probes,
            channel,
            windows: std::sync::Mutex::new(Vec::new()),
            followed: std::sync::atomic::AtomicBool::new(false),
            stop: std::sync::atomic::AtomicBool::new(false),
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
        // `ProbeTable::flows` at the last frame, as `Inspection::published_through` keeps it for
        // pull mode: `None` from a follow until the next frame, `Some(0)` again at each switch.
        let mut published_through = Some(0);
        // Whether probing was on at the last tick. The run's poll can switch it on between two
        // ticks (`Driver::polled`), which starts a fresh table as a switch here does.
        let mut was_enabled = self.probes.is_enabled();
        while !self.stop.load(Ordering::Acquire) {
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
                    self.windows
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .clear();
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
                published_through = Some(table.flows());
                let windows = self
                    .windows
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .clone();
                self.channel.publish_probes(&table, &windows);
            }
            thread::sleep(PUBLISH_INTERVAL);
        }
    }
}

/// Drive `program`, compiled in `ctx` with its sinks unpulled, in pull mode: pull each sink once,
/// as the compile would have, then deliver what the sources bring and pull the `main` output
/// until it is released whole and every sink is done. A sink program that serves requests never
/// finishes, as under [`run_program`].
fn run_in_pull_mode(ctx: &mut GlobalContext, program: &mut CompiledProgram) {
    let sinks: Vec<_> = program
        .outputs
        .iter()
        .filter_map(|output| output.sink_consumer.clone())
        .collect();
    for sink in &sinks {
        sink.borrow().pull_now();
    }
    let mut main = program
        .outputs
        .iter_mut()
        .find(|output| output.is_main())
        .and_then(|output| output.producer.take());
    let mut main_done = main.is_none();
    // A program with no sink drops its done sender, so it never signals.
    let mut sinks_done = sinks.is_empty();
    loop {
        let delivery = ctx.scheduler().poll_sources();
        let delivered = ctx.scheduler().deliver(delivery);
        if let Some(producer) = main.as_mut()
            && !main_done
        {
            main_done = pull_main(MAIN_BRANCH, &mut **producer);
        }
        sinks_done |= program.done.try_recv().is_ok();
        if main_done && sinks_done {
            return;
        }
        if !delivered {
            thread::sleep(Duration::from_millis(10));
        }
    }
}

/// Runs a loaded Cambra program.
///
/// Returns `Err(())` if compilation failed; the errors have already been
/// rendered to stderr by [`eprint_errors`], so the caller's job is just to exit
/// non-zero.
///
/// `dispatch` runs every branch through the dispatcher with work packages of at most that many
/// rows ([`LiveProgram::run`]), servicing each control request between two runs; `None` runs in
/// pull mode.
fn run_program(
    loaded: &LoadedProgram,
    inspect_port: Option<u16>,
    control_port: Option<u16>,
    dispatch: Option<usize>,
) -> Result<(), ()> {
    // Each branch's `main` consumer marks that branch as having something to
    // pull ([`LiveProgram::pull_mains`]); the driver polls those marks, so the
    // wake itself carries nothing.
    let main_consumer = || -> Box<dyn Consumer> {
        Box::new(|| {
            debug!("Main loop received notification");
        })
    };

    let mut ctx = GlobalContext::default();
    if dispatch.is_some() {
        ctx.defer_sink_pulls();
    }
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
                    ctx.scheduler().probes().clone(),
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

    // Pull every branch's `main` output until each has released everything,
    // and keep the scheduler running until every branch's sinks signal
    // completion. Long-lived servers (e.g. `http_serve`) never signal, so for
    // them this loop runs until the process exits. The control port is serviced
    // once per pass: a swap sits between two pulls, so a source delivering
    // without pause must not be able to starve it of its turn.
    if let Some(rows) = dispatch {
        let mut pending: Option<ControlMessage> = None;
        // Whether a run has started. A refusal of the first run ran nothing, so the process falls
        // back to pull mode; a later run starts over breakers that consumed, which pull mode cannot
        // drive.
        let mut ran = false;
        let publisher = inspection.as_ref().map(|inspection| {
            Publisher::start(inspection.probes.clone(), inspection.channel.clone())
        });
        loop {
            if let Some(message) = pending.take() {
                let reply = service(message.request(), &mut ctx, &mut live, &main_consumer);
                message.answer(reply);
            }
            if let Some(inspection) = inspection.as_mut()
                && inspection.follow(&live)
                && let Some(publisher) = publisher.as_ref()
            {
                publisher.followed();
            }
            let mut driver = Driver {
                control: control.as_ref(),
                pending: &mut pending,
                inspection: inspection.as_ref(),
                publisher: publisher.as_ref(),
                scheduler: ctx.scheduler(),
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
                Err(refused) if !ran => {
                    eprintln!("note: {DISPATCH_VAR}: {refused}; running in pull mode");
                    // Pull mode switches probing itself before each pull, from a slot the
                    // publisher may have filled.
                    if let Some(inspection) = inspection.as_ref() {
                        inspection.probes.disable();
                    }
                    ctx.resume_sink_pulls();
                    live.pull_sinks();
                    break;
                }
                Err(refused) => {
                    eprintln!("error: {DISPATCH_VAR}: {refused}, after a run has consumed");
                    return Err(());
                }
            }
            ran = true;
        }
        if let Some(publisher) = publisher {
            publisher.stop();
        }
        if ran {
            if let Some(inspection) = inspection.as_ref() {
                inspection.publish_final(ctx.scheduler());
            }
            return Ok(());
        }
        if let Some(message) = pending.take() {
            let reply = service(message.request(), &mut ctx, &mut live, &main_consumer);
            message.answer(reply);
        }
    }

    loop {
        poll_control(control.as_ref(), &mut ctx, &mut live, &main_consumer);
        if let Some(inspection) = inspection.as_mut() {
            inspection.follow(&live);
        }
        // Sampled between the poll and the delivery. The poll takes this pass's
        // arrivals into the source buffers; the delivery is where a sink pulls
        // them, and both the delivery and a `main` pull are where a `Memo`
        // releases its input from inside `get_impl`. A window read before the
        // poll misses the arrivals, and one read after the delivery or the pull
        // reports what the pass consumed.
        //
        // The poll also has to come before `before_pull`'s `is_watched` check.
        // `LiveServer::accept` counts a client as watching before replying to its
        // handshake, so any input the client sends is taken in by a poll that
        // precedes a check already seeing the count, and is recorded.
        let delivery = ctx.scheduler().poll_sources();
        let sources = match inspection.as_mut() {
            Some(inspection) => inspection.before_pull(ctx.scheduler()),
            None => Vec::new(),
        };
        let delivered = ctx.scheduler().deliver(delivery);
        live.pull_mains(pull_main);
        if let Some(inspection) = inspection.as_mut() {
            inspection.publish(&sources);
        }
        if live.poll_finished() {
            break;
        }
        // A `main` output is pulled as soon as it is notified, so while one is
        // running the loop spins; a sink program is woken by its sources. A pass that
        // delivered something may have queued more, since a sink pulls once per pass, so
        // the next pass runs at once.
        if !delivered && !live.any_main_running() {
            // TODO we shouldn't need to sleep here; we should come up with a better interface
            // for check_for_notifications
            thread::sleep(Duration::from_millis(10));
        }
    }

    if let Some(inspection) = inspection.as_ref() {
        inspection.publish_final(ctx.scheduler());
    }
    Ok(())
}

/// What the driver has taken delivery of in `tile`, to release back.
///
/// A product value's fields are tiled independently, so the guard is built per field
/// rather than from the record as a whole.
fn release_guard_for(tile: &Tile) -> TileGuard {
    match tile {
        Tile::Scalar(cv) => TileGuard::Scalar(TileGuard::leaf(!cv.is_empty())),
        Tile::DataFunction {
            domain_predicate, ..
        } => TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
        Tile::Record { fields, .. } => TileGuard::Record(
            fields
                .iter()
                .map(|(k, t)| (k.clone(), release_guard_for(t)))
                .collect(),
        ),
        other => panic!("Unexpected top-level tile shape: {other:?}"),
    }
}

/// Whether `tile` carries nothing yet. A producer may answer empty and still
/// have more to deliver, which is what separates this from being done.
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
    /// [`ProbeTable::flows`] at the last publish. Zero again whenever probing
    /// switches, because each switch starts a fresh table or none. `None` from
    /// [`follow`](Self::follow) taking up a new version until the next
    /// [`publish`](Self::publish) with probing on, which sends a frame whatever
    /// `flows` reads; a switch keeps it `None`.
    published_through: Option<u64>,
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
            published_through: Some(0),
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
        self.published_through = None;
        true
    }

    /// Switch probing to match whether a client is connected, and sample the
    /// source windows while probing is on.
    ///
    /// Called before each pull, so a switch never lands inside a `get`.
    fn before_pull(&mut self, scheduler: &Scheduler) -> Vec<SourceWindow> {
        let watched = self.channel.is_watched();
        if watched != self.probes.is_enabled() {
            if watched {
                self.probes.enable();
            } else {
                self.probes.disable();
                self.channel.forget_frame();
            }
            if self.published_through.is_some() {
                self.published_through = Some(0);
            }
        }
        if !watched {
            return Vec::new();
        }
        self.sample_sources(scheduler)
    }

    /// Publish a frame if some probe took a reading that carried rows since the
    /// last publish, or if `main`'s version changed since it.
    ///
    /// The driver polls on a 10ms timer, and a poll that delivers nothing
    /// still takes an empty reading from every producer it pulls. Gating on
    /// every reading would broadcast an unchanged frame a hundred times a
    /// second, each paired with a window sampled on a pass that carried
    /// nothing.
    fn publish(&mut self, sources: &[SourceWindow]) {
        let flows = self.probes.with_table(ProbeTable::flows);
        let Some(flows) = flows.filter(|&flows| Some(flows) != self.published_through) else {
            return;
        };
        self.published_through = Some(flows);
        self.probes
            .with_table(|table| self.channel.publish_probes(table, sources));
    }

    /// The last probe frame, marked `final`, so a reader can tell a finished
    /// run from an idle one. Published whether or not a client is connected: a
    /// client connecting later is handed it, and with probing off it carries
    /// the source windows and no readings. The process parks afterwards, so
    /// the socket stays open.
    fn publish_final(&self, scheduler: &Scheduler) {
        let sources = self.sample_sources(scheduler);
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
    /// The scheduler's handles are the sources the program reads: a handle is
    /// registered when an `IterateExtent` over the source is subscribed. Every
    /// context registers `stdin` whether or not the program mentions it, so
    /// iterating the context's sources instead would report a window for a
    /// source that is not part of the program.
    fn sample_sources(&self, scheduler: &Scheduler) -> Vec<SourceWindow> {
        scheduler
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
            let result = match (dispatch_requested(), served) {
                (true, false) => run_dispatched(&loaded),
                (true, true) => {
                    run_program(&loaded, inspect_port, control_port, Some(morsel_rows()))
                }
                (false, _) => run_program(&loaded, inspect_port, control_port, None),
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
    fn test_run_program() {
        run_program(&LoadedProgram::test("x = 1; x"), None, None, None).unwrap();
    }
}

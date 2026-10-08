use std::{collections::HashMap, thread, time::Duration};

use cambra::{
    ccl::{
        context::{GlobalContext, eprint_errors},
        provenance::NodeId,
    },
    control_port::{ControlPort, service},
    inspector_server::{ServedSnapshot, live::LiveChannel, serve_compiled},
    interpreter::{
        ColumnValue, Consumer, Scheduler,
        operator_graph::source_nodes,
        tile_operators::{FunctionGuard, Tile, TileGuard, TileProducer},
        value_probe::{
            ProbeSlot, ProbeTable, ROWS_PER_READING, SourceWindow, render_source_window,
            window_tail,
        },
    },
    live_program::{DEFAULT_BRANCH, LiveProgram},
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
/// The default branch's value prints as `Got value: …` and every other
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
        if branch == DEFAULT_BRANCH {
            println!("Got value: {tile:#?}");
        } else {
            println!("Got value from {branch}: {tile:#?}");
        }
    }
    done
}

/// Runs a Cambra program from a source string.
///
/// `src_name` is the label shown in error reports (typically the input
/// file name). Returns `Err(())` if compilation failed; the errors have
/// already been rendered to stderr by [`eprint_errors`], so the caller's
/// job is just to exit non-zero.
fn run_program(
    src_name: &str,
    code: &str,
    inspect_port: Option<u16>,
    control_port: Option<u16>,
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
    let mut live = match LiveProgram::start(&mut ctx, code, &main_consumer) {
        Ok(p) => p,
        Err(errs) => {
            eprint_errors(&errs, src_name, code);
            return Err(());
        }
    };

    // Serve the panes from the same compile that is about to be driven, so a
    // click in a pane names a node the running graph actually built. A reload
    // of `main` replaces both through `Inspection::follow`: see
    // `src/inspector_model/design.md`, "A reload of main is followed".
    let mut inspection = match inspect_port {
        Some(port) => {
            let program = live.program().expect("the process starts with `main`");
            let version = live.version().expect("the process starts with `main`");
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
        let delivery = ctx.scheduler().poll_sources();
        let sources = match inspection.as_mut() {
            Some(inspection) => inspection.before_pull(ctx.scheduler()),
            None => Vec::new(),
        };
        ctx.scheduler().deliver(delivery);
        live.pull_mains(pull_main);
        if let Some(inspection) = inspection.as_mut() {
            inspection.publish(&sources);
        }
        if live.finished() {
            break;
        }
        // A `main` output is pulled as soon as it is notified, so while one is
        // running the loop spins; a sink program is woken by its sources.
        if !live.any_main_running() {
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
    /// switches, because each switch starts a fresh table or none.
    published_through: u64,
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
            published_through: 0,
        }
    }

    /// Describe the version `main` now runs, if a reload changed it.
    ///
    /// Everything the inspector ships is named by `NodeId`, and a reload mints
    /// fresh ids for every operator it rebuilt, so the payload, the anchors and
    /// the frame stamp move together. The frame stamp moves last: a frame naming
    /// a version the server cannot yet answer `/api/snapshot` with would send a
    /// client to refetch the old one. Another branch's reload changes nothing
    /// here, and neither does deleting `main`: the panes keep describing the last
    /// version it ran (`src/inspector_model/design.md`, "A reload of main is
    /// followed").
    fn follow(&mut self, live: &LiveProgram) {
        let (Some(version), Some(program)) = (live.version(), live.program()) else {
            return;
        };
        if version == self.following {
            return;
        }
        self.snapshot.replace(program, &self.name, version);
        self.source_node_ids = source_nodes(&program.operator_graph);
        self.channel.follow(version);
        self.following = version;
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
            self.published_through = 0;
        }
        if !watched {
            return Vec::new();
        }
        self.sample_sources(scheduler)
    }

    /// Publish a frame if some probe took a reading that carried rows since the
    /// last publish.
    ///
    /// The driver polls on a 10ms timer, and a poll that delivers nothing
    /// still takes an empty reading from every producer it pulls. Gating on
    /// every reading would broadcast an unchanged frame a hundred times a
    /// second, each paired with a window sampled on a pass that carried
    /// nothing.
    fn publish(&mut self, sources: &[SourceWindow]) {
        let flows = self.probes.with_table(ProbeTable::flows);
        let Some(flows) = flows.filter(|&flows| flows != self.published_through) else {
            return;
        };
        self.published_through = flows;
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
                    window.len(),
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
| --inspect-only[=PORT] | --dump-snapshot] <input_file>";
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

    let code = std::fs::read_to_string(&input_file).expect("Failed to read input file");

    match mode {
        Mode::DumpSnapshot => {
            println!(
                "{}",
                cambra::inspector_server::snapshot_body_pretty(&code, &input_file)
            );
        }
        Mode::InspectOnly { port } => {
            if let Err(e) = cambra::inspector_server::serve(&code, &input_file, port) {
                eprintln!("error: serving the inspector: {e}");
                std::process::exit(1);
            }
        }
        Mode::Run {
            inspect_port,
            control_port,
        } => {
            if run_program(&input_file, &code, inspect_port, control_port).is_err() {
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
    use test_log::test;

    #[test]
    fn test_run_program() {
        run_program("<test>", "x = 1; x", None, None).unwrap();
    }
}

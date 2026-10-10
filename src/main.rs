use std::{cell::RefCell, collections::HashMap, rc::Rc, thread, time::Duration};

use cambra::{
    ccl::{
        context::{GlobalContext, ReuseTally, eprint_errors},
        provenance::NodeId,
    },
    chl_parser::SourceMap,
    control_port::{ControlPort, ControlReply, ControlRequest},
    inspector_server::{live::LiveChannel, serve_compiled},
    interpreter::{
        ColumnValue, Consumer, Scheduler,
        operator_graph::source_nodes,
        tile_operators::{FunctionGuard, Tile, TileGuard},
        value_probe::{
            ProbeSlot, ProbeTable, ROWS_PER_READING, SourceWindow, render_source_window,
            window_tail,
        },
    },
    live_program::{LiveProgram, render_unreadable},
};
use log::debug;

/// Service at most one pending control request.
///
/// One request per call rather than draining the queue: an accepted `/reload`
/// replaces the program, so the requests behind it would be answered against a
/// version that no longer exists.
fn poll_control(
    control: Option<&ControlPort>,
    ctx: &mut GlobalContext,
    live: &mut LiveProgram,
    main_consumer: &dyn Fn() -> Box<dyn Consumer>,
    new_data: &Rc<RefCell<bool>>,
) {
    let Some(port) = control else { return };
    let Some(message) = port.poll() else { return };
    // The posted text arrived over the control port and need not match any file
    // on disk, so its diagnostics label it `<new>` rather than a path.
    const POSTED: &str = "<new>";
    let reply = match message.request() {
        ControlRequest::Diff { code, phase } => {
            let sources = SourceMap::single(POSTED, code.as_str());
            match live.diff_against(ctx, &sources, *phase) {
                Ok(report) => ControlReply::ok(format!(
                    "{}{}",
                    report.diff,
                    render_unreadable(&report.unreadable)
                )),
                Err(e) => ControlReply::rejected(e.render(&sources)),
            }
        }
        ControlRequest::Reload { code } => {
            let sources = SourceMap::single(POSTED, code.as_str());
            // A rebuilt operator's producer takes the scheduler's probe slot
            // when it is built, as the first compile's did.
            match live.reload(ctx, &sources, main_consumer) {
                Ok(report) => {
                    // The new graph has subscribed but nothing has pulled it, so arm
                    // the driver for one pass.
                    *new_data.borrow_mut() = true;
                    let ReuseTally { kept, bound } = report.reuse;
                    ControlReply::ok(format!(
                        "reloaded: {kept}/{bound} operators kept\n\n{}{}",
                        report.diff,
                        render_unreadable(&report.unreadable),
                    ))
                }
                Err(e) => ControlReply::rejected(e.render(&sources)),
            }
        }
    };
    message.answer(reply);
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
    let new_data = Rc::new(RefCell::new(false));
    let flag = new_data.clone();
    let main_consumer = move || -> Box<dyn Consumer> {
        let flag = flag.clone();
        Box::new(move || {
            debug!("Main loop received notification");
            *flag.borrow_mut() = true;
        })
    };

    let mut ctx = GlobalContext::default();
    let sources = SourceMap::single(src_name, code);
    let mut live = match LiveProgram::start(&mut ctx, &sources, &main_consumer) {
        Ok(p) => p,
        Err(errs) => {
            eprint_errors(&errs, &sources);
            return Err(());
        }
    };

    // Serve the panes from the same compile that is about to be driven, so a
    // click in a pane names a node the running graph actually built. A reload
    // replaces neither the panes nor `source_node_ids` below: see
    // `src/inspector_model/design.md`, "A reload is not followed".
    let mut inspection = match inspect_port {
        Some(port) => match serve_compiled(live.program(), src_name, port) {
            Ok(channel) => Some(Inspection::new(
                channel,
                ctx.scheduler().probes().clone(),
                source_nodes(&live.program().operator_graph),
            )),
            Err(e) => {
                eprintln!("error: serving the inspector: {e}");
                return Err(());
            }
        },
        None => None,
    };

    let control = match control_port.map(ControlPort::new).transpose() {
        Ok(control) => control,
        Err(e) => {
            eprintln!("error: could not start the control port: {e}");
            return Err(());
        }
    };

    // Drive the `main` output (if any) until it signals a universal release.
    // For sink-only programs this loop is skipped entirely.
    while live.has_main() {
        // Serviced once per pull and then for as long as the program waits. A
        // swap sits between two pulls, so a source delivering without pause must
        // not be able to starve the control port of its turn.
        loop {
            poll_control(
                control.as_ref(),
                &mut ctx,
                &mut live,
                &main_consumer,
                &new_data,
            );
            if *new_data.borrow() {
                break;
            }
            ctx.scheduler().check_for_notifications();
        }
        *new_data.borrow_mut() = false;

        // Re-read the producer each pass: a reload between pulls replaces it.
        let Some(producer) = live.main_producer_mut() else {
            break;
        };
        debug!("Main calling get");
        // Sampled before the pull, not after. A `Memo` releases its input from
        // inside `get_impl`, so the release cascade reaches the source buffer
        // partway through the driver's own `get` — sampling afterwards reads a
        // buffer the pull already drained. Before it, the pass's arrivals are
        // present and nothing has taken delivery.
        let sources = match inspection.as_mut() {
            Some(inspection) => inspection.before_pull(ctx.scheduler()),
            None => Vec::new(),
        };
        let tile = producer.get(producer.tiling().universal_guard());
        if let Some(inspection) = inspection.as_mut() {
            inspection.publish(&sources);
        }

        let release_guard = release_guard_for(&tile);
        debug!("Main releasing with {release_guard:?}");
        let done = release_guard.is_universal();
        producer.release(release_guard);
        // Producers can return empty tiles, but still have more data.
        let is_empty = tile_is_empty(&tile);
        if !is_empty || done {
            println!("Got value: {tile:#?}");
        }
        if done {
            break;
        }
    }

    // If there are sinks, keep the scheduler running until they all signal
    // completion.  Long-lived servers (e.g. http_serve) never signal, so this
    // loop runs until the process exits.
    if live.program().sinks().next().is_some() {
        loop {
            // Sampled between the poll and the delivery. The poll takes this
            // pass's arrivals into the source buffers; the delivery is where a
            // sink pulls them and a `Memo` releases its input from inside
            // `get_impl`. A window read before the poll misses the arrivals,
            // and one read after the delivery reports what the pass consumed.
            let delivery = ctx.scheduler().poll_sources();
            let sources = match inspection.as_mut() {
                Some(inspection) => inspection.before_pull(ctx.scheduler()),
                None => Vec::new(),
            };
            ctx.scheduler().deliver(delivery);
            if let Some(inspection) = inspection.as_mut() {
                inspection.publish(&sources);
            }
            poll_control(
                control.as_ref(),
                &mut ctx,
                &mut live,
                &main_consumer,
                &new_data,
            );
            if live.done().try_recv().is_ok() {
                break;
            }
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
    probes: ProbeSlot,
    /// The `IterateExtent`s over each source, which is where a click on its
    /// window resolves. A reload does not update these: see
    /// `src/inspector_model/design.md`, "A reload is not followed".
    source_node_ids: HashMap<String, Vec<NodeId>>,
    /// [`ProbeTable::flows`] at the last publish. Zero again whenever probing
    /// switches, because each switch starts a fresh table or none.
    published_through: u64,
}

impl Inspection {
    fn new(
        channel: LiveChannel,
        probes: ProbeSlot,
        source_node_ids: HashMap<String, Vec<NodeId>>,
    ) -> Self {
        Self {
            channel,
            probes,
            source_node_ids,
            published_through: 0,
        }
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
    /// The sink loop polls on a 10ms timer, and a poll that delivers nothing
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
    /// values flowing through its operators; with a control port, accept
    /// `/diff` and `/reload` against the running program.
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

use std::{cell::RefCell, path::Path, rc::Rc, thread, time::Duration};

use cambra::{
    ccl::{
        channels::{ChannelDecl, ChannelFile},
        context::{GlobalContext, ReuseTally, eprint_errors, render_errors},
        provenance::NodeId,
    },
    control_port::{ControlPort, ControlReply, ControlRequest},
    inspector_server::serve_compiled,
    interpreter::{
        Consumer, Scheduler,
        operator_graph::GraphNode,
        tile_operators::{FunctionGuard, Tile, TileGuard},
        value_recorder::{
            self, DEFAULT_ROWS_PER_RECORDING, SharedRecorder, SourceWindow, ValueRecorder,
            render_source_window,
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
    recorder: Option<&SharedRecorder>,
) {
    let Some(port) = control else { return };
    let Some(message) = port.poll() else { return };
    let reply = match message.request() {
        ControlRequest::Diff { code, phase } => match live.diff_against(ctx, code, *phase) {
            Ok(report) => ControlReply::ok(format!(
                "{}{}",
                report.diff,
                render_unreadable(&report.unreadable)
            )),
            Err(errs) => ControlReply::rejected(render_errors(&errs, "<new>", code)),
        },
        ControlRequest::Reload { code } => {
            // A reload rebuilds the operators it could not keep, and a producer
            // takes its recorder handle when it is built — so the replacement
            // records only under a session, exactly as the first compile does.
            // `diff_against` is left out: it compiles a version to compare and
            // throws it away.
            let reloaded = {
                let _recording = recorder.cloned().map(value_recorder::install);
                live.reload(ctx, code, main_consumer)
            };
            match reloaded {
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
                Err(errs) => ControlReply::rejected(render_errors(&errs, "<new>", code)),
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
    channels: &[ChannelDecl],
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

    // Recording is installed for the whole subscribe, which happens inside
    // `compile_program`: a producer takes its handle when its `ProducerBase` is
    // built, and there is no traversal of the live graph to hand one out later.
    let recorder = inspect_port.map(|_| Rc::new(RefCell::new(ValueRecorder::with_defaults())));

    let mut ctx = GlobalContext::default();
    if let Err(e) = ctx.register_channels(channels) {
        eprintln!("error: {e}");
        return Err(());
    }
    let mut live = {
        let _recording = recorder.clone().map(value_recorder::install);
        match LiveProgram::start(&mut ctx, code, &main_consumer) {
            Ok(p) => p,
            Err(errs) => {
                eprint_errors(&errs, src_name, code);
                return Err(());
            }
        }
    };

    // Serve the panes from the same compile that is about to be driven, so a
    // click in a pane names a node the running graph actually built.
    //
    // Named `frames` rather than `live`: `live` is the running program here.
    let frames = match inspect_port {
        Some(port) => match serve_compiled(live.program(), src_name, port) {
            Ok(channel) => Some(channel),
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

    // Publishing sits between the pull and the release, so a source's retained
    // window is sampled before anything is dropped from it.
    //
    // Only when a producer actually produced. The sink loop below polls on a
    // 10ms timer and most polls record nothing, so publishing per iteration
    // would broadcast an unchanged frame a hundred times a second and make
    // `tick` count timer ticks rather than data. Returns whether it published,
    // so the caller advances `tick` only over a tick that carried something.
    let published_through = std::cell::Cell::new(0u64);
    let publish = |tick: u64, sources: &[SourceWindow]| -> bool {
        let (Some(frames), Some(recorder)) = (frames.as_ref(), recorder.as_ref()) else {
            return false;
        };
        let recorded = recorder.borrow().recorded();
        if recorded == published_through.get() {
            return false;
        }
        published_through.set(recorded);
        frames.publish(recorder, sources, tick);
        true
    };

    // The last frame, marked `final`, so a reader can tell a finished run from
    // an idle one. The process parks afterwards, so the socket stays open.
    let finish = |tick: u64, sources: &[SourceWindow]| {
        if let (Some(frames), Some(recorder)) = (frames.as_ref(), recorder.as_ref()) {
            frames.finish(recorder, sources, tick);
        }
    };

    // A source's retained window, read on the thread that owns the graph: the
    // handles are `Rc`, and `retained_keys`/`get` are `&self`, so sampling
    // releases nothing. Sampled before the release below, so a window still
    // shows what the tick delivered.
    //
    // The scheduler's handles are the sources the program *reads*: a handle is
    // registered when an `IterateExtent` over the source is subscribed. Every
    // context registers `stdin` whether or not the program mentions it, so
    // iterating the context's sources instead would report a window for a
    // source that is not part of the program.
    let source_node_ids: std::collections::HashMap<String, NodeId> = live
        .program()
        .operator_graph
        .nodes()
        .iter()
        .filter_map(|node| match node {
            GraphNode::Source { id, name } => Some((name.clone(), *id)),
            _ => None,
        })
        .collect();
    let sample_sources = |scheduler: &Scheduler| -> Vec<SourceWindow> {
        if frames.is_none() {
            return Vec::new();
        }
        scheduler
            .sources()
            .filter_map(|(name, handle)| {
                let source = handle.borrow();
                let keys = source.retained_keys()?;
                let values = source.get(keys.clone());
                Some(render_source_window(
                    source_node_ids.get(name).copied(),
                    name,
                    &keys,
                    &values,
                    DEFAULT_ROWS_PER_RECORDING,
                ))
            })
            .collect()
    };

    let mut tick = 0u64;

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
                recorder.as_ref(),
            );
            if *new_data.borrow() {
                break;
            }
            ctx.scheduler().check_for_notifications();
        }
        *new_data.borrow_mut() = false;

        // Re-read the producer each pass: a reload between ticks replaces it.
        let Some(producer) = live.main_producer_mut() else {
            break;
        };
        debug!("Main calling get");
        if let Some(recorder) = recorder.as_ref() {
            recorder.borrow_mut().set_tick(tick);
        }
        // Sampled before the pull, not after. A `Memo` releases its input from
        // inside `get_impl`, so the release cascade reaches the source buffer
        // partway through the driver's own `get` — sampling afterwards reads a
        // buffer the pull already drained. Before it, the tick's arrivals are
        // present and nothing has taken delivery.
        let sources = sample_sources(ctx.scheduler());
        let tile = producer.get(producer.tiling().universal_guard());
        if publish(tick, &sources) {
            tick += 1;
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
            if let Some(recorder) = recorder.as_ref() {
                recorder.borrow_mut().set_tick(tick);
            }
            ctx.scheduler().check_for_notifications();
            let sources = sample_sources(ctx.scheduler());
            if publish(tick, &sources) {
                tick += 1;
            }
            poll_control(
                control.as_ref(),
                &mut ctx,
                &mut live,
                &main_consumer,
                &new_data,
                recorder.as_ref(),
            );
            if live.done().try_recv().is_ok() {
                break;
            }
            // TODO we shouldn't need to sleep here; we should come up with a better interface
            // for check_for_notifications
            thread::sleep(Duration::from_millis(10));
        }
    }

    finish(tick, &sample_sources(ctx.scheduler()));
    Ok(())
}

/// What the driver has taken delivery of in `tile`, to release back.
///
/// A record value's fields are tiled independently — a scalar field alongside a
/// materialized collection field — so the guard is built per field rather than
/// from the record as a whole.
fn release_guard_for(tile: &Tile) -> TileGuard {
    match tile {
        Tile::Scalar(cv) => TileGuard::Scalar(!cv.is_empty()),
        Tile::SealedFunction {
            domain_predicate, ..
        } => TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
        Tile::Record(fields) => TileGuard::Record(
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
        Tile::SealedFunction { domain, .. } => domain.is_empty(),
        Tile::Record(fields) => fields.values().all(tile_is_empty),
        _ => false,
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

    // A program that calls a host source does not say what that source is, so
    // the declarations travel beside it. Reading them here rather than behind a
    // flag is what lets such a program be run, inspected and dumped from a path
    // like any other — including by the golden sweep, which spawns this binary.
    let channels = match ChannelFile::beside(Path::new(&input_file)) {
        Ok(Some(file)) => file.channels,
        Ok(None) => Vec::new(),
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    match mode {
        Mode::DumpSnapshot => {
            println!(
                "{}",
                cambra::inspector_server::snapshot_body_pretty(&code, &input_file, &channels)
            );
        }
        Mode::InspectOnly { port } => {
            if let Err(e) = cambra::inspector_server::serve(&code, &input_file, port, &channels) {
                eprintln!("error: serving the inspector: {e}");
                std::process::exit(1);
            }
        }
        Mode::Run {
            inspect_port,
            control_port,
        } => {
            if run_program(&input_file, &code, inspect_port, control_port, &channels).is_err() {
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
        run_program("<test>", "x = 1; x", None, None, &[]).unwrap();
    }
}

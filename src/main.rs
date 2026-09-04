use std::{path::Path, thread, time::Duration};

use cambra::{
    ccl::{
        channels::{ChannelDecl, ChannelFile},
        context::{GlobalContext, compile_program, eprint_errors},
        provenance::NodeId,
    },
    host_driver::{self, StdinLines},
    inspector_server::serve_compiled,
    interpreter::{
        Consumer, Scheduler,
        operator_graph::GraphNode,
        tile_operators::{FunctionGuard, Tile, TileGuard},
        value_recorder::{
            self, DEFAULT_ROWS_PER_RECORDING, SourceWindow, ValueRecorder, render_source_window,
        },
    },
};
use log::debug;

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
    channels: &[ChannelDecl],
) -> Result<(), ()> {
    use std::{cell::RefCell, rc::Rc};

    let new_data = Rc::new(RefCell::new(false));
    let new_data_clone = new_data.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        debug!("Main loop received notification");
        *new_data_clone.borrow_mut() = true;
    });

    // Recording is installed for the whole subscribe, which happens inside
    // `compile_program`: a producer takes its handle when its `ProducerBase` is
    // built, and there is no traversal of the live graph to hand one out later.
    let recorder = inspect_port.map(|_| Rc::new(RefCell::new(ValueRecorder::with_defaults())));

    let mut ctx = GlobalContext::default();
    let host_channels = match ctx.register_channels(channels) {
        Ok(registered) => registered,
        Err(e) => {
            eprintln!("error: {e}");
            return Err(());
        }
    };
    // A program with declared channels is driven from stdin for the length of
    // the run; one without never reads a line, so the reader thread is not
    // started and `stdin()` keeps its own.
    let mut input = (!channels.is_empty()).then(StdinLines::new);
    let mut compiled = {
        let _recording = recorder.clone().map(value_recorder::install);
        match compile_program(&mut ctx, code, consumer) {
            Ok(c) => c,
            Err(errs) => {
                eprint_errors(&errs, src_name, code);
                return Err(());
            }
        }
    };

    // Serve the panes from the same compile that is about to be driven, so a
    // click in a pane names a node the running graph actually built.
    let live = match inspect_port {
        Some(port) => match serve_compiled(&compiled, src_name, port) {
            Ok(channel) => Some(channel),
            Err(e) => {
                eprintln!("error: serving the inspector: {e}");
                return Err(());
            }
        },
        None => None,
    };

    let mut main_producer = compiled.main_mut().and_then(|o| o.producer.take());

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
        let (Some(live), Some(recorder)) = (live.as_ref(), recorder.as_ref()) else {
            return false;
        };
        let recorded = recorder.borrow().recorded();
        if recorded == published_through.get() {
            return false;
        }
        published_through.set(recorded);
        live.publish(recorder, sources, tick);
        true
    };

    // The last frame, marked `final`, so a reader can tell a finished run from
    // an idle one. The process parks afterwards, so the socket stays open.
    let finish = |tick: u64, sources: &[SourceWindow]| {
        if let (Some(live), Some(recorder)) = (live.as_ref(), recorder.as_ref()) {
            live.finish(recorder, sources, tick);
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
    let source_node_ids: std::collections::HashMap<String, NodeId> = compiled
        .operator_graph
        .nodes()
        .iter()
        .filter_map(|node| match node {
            GraphNode::Source { id, name } => Some((name.clone(), *id)),
            _ => None,
        })
        .collect();
    let sample_sources = |scheduler: &Scheduler| -> Vec<SourceWindow> {
        if live.is_none() {
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
    if let Some(producer) = main_producer.as_mut() {
        loop {
            while !*new_data.borrow() {
                ctx.scheduler().check_for_notifications();
            }
            *new_data.borrow_mut() = false;

            debug!("Main calling get");
            if let Some(recorder) = recorder.as_ref() {
                recorder.borrow_mut().set_tick(tick);
            }
            // Sampled before the pull, not after. A `Memo` releases its input
            // from inside `get_impl`, so the release cascade reaches the source
            // buffer partway through the driver's own `get` — sampling
            // afterwards reads a buffer the pull already drained. Before it,
            // the tick's arrivals are present and nothing has taken delivery.
            let sources = sample_sources(ctx.scheduler());
            let tile = producer.get(producer.tiling().universal_guard());
            if publish(tick, &sources) {
                tick += 1;
            }

            let release_guard = match &tile {
                Tile::Scalar(cv) => TileGuard::Scalar(!cv.is_empty()),
                Tile::SealedFunction {
                    domain_predicate, ..
                } => TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
                other => panic!("Unexpected top-level tile shape: {other:?}"),
            };
            debug!("Main releasing with {release_guard:?}");
            let done = release_guard.is_universal();
            producer.release(release_guard);
            // Producers can return empty tiles, but still have more data.
            let is_empty = match &tile {
                Tile::Scalar(cv) => cv.is_empty(),
                Tile::SealedFunction { domain, .. } => domain.is_empty(),
                _ => false,
            };
            if !is_empty || done {
                println!("Got value: {tile:#?}");
            }
            if done {
                break;
            }
        }
    }

    // If there are sinks, keep the scheduler running until they all signal
    // completion.  Long-lived servers (e.g. http_serve) never signal, so this
    // loop runs until the process exits.
    //
    // TODO: drive this through `Host::tick`, which is the same body.
    //
    // `embed::Host` was extracted so a WebAssembly host and this one share a
    // driver, and the two have already diverged in shape: the loop below owns
    // its recorder, its windows and its publish bookkeeping, and `Host` owns the
    // same three. Unifying them means `Host` handing back the `main` producer so
    // the loop above can still run a pure program to convergence — a different
    // shape from a tick, and the reason the two were not merged in one step.
    if compiled.sinks().next().is_some() {
        let mut out = std::io::stdout();
        /// Ticks with no sink output after end of input before the run stops.
        /// At the loop's 10 ms cadence this is a fifth of a second, which is
        /// far more than the tick or two a reader lags its writer by.
        const QUIET_TICKS: u32 = 20;
        let mut quiet_ticks = 0u32;
        let mut pending: std::collections::VecDeque<String> = std::collections::VecDeque::new();
        loop {
            if let Some(recorder) = recorder.as_ref() {
                recorder.borrow_mut().set_tick(tick);
            }
            // One line per tick, not the whole backlog: a line is one host
            // event, and a program's answer to it depends on what has already
            // committed. Draining three lines into one tick commits them
            // together, so a view request that follows a price in the input
            // reads the value from before it.
            if let Some(input) = input.as_mut() {
                pending.extend(input.take());
                if let Some(line) = pending.pop_front() {
                    host_driver::push_line(&host_channels, &line);
                }
            }
            ctx.scheduler().check_for_notifications();
            let sources = sample_sources(ctx.scheduler());
            if publish(tick, &sources) {
                tick += 1;
            }
            let produced_this_tick = match host_driver::write_sink_rows(&host_channels, &mut out) {
                Ok(produced) => produced,
                Err(e) => {
                    eprintln!("cambra: writing sink rows: {e}");
                    break;
                }
            };
            if compiled.done.try_recv().is_ok() {
                break;
            }
            // End of input ends the run for a channel-driven program, but not
            // at once: the rows that arrived last still have to reach the sinks,
            // and a reader fires a tick or more after the write it reads. So the
            // loop drains until the program has been quiet for QUIET_TICKS
            // rather than stopping the moment stdin closes. A program reading a
            // socket has no end of input and keeps running.
            if input.as_ref().is_some_and(StdinLines::is_closed) && pending.is_empty() {
                if produced_this_tick {
                    quiet_ticks = 0;
                } else {
                    quiet_ticks += 1;
                    if quiet_ticks >= QUIET_TICKS {
                        break;
                    }
                }
            }
            // TODO we shouldn't need to sleep here; we should come up with a better interface
            // for check_for_notifications
            thread::sleep(Duration::from_millis(10));
        }
    }

    finish(tick, &sample_sources(ctx.scheduler()));
    Ok(())
}

/// The default port for every inspector surface. `Run` and `InspectOnly` are
/// mutually exclusive, so the shared default binds one server at a time.
const DEFAULT_INSPECT_PORT: u16 = 8080;

/// What the binary does with the program it was given.
///
/// The modes are mutually exclusive by construction rather than by a check on
/// two flags that each mean something: a program is either run or it is not, and
/// `--inspect-only` is the not.
enum Mode {
    /// Run the program. With a port, serve its panes and stream the values
    /// flowing through its operators.
    Run { inspect_port: Option<u16> },
    /// Compile the program and serve its panes, without running it. Answers
    /// what the program is, so no values flow.
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
    let mut inspect_only_port: Option<u16> = None;
    let mut dump_snapshot = false;

    for arg in &args[1..] {
        if arg == "--inspect" {
            inspect_port = Some(DEFAULT_INSPECT_PORT);
        } else if let Some(port_str) = arg.strip_prefix("--inspect=") {
            inspect_port = Some(port_str.parse().expect("Invalid port for --inspect"));
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

    let usage =
        "Usage: cambra [--inspect[=PORT] | --inspect-only[=PORT] | --dump-snapshot] <input_file>";
    let mode = match (inspect_port, inspect_only_port, dump_snapshot) {
        (None, Some(port), false) => Mode::InspectOnly { port },
        (None, None, true) => Mode::DumpSnapshot,
        (inspect_port, None, false) => Mode::Run { inspect_port },
        _ => {
            eprintln!("error: --inspect, --inspect-only and --dump-snapshot are exclusive");
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
        Mode::Run { inspect_port } => {
            if run_program(&input_file, &code, inspect_port, &channels).is_err() {
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
        run_program("<test>", "x = 1; x", None, &[]).unwrap();
    }
}

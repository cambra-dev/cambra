use std::{cell::RefCell, rc::Rc, thread, time::Duration};

use cambra::{
    ccl::{
        context::{GlobalContext, ReuseTally, eprint_errors, render_errors},
        symbolic::symbolic,
    },
    control_port::{ControlPort, ControlReply, ControlRequest},
    interpreter::{
        Consumer,
        tile_operators::{FunctionGuard, Tile, TileGuard},
    },
    live_program::LiveProgram,
    pretty_graph::pretty_tile_operator,
    web_inspector::WebInspector,
};
use log::debug;

/// Render the running program's producers into the inspector's snapshot.
fn snapshot(live: &LiveProgram, inspector: Option<&WebInspector>, tick: u64) {
    let Some(inspector) = inspector else { return };
    inspector.update_snapshot(tick, |add| {
        // The `main` producer is held out of the compiled outputs for the
        // driver, so it is read off the program rather than found among them.
        if let Some(p) = live.main_producer() {
            add(p);
        }
        for output in live.program().sinks() {
            if let Some(c) = &output.sink_consumer {
                c.borrow().with_producer(|p| add(p));
            }
        }
    });
}

/// Service at most one pending control request.
///
/// One request per call rather than draining the queue: an accepted `/update`
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
    let reply = match message.request() {
        ControlRequest::Diff { code, stage } => match live.diff_against(ctx, code, *stage) {
            Ok(rendered) => ControlReply::ok(rendered),
            Err(errs) => ControlReply::rejected(render_errors(&errs, "<new>", code)),
        },
        ControlRequest::Update { code } => match live.update(ctx, code, main_consumer) {
            Ok(report) => {
                // The new graph has subscribed but nothing has pulled it, so arm
                // the driver for one pass.
                *new_data.borrow_mut() = true;
                let ReuseTally { adopted, bound } = report.reuse;
                ControlReply::ok(format!(
                    "updated: {adopted}/{bound} bindings adopted\n\n{}",
                    report.diff
                ))
            }
            Err(errs) => ControlReply::rejected(render_errors(&errs, "<new>", code)),
        },
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
    let mut live = match LiveProgram::start(&mut ctx, code, &main_consumer) {
        Ok(p) => p,
        Err(errs) => {
            eprint_errors(&errs, src_name, code);
            return Err(());
        }
    };

    let inspector = inspect_port.map(|port| {
        // Render every output's operator tree.  The AST shown is the full
        // join-planned program (shared across all outputs).
        let op_parts: Vec<String> = live
            .program()
            .outputs
            .iter()
            .map(|o| pretty_tile_operator(o.op.as_ref()))
            .collect();
        WebInspector::new(port, symbolic(&live.program().ast), op_parts.join("\n\n"))
    });
    let control = control_port.map(ControlPort::new);

    let mut tick = 0u64;

    // Drive the `main` output (if any) until it signals a universal release.
    // For sink-only programs this loop is skipped entirely.
    while live.has_main() {
        while !*new_data.borrow() {
            ctx.scheduler().check_for_notifications();
            poll_control(
                control.as_ref(),
                &mut ctx,
                &mut live,
                &main_consumer,
                &new_data,
            );
        }
        *new_data.borrow_mut() = false;

        // Re-read the producer each pass: an update between ticks replaces it.
        let Some(producer) = live.main_producer_mut() else {
            break;
        };
        debug!("Main calling get");
        let tile = producer.get(producer.tiling().universal_guard());

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
        snapshot(&live, inspector.as_ref(), tick);
        tick += 1;
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

    // If there are sinks, keep the scheduler running until they all signal
    // completion.  Long-lived servers (e.g. http_serve) never signal, so this
    // loop runs until the process exits.
    if live.program().sinks().next().is_some() {
        loop {
            ctx.scheduler().check_for_notifications();
            snapshot(&live, inspector.as_ref(), tick);
            tick += 1;
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

    Ok(())
}

/// Runs a given Cambra file, specified as the first command-line argument.
fn main() {
    env_logger::init();
    let args: Vec<String> = std::env::args().collect();

    let mut input_file = None;
    let mut inspect_port: Option<u16> = None;
    let mut control_port: Option<u16> = None;

    for arg in &args[1..] {
        if arg == "--inspect" {
            inspect_port = Some(8080);
        } else if let Some(port_str) = arg.strip_prefix("--inspect=") {
            inspect_port = Some(port_str.parse().expect("Invalid port for --inspect"));
        } else if arg == "--control" {
            control_port = Some(8081);
        } else if let Some(port_str) = arg.strip_prefix("--control=") {
            control_port = Some(port_str.parse().expect("Invalid port for --control"));
        } else {
            input_file = Some(arg.clone());
        }
    }

    let input_file = input_file.unwrap_or_else(|| {
        eprintln!("Usage: cambra [--inspect[=PORT]] [--control[=PORT]] <input_file>");
        std::process::exit(1);
    });

    let code = std::fs::read_to_string(&input_file).expect("Failed to read input file");

    if run_program(&input_file, &code, inspect_port, control_port).is_err() {
        std::process::exit(1);
    }

    if let Some(port) = inspect_port {
        eprintln!("Program finished. Inspector at http://localhost:{port} — press Ctrl+C to exit.");
        loop {
            std::thread::park();
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

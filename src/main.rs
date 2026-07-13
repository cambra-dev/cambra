use std::{thread, time::Duration};

use cambra::{
    ccl::{
        context::{GlobalContext, compile_program, eprint_errors},
        symbolic::symbolic,
    },
    interpreter::{
        Consumer,
        tile_operators::{FunctionGuard, Tile, TileGuard},
    },
    pretty_graph::pretty_tile_operator,
    web_inspector::WebInspector,
};
use log::debug;

/// Runs a Cambra program from a source string.
///
/// `src_name` is the label shown in error reports (typically the input
/// file name). Returns `Err(())` if compilation failed; the errors have
/// already been rendered to stderr by [`eprint_errors`], so the caller's
/// job is just to exit non-zero.
fn run_program(src_name: &str, code: &str, inspect_port: Option<u16>) -> Result<(), ()> {
    use std::{cell::RefCell, rc::Rc};

    let new_data = Rc::new(RefCell::new(false));
    let new_data_clone = new_data.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        debug!("Main loop received notification");
        *new_data_clone.borrow_mut() = true;
    });

    let mut ctx = GlobalContext::default();
    let mut compiled = match compile_program(&mut ctx, code, consumer) {
        Ok(c) => c,
        Err(errs) => {
            eprint_errors(&errs, src_name, code);
            return Err(());
        }
    };

    let inspector = inspect_port.map(|port| {
        // Render every output's operator tree.  The AST shown is the full
        // join-planned program (shared across all outputs).
        let op_parts: Vec<String> = compiled
            .outputs
            .iter()
            .map(|o| pretty_tile_operator(o.op.as_ref()))
            .collect();
        WebInspector::new(port, symbolic(&compiled.ast), op_parts.join("\n\n"))
    });

    // Pull the main producer out of `compiled` so the rest of the outputs can
    // be borrowed immutably during snapshot() while we drive the producer.
    let mut main_producer = compiled.main_mut().and_then(|o| o.producer.take());

    let snapshot =
        |tick: u64,
         main_producer: Option<&dyn cambra::interpreter::tile_operators::TileProducer>| {
            if let Some(ref insp) = inspector {
                insp.update_snapshot(tick, |add| {
                    if let Some(p) = main_producer {
                        add(p);
                    }
                    for output in compiled.sinks() {
                        if let Some(ref c) = output.sink_consumer {
                            c.borrow().with_producer(|p| add(p));
                        }
                    }
                });
            }
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
            let tile = producer.get(producer.tiling().universal_guard());
            snapshot(tick, Some(producer.as_ref()));
            tick += 1;

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
    if compiled.sinks().next().is_some() {
        loop {
            ctx.scheduler().check_for_notifications();
            snapshot(tick, None);
            tick += 1;
            if compiled.done.try_recv().is_ok() {
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

    for arg in &args[1..] {
        if arg == "--inspect" {
            inspect_port = Some(8080);
        } else if let Some(port_str) = arg.strip_prefix("--inspect=") {
            inspect_port = Some(port_str.parse().expect("Invalid port for --inspect"));
        } else {
            input_file = Some(arg.clone());
        }
    }

    let input_file = input_file.unwrap_or_else(|| {
        eprintln!("Usage: cambra [--inspect[=PORT]] <input_file>");
        std::process::exit(1);
    });

    let code = std::fs::read_to_string(&input_file).expect("Failed to read input file");

    if run_program(&input_file, &code, inspect_port).is_err() {
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
        run_program("<test>", "x = 1; x", None).unwrap();
    }
}

use cambra::{
    ccl::{
        context::{GlobalContext, compile_program},
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

/// Runs a Cambra program given as a string of Python code.
fn run_program(code: &str, inspect_port: Option<u16>) {
    use std::{cell::RefCell, rc::Rc};

    let new_data = Rc::new(RefCell::new(false));
    let new_data_clone = new_data.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        debug!("Main loop received notification");
        *new_data_clone.borrow_mut() = true;
    });

    let mut ctx = GlobalContext::default();
    let (ast_tree, operator_tree, mut producer) = compile_program(&mut ctx, code, consumer);

    let inspector = inspect_port.map(|port| {
        WebInspector::new(
            port,
            symbolic(&ast_tree),
            pretty_tile_operator(operator_tree.as_ref()),
        )
    });

    let mut tick = 0u64;
    loop {
        while !*new_data.borrow() {
            debug!("Scheduler checking for notifications");
            ctx.scheduler().check_for_notifications();
        }
        *new_data.borrow_mut() = false;

        debug!("Main calling get");
        let tile = producer.get(producer.tiling().universal_guard());

        if let Some(ref insp) = inspector {
            insp.update_snapshot(tick, producer.as_ref());
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
        println!("Got value: {tile:#?}");
        if done {
            break;
        }
    }
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

    run_program(&code, inspect_port);

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
        run_program("x = 1; x", None);
    }
}

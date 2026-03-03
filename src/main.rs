use std::{cell::RefCell, rc::Rc};

use cambra::{
    interpreter::{Consumer, GetResult, Guard, Scheduler},
    lowering::{lower_let_stmt_block, LoweringContext},
    parse_python_code, pretty_ast,
    pretty_graph::{self, pretty_dataflow},
    web_inspector::WebInspector,
};
use log::debug;
use rustpython_parser::ast::Mod;

/// Runs a Cambra program given as a string of Python code.
///
/// The program must currently be a series of assignments and a single final expression.
/// Will loop continuously calling get and release on that expression's producer until
/// it is notified with a Universal obsolete Guard.
///
/// When `inspect_port` is `Some`, starts a web inspector on that port, computing
/// static AST and operator graph trees from the parsed/lowered program.
fn run_program(code: &str, inspect_port: Option<u16>) {
    let module: Mod = parse_python_code(code).expect("Failed to parse Python code");

    let ast_tree = pretty_ast::pretty(&module);

    let stmts = match module {
        Mod::Module { body, .. } => body,
        _ => panic!("Expected module, got {module:?}"),
    };
    let mut scheduler = Scheduler::new();
    let (mut op, scope) =
        lower_let_stmt_block(&mut LoweringContext::default(), &stmts, &mut scheduler).unwrap();

    let operator_tree = pretty_graph::pretty_operator(op.as_ref());

    let inspector = inspect_port.map(|port| WebInspector::new(port, ast_tree, operator_tree));

    let new_data = Rc::new(RefCell::new(false));
    let new_data_clone = new_data.clone();
    let mut obsolete_guard: Guard;
    let consumer: Box<dyn Consumer> = Box::new(move || {
        debug!("Main loop received notification");
        *new_data_clone.borrow_mut() = true;
    });

    let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);

    let mut tick: u64 = 0;
    if let Some(ref inspector) = inspector {
        inspector.update_snapshot(tick, &*producer, &scheduler);
    }
    debug!("main producer:\n{}", pretty_dataflow(producer.as_ref()));

    loop {
        while !*new_data.borrow() {
            debug!("Scheduler checking for notifications");
            scheduler.check_for_notifications();
            tick += 1;

            if let Some(ref inspector) = inspector {
                inspector.update_snapshot(tick, &*producer, &scheduler);
            }
        }
        let GetResult {
            column_value,
            yield_guard,
        } = producer.get();
        debug!("Main got yield_guard: {yield_guard:?}, releasing");
        obsolete_guard = producer.release(yield_guard.clone());
        debug!("Main release got {obsolete_guard:?}");
        *new_data.borrow_mut() = false;
        println!("Got value: {:#?}", &column_value);
        tick += 1;
        if let Some(ref inspector) = inspector {
            inspector.update_snapshot(tick, &*producer, &scheduler);
        }

        if yield_guard.is_universal() {
            break;
        }
    }
    producer.release(Guard::universal());
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

    // When inspecting, keep the process alive so the dashboard remains accessible.
    if let Some(port) = inspect_port {
        eprintln!(
            "Program finished. Inspector at http://localhost:{} — press Ctrl+C to exit.",
            port
        );
        loop {
            std::thread::park();
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::run_program;
    use test_log::test;

    /// Smoke test that makes sure running a simple program doesn't crash.
    #[test]
    fn test_run_program() {
        run_program("x = 1; x", None);
    }
}

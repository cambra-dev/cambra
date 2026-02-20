use std::{cell::RefCell, rc::Rc};

use cambra::{
    interpreter::{Consumer, GetResult, Guard, Notification, Scheduler, Value},
    lowering::{lower_let_stmt_block, LoweringContext},
    parse_python_code, pretty_ast, pretty_graph,
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

    let yield_guard = Rc::new(RefCell::new(Guard::empty()));
    let yield_guard_clone = yield_guard.clone();
    let new_data = Rc::new(RefCell::new(false));
    let new_data_clone = new_data.clone();
    let mut obsolete_guard: Guard;
    let consumer: Box<dyn Consumer> = Box::new(move |notification: Notification| {
        debug!("Main loop received notification: {notification:?}");
        match notification {
            Notification::NewData => *new_data_clone.borrow_mut() = true,
            Notification::Yield(yield_guard) => *yield_guard_clone.borrow_mut() = yield_guard,
        };
    });

    let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);

    let mut tick: u64 = 0;
    if let Some(ref inspector) = inspector {
        inspector.update_snapshot(tick, &*producer, &scheduler);
    }
    debug!("main producer:\n{producer:#?}");

    loop {
        while !*new_data.borrow() && !yield_guard.borrow().is_universal() {
            debug!("Scheduler checking for notifications");
            scheduler.check_for_notifications();
            tick += 1;

            if let Some(ref inspector) = inspector {
                inspector.update_snapshot(tick, &*producer, &scheduler);
            }
        }
        let GetResult {
            column_value,
            yield_guard: new_yield_guard,
        } = producer.get();
        *yield_guard.borrow_mut() = new_yield_guard;

        let new_obsolete_guard: Guard = match column_value.as_single() {
            Some(Value::Function(bindings)) => Guard::Domain(Box::new(
                bindings
                    .last()
                    .map(|b| b.input.clone())
                    .map_or(Guard::Empty, Guard::LessThanOrEq),
            )),
            _ => {
                debug!("Main received constant, releasing Universal");
                Guard::Universal
            }
        };
        obsolete_guard = producer.release(new_obsolete_guard.clone());
        debug!("Main released with {new_obsolete_guard:?}, got {obsolete_guard:?}");
        *new_data.borrow_mut() = false;

        tick += 1;
        if let Some(ref inspector) = inspector {
            inspector.update_snapshot(tick, &*producer, &scheduler);
        }

        if yield_guard.borrow().is_universal() {
            break;
        }
        println!("Got value: {:#?}", &column_value.data);
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

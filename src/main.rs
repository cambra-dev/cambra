use std::{cell::RefCell, rc::Rc};

use cambra::{
    interpreter::{Consumer, GetResult, Guard, Notification, Scheduler, Value},
    lowering::lower_let_stmt_block,
    parse_python_code,
};
use log::debug;
use rustpython_parser::ast::Mod;

/// Runs a Cambra program given as a string of Python code.
/// The program must currently be a series of assignments and a single final expression
/// Will loop continuously calling get and release on that expression's producer until
/// it is notified with a Universal obsolete Guard.
fn run_program(code: &str) {
    let module: Mod = parse_python_code(code).expect("Failed to parse Python code");
    let stmts = match module {
        Mod::Module { body, .. } => body,
        _ => panic!("Expected module, got {:?}", module),
    };
    let mut scheduler = Scheduler::new();
    let (mut op, scope) = lower_let_stmt_block(&stmts, &mut scheduler).unwrap();

    let yield_guard = Rc::new(RefCell::new(Guard::empty()));
    let yield_guard_clone = yield_guard.clone();
    let new_data = Rc::new(RefCell::new(false));
    let new_data_clone = new_data.clone();
    let mut obsolete_guard: Guard;
    let consumer: Box<dyn Consumer> = Box::new(move |notification: Notification| {
        debug!("Main loop received notification: {:?}", notification);
        match notification {
            Notification::NewData => *new_data_clone.borrow_mut() = true,
            Notification::Yield(yield_guard) => *yield_guard_clone.borrow_mut() = yield_guard,
        };
    });

    let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);

    debug!("main producer:\n{:#?}", producer);

    loop {
        while !*new_data.borrow() && !yield_guard.borrow().is_universal() {
            debug!("Scheduler checking for notifications");
            scheduler.check_for_notifications();
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
        debug!(
            "Main released with {:?}, got {:?}",
            new_obsolete_guard, obsolete_guard
        );
        *new_data.borrow_mut() = false;
        if yield_guard.borrow().is_universal() {
            break;
        }
        println!("Got value: {:#?}", &column_value.values);
    }
    producer.release(Guard::universal());
}

/// Runs a given Cambra file, specified as the first command-line argument.
fn main() {
    env_logger::init();
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() != 2 {
        debug!("Usage: cambra <input_file>");
        std::process::exit(1);
    }
    let input_file = &args[1];
    let code = std::fs::read_to_string(input_file).expect("Failed to read input file");

    run_program(&code);
}

#[cfg(test)]
mod tests {
    use crate::run_program;
    use test_log::test;

    /// Smoke test that makes sure running a simple program doesn't crash.
    #[test]
    fn test_run_program() {
        run_program("x = 1; x")
    }
}

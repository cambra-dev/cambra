//! What a function requires and causes, as inference collects it and a module's interface
//! prints it (`docs/chl-spec.md`, "6.9 Capabilities";
//! `src/ccl/design/type-inference.md`, "Capability variables").

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::check_scalar;
use super::modules::program;

/// The members the cases below share: a transactional mutable variable, a feed, functions
/// that commit a transaction, and a higher-order function.
const PRELUDE: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    out: Feed(_)

    pub def take(n: Int):
        with begin():
            stock := stock - n

    pub def taken(n: Int) => Int:
        take(n)
        n

    def apply(f, x):
        f(x)
"};

/// The interface `code`, checked as a module, prints.
fn interface_of(code: &str) -> String {
    check_program(&mut GlobalContext::default(), &program(code, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"))
}

/// The errors checking `code` as a module reports, rendered.
fn errors_of(code: &str) -> String {
    match check_program(&mut GlobalContext::default(), &program(code, &[])) {
        Ok(interface) => panic!("expected an error, got:\n{interface}"),
        Err(errors) => format!("{errors:?}"),
    }
}

/// The clauses after the codomain of `member`'s contract, as `cambra check` prints it: from its
/// `requires` or, without one, its `causes`. A parameter's or a codomain's own clauses are in
/// parentheses, so the contract's are the first outside every bracket.
fn clauses_of(code: &str, member: &str) -> String {
    let interface = interface_of(&format!("{PRELUDE}\n{code}"));
    let prefix = format!("pub {member}: ");
    let line = interface
        .lines()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("no `{member}` in the interface:\n{interface}"));
    let mut depth = 0usize;
    for (at, c) in line.char_indices() {
        match c {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => depth -= 1,
            ' ' if depth == 0
                && (line[at..].starts_with(" requires ") || line[at..].starts_with(" causes ")) =>
            {
                return line[at + 1..].to_owned();
            }
            _ => {}
        }
    }
    String::new()
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// A `with begin():` block commits, and its write is of the module's own state, which the
// interface writes `Module::*` since no other module names the private `stock`.
#[case(
    "",
    "take",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
// A feed names the feed it appends to.
#[case(
    indoc! {"
        pub def report(n: Int):
            out << n
    "},
    "report",
    "causes Append(out)"
)]
// A call does what its callee does.
#[case(
    indoc! {"
        pub def twice(n: Int):
            take(n)
            take(n)
    "},
    "twice",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
// A loop body runs where the loop stands, and so does a comprehension's element.
#[case(
    indoc! {"
        pub def report_all(xs):
            for x in xs:
                out << x
    "},
    "report_all",
    "requires r: Iterable(A), r::Elements <: C causes Append(out)"
)]
#[case(
    indoc! {"
        pub def take_listed(xs):
            [take(x) for x in xs]
    "},
    "take_listed",
    "requires r: Iterable(A), r::Elements <: C, ReadTxn(Module::*) causes RunTransaction, \
     WriteTxn(Module::*)"
)]
// Each use of a polymorphic function collects its own capabilities, so a call that passes it a
// committing function commits and one that passes it a pure function does not.
#[case(
    indoc! {"
        pub def committing_use(x: Int):
            apply(take, x)
    "},
    "committing_use",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
#[case(
    indoc! {"
        pub def committing_use(x: Int):
            apply(take, x)
        pub def pure_use(x: Int):
            apply(\\y -> y + 1, x)
    "},
    "pure_use",
    ""
)]
// A variable a function's body binds is the function's own, so writing it is no effect of
// the function's.
#[case(
    indoc! {"
        pub def total(xs):
            t := 0
            for x in xs:
                t += x
            t
    "},
    "total",
    "requires r: Iterable(A), r::Elements <: B, r1: Addable(Int, C), r1::Output <: Int"
)]
#[case(
    indoc! {"
        pub def local_feed(xs):
            g: Feed(_)
            for x in xs:
                g << x
            sum(g)
    "},
    "local_feed",
    "requires r: Iterable(A), r::Elements <: B"
)]
// A `Mut` parameter's history is its argument's, so the call writes the argument: the
// caller's own variable here, which is no effect of the caller's…
#[case(
    indoc! {"
        def inc(x: Mut(Int)):
            x += 1
        pub def counted(xs):
            c := 0
            for x in xs:
                inc(c)
            c
    "},
    "counted",
    "requires r: Iterable(A), r::Elements <: B"
)]
// …and a transactional variable there, which is.
#[case(
    indoc! {"
        def bump(x: Mut(Int, Txn)):
            with begin():
                x += 1
        pub def bump_stock(n: Int):
            bump(stock)
    "},
    "bump_stock",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
// A written clause is a lower bound: the body adds what it does, and a call sees what the
// clause lists whether or not the body does it.
#[case(
    indoc! {"
        pub def report(n: Int) causes AffectWorld:
            out << n
    "},
    "report",
    "causes Append(out), AffectWorld"
)]
#[case(
    indoc! {"
        pub def later(n: Int) causes RunTransaction:
            n
    "},
    "later",
    "causes RunTransaction"
)]
// `only` makes the clause an upper bound that the body meets.
#[case(
    indoc! {"
        pub def take_only(n: Int) causes only WriteTxn(stock), RunTransaction:
            take(n)
    "},
    "take_only",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
// A written function type's clauses are exact, so a function meeting them is passed, and the
// call does what the type states.
#[case(
    indoc! {"
        def call_with(f: (Int => Int requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction), x: Int):
            f(x)
        pub def call_taken(n: Int):
            call_with(taken, n)
    "},
    "call_taken",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
// A parameter's `_` is what each call passes.
#[case(
    indoc! {"
        def call_with(f: (Int => Int requires _ causes _), x: Int):
            f(x)
        pub def via_hole(n: Int):
            call_with(taken, n)
    "},
    "via_hole",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
// A declared parameter is what each call passes.
#[case(
    indoc! {"
        def call_all(R <: Context, E <: Effect, f: (Int => Int requires R causes E), x: Int) causes only E:
            f(x)
        pub def via_param(n: Int):
            call_all(taken, n)
    "},
    "via_param",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
// A `let` annotation's `_` is what its value fills.
#[case(
    indoc! {"
        g: Int => Int requires _ causes _ = taken
        pub def via_g(n: Int):
            g(n)
    "},
    "via_g",
    "requires ReadTxn(Module::*) causes RunTransaction, WriteTxn(Module::*)"
)]
fn a_contract_states_what_the_function_causes(
    #[case] code: &str,
    #[case] member: &str,
    #[case] expected: &str,
) {
    assert_eq!(clauses_of(code, member), expected);
}

/// A function type with clauses is parenthesized where another type follows it, in a tuple, or
/// where clauses after it would read as its own: those of an arrow whose codomain it is.
#[rstest]
#[case::a_codomain(
    indoc! {"
        pub def make(n: Int):
            out << n
            take
    "},
    "pub make: Int => (Int => {} requires ReadTxn(Module::*) causes RunTransaction, \
     WriteTxn(Module::*)) causes Append(out)"
)]
#[case::a_tuple_component(
    indoc! {"
        pub def pair(n: Int):
            (take, n)
    "},
    "pub pair: Int => {(Int => {} requires ReadTxn(Module::*) causes RunTransaction, \
     WriteTxn(Module::*)), Int}"
)]
fn a_function_type_with_clauses_is_parenthesized(#[case] code: &str, #[case] line: &str) {
    let interface = interface_of(&format!("{PRELUDE}\n{code}"));
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// A feed reached through a second name is not tracked: a capability is keyed by the name it is
/// recorded through, and a feed handle, unlike a `Mut` one, is a value that travels
/// (`src/ccl/design/type-inference.md`, "4.9 Capabilities"). These pin the current output, which
/// names the parameter, the alias and the projection, where each should be `Append(out)`; the
/// mutability redesign decides how a feed travels.
#[rstest]
#[case::an_unannotated_parameter(
    indoc! {"
        def emit(o, v: Int):
            o << v
        pub def emit_out(v: Int):
            emit(out, v)
    "},
    "emit_out",
    "causes Append(o)"
)]
#[case::an_alias(
    indoc! {"
        pub def via_alias(v: Int):
            log: Feed(_) = out
            log << v
    "},
    "via_alias",
    "causes Append(log)"
)]
#[case::a_projection(
    indoc! {"
        pub def via_tuple(v: Int):
            p = (out, v)
            q = p.0
            q << v
    "},
    "via_tuple",
    "causes Append(q)"
)]
// An annotated parameter is tracked: its capability is its argument's.
#[case::an_annotated_parameter(
    indoc! {"
        def emit(o: Feed(Int), v: Int):
            o << v
        pub def emit_out(v: Int):
            emit(out, v)
    "},
    "emit_out",
    "causes Append(out)"
)]
fn a_feed_reached_through_another_name(
    #[case] code: &str,
    #[case] member: &str,
    #[case] expected: &str,
) {
    assert_eq!(clauses_of(code, member), expected);
}

/// A function whose capabilities are what a function argument's are is polymorphic in them, and
/// its contract names each part a written clause leaves open (`docs/chl-spec.md`, "Writing
/// requirements and effects").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_called_parameter(
    indoc! {"
        pub def call(f, x):
            f(x)
    "},
    "pub call: forall (A, B, R <: Context, E <: Effect) {(A => B requires R causes E), A} => \
     B requires R causes E"
)]
#[case::a_hole_in_a_written_parameter_type(
    indoc! {"
        pub def call_with(f: (Int => Int causes _), x: Int):
            f(x)
    "},
    "pub call_with: forall (E <: Effect) {(Int => Int causes E), Int} => Int causes E"
)]
#[case::a_parameter_called_twice(
    indoc! {"
        pub def twice(f, x: Int) => Int:
            f(f(x))
    "},
    "pub twice: forall (R <: Context, E <: Effect) {(Int => Int requires R causes E), Int} => Int \
     requires R causes E"
)]
#[case::a_parameter_never_called(
    indoc! {"
        pub def keep(f, x: Int):
            x
    "},
    "pub keep: forall (A) {A, Int} => Int"
)]
#[case::a_returned_function(
    indoc! {"
        pub def compose(f, g):
            \\x -> g(f(x))
    "},
    "pub compose: forall (A, B, C, R <: Context, E <: Effect, R1 <: Context, E1 <: Effect) \
     {(A => B requires R causes E), (B => C requires R1 causes E1)} => A => C requires R, R1 \
     causes E, E1"
)]
#[case::a_declared_effect_parameter(
    indoc! {"
        pub def call_all(E <: Effect, f: (Int => Int causes E), x: Int) causes only E:
            f(x)
    "},
    "pub call_all: forall (E <: Effect) {(Int => Int causes E), Int} => Int causes E"
)]
#[case::a_declared_requirement_parameter(
    indoc! {"
        pub def with_ctx(R <: Context, f: (Int => Int requires R), x: Int) requires only R:
            f(x)
    "},
    "pub with_ctx: forall (R <: Context) {(Int => Int requires R), Int} => Int requires R"
)]
fn a_contract_names_the_effects_an_argument_brings(#[case] code: &str, #[case] line: &str) {
    let interface = interface_of(code);
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// A printed contract is an annotation a program can write: a function type with clauses in a
/// tuple is parenthesized, so the comma after it ends its clause.
#[test]
fn a_printed_contract_annotates_its_definition() {
    check_scalar(
        indoc! {"
            def call_with(f: (Int => Int causes _), x: Int):
                f(x)
            g: forall (E <: Effect) {(Int => Int causes E), Int} => Int causes E = call_with
            g(\\y -> y + 1, 4)
        "},
        Value::Int(5),
    );
}

/// A clause bounding what a function may require or cause refuses a body or an argument that
/// exceeds it, and a clause naming no variable of the kind it takes is refused
/// (`docs/chl-spec.md`, "Writing requirements and effects").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::beyond_only(
    indoc! {"
        def f(n: Int) causes only RunTransaction:
            with begin():
                stock := stock - n
            n
    "},
    "this has `WriteTxn(stock)`, which the definition's clause"
)]
#[case::beyond_nothing(
    indoc! {"
        def f(n: Int) causes nothing:
            out << n
            n
    "},
    "this has `Append(out)`, which the definition's clause"
)]
#[case::an_inferred_trait_requirement(
    indoc! {"
        def add(a, b) requires nothing:
            a + b
    "},
    "Addable(A, B)"
)]
#[case::an_argument_beyond_a_written_type(
    indoc! {"
        def call_with(f: Int => Int, x: Int):
            f(x)
        call_with(taken, 1)
    "},
    "this has `ReadTxn(stock)`, which the function type it must have does not state"
)]
#[case::beyond_a_parameter(
    indoc! {"
        def f(E <: Effect, g: (Int => Int causes E), n: Int) causes only E:
            out << n
            g(n)
    "},
    "this has `Append(out)`, which the definition's clause"
)]
#[case::a_name_bound_nowhere(
    indoc! {"
        def f(n: Int) causes Write(nope):
            n
    "},
    "`Write(nope)` names no variable in scope"
)]
#[case::a_feed_written(
    indoc! {"
        def f(n: Int) causes Write(out):
            n
    "},
    "`Write(out)` names no variable in scope"
)]
fn a_clause_refuses_what_exceeds_it(#[case] code: &str, #[case] needle: &str) {
    let errors = super::modules::compile_errors(&program(&format!("{PRELUDE}\n{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// A `_` in a parameter's type whose capabilities reach a bounded clause of the `def` takes
/// that bound, so the contract states it and a use passing more is refused at the call.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::nothing(
    indoc! {"
        pub def p(f: (Int => Int causes _), x: Int) => Int causes nothing:
            f(x)
    "},
    "pub p: {Int => Int, Int} => Int"
)]
#[case::a_listed_effect(
    indoc! {"
        pub def q(f: (Int => Int causes _), x: Int) => Int causes only Append(out):
            f(x)
    "},
    "pub q: {(Int => Int causes Append(out)), Int} => Int causes Append(out)"
)]
#[case::what_a_block_discharges(
    indoc! {"
        pub def r(f: (Int => Int requires _), x: Int) => Int requires nothing:
            with begin():
                stock := f(x)
            x
    "},
    "pub r: {(Int => Int requires Transaction), Int} => Int causes RunTransaction, \
     WriteTxn(Module::*)"
)]
#[case::a_clause_variable(
    indoc! {"
        pub def s(E <: Effect, g: (Int => Int causes E), f: (Int => Int causes _), x: Int) => Int causes only E:
            g(f(x))
    "},
    "pub s: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes E), Int} => Int \
     causes E"
)]
fn a_hole_reaching_a_bounded_clause_takes_its_bound(#[case] code: &str, #[case] line: &str) {
    let interface = interface_of(&format!("{PRELUDE}\n{code}"));
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// A use passing a function beyond the bound a hole takes is refused at the call.
#[test]
fn an_argument_beyond_a_holes_bound_is_refused_at_the_call() {
    let code = indoc! {"
        def noisy(n: Int) => Int:
            out << n
            n
        def p(f: (Int => Int causes _), x: Int) => Int causes nothing:
            f(x)
        p(noisy, 1)
    "};
    let errors = super::modules::compile_errors(&program(&format!("{PRELUDE}\n{code}"), &[]));
    assert_eq!(super::modules::report_count(&errors), 1, "{errors}");
    assert!(
        errors.contains(
            "this has `Append(out)`, which the function type it must have does not state"
        ),
        "{errors}"
    );
    assert!(errors.contains("p(noisy, 1)"), "{errors}");
}

/// A capability beyond a written function type stops at that type, so an argument the type
/// refuses is reported once, at the call, and not again where the function is called.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_argument(indoc! {"
    def noisy(n: Int) => Int:
        out << n
        n
    def apply(f: Int => Int, x: Int) => Int causes nothing:
        f(x)
    apply(noisy, 1)
"})]
#[case::a_returned_function(indoc! {"
    def noisy(n: Int) => Int:
        out << n
        n
    def pick(n: Int) => (Int => Int) causes nothing:
        noisy
    def call_pick(n: Int) => Int causes nothing:
        pick(n)(n)
    call_pick(1)
"})]
fn a_capability_beyond_a_written_type_is_reported_once(#[case] code: &str) {
    let errors = super::modules::compile_errors(&program(&format!("{PRELUDE}\n{code}"), &[]));
    assert_eq!(super::modules::report_count(&errors), 1, "{errors}");
    assert!(
        errors.contains("which the function type it must have does not state"),
        "{errors}"
    );
}

/// A clause naming no variable is reported at the clause, which no node of the tree stands for,
/// rather than at the whole definition.
#[test]
fn a_clause_naming_no_variable_is_reported_at_the_clause() {
    let code = indoc! {"
        def f(n: Int) => Int causes Write(nope):
            n
        f(1)
    "};
    let consumer: Box<dyn cambra::interpreter::Consumer> = Box::new(|| {});
    let Err(errors) = cambra::ccl::context::compile_program(
        &mut GlobalContext::default(),
        &cambra::ccl::load::LoadedProgram::test(code),
        consumer,
    ) else {
        panic!("expected a compile error");
    };
    let [cambra::ccl::context::CompileError::Infer { span, .. }] = errors.as_slice() else {
        panic!("expected one located inference error, got {errors:?}");
    };
    assert_eq!(&code[span.start..span.end], "causes Write(nope)");
}

/// A clause form this compiler does not implement yet, and one written where it cannot stand,
/// is refused where it is written.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_exception(
    indoc! {"
        def f(n: Int) causes Raise(Int):
            n
    "},
    "`Raise` is not supported yet"
)]
#[case::an_effect_variable(
    indoc! {"
        def f(n: Int) causes E:
            n
    "},
    "`E` is not an effect"
)]
#[case::a_hole_under_only(
    indoc! {"
        def f(n: Int) causes only _:
            n
    "},
    "`only` makes a clause an upper bound"
)]
#[case::a_trait_requirement_in_a_function_type(
    indoc! {"
        def call_with(f: (Int => Int requires Orderable(Int, Int)), x: Int):
            f(x)
    "},
    "a function type's `requires` clause names only"
)]
#[case::a_clause_on_an_instance_function(
    indoc! {"
        type Count:
            count(n: Int)
        trait Twice(T):
            def twice(t: T) => T
        instance Twice(Count):
            def twice(t: Count) => Count causes RunTransaction:
                t
    "},
    "an instance's function requires and causes what its trait's signature states"
)]
#[case::a_parameter_in_the_other_clause(
    indoc! {"
        def f(R <: Context, g: (Int => Int causes R), n: Int):
            g(n)
    "},
    "`R` is bounded by `Context`, so it stands in a `requires` clause"
)]
#[case::a_bound_as_a_value_type(
    indoc! {"
        def f(x: Effect):
            x
    "},
    "`Effect` bounds a type parameter standing for a clause"
)]
fn an_unsupported_or_misplaced_clause_is_refused(#[case] code: &str, #[case] needle: &str) {
    let errors = super::modules::compile_errors(&program(&format!("{PRELUDE}\n{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// An expression statement before its block's last statement, or anywhere in a loop body, is
/// evaluated only for what it causes, so one that causes nothing is refused (`docs/chl-spec.md`,
/// "4.9 Expression statement"), in every module of the program.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_pure_call(
    indoc! {"
        def f(x):
            x + 1
        f(3)
        2
    "},
    ""
)]
#[case::arithmetic(
    indoc! {"
        x = 1
        x + 1
        2
    "},
    ""
)]
#[case::in_a_loop_body(
    indoc! {"
        cnt := 0
        for x in [1, 2]:
            x + 1
            cnt += x
        cnt
    "},
    ""
)]
#[case::in_a_loop_in_a_def(
    indoc! {"
        def total(xs):
            c := 0
            for x in xs:
                x + 1
                c += x
            c
        total([1, 2])
    "},
    ""
)]
#[case::in_a_run_module(
    indoc! {"
        run lib as l
        1
    "},
    indoc! {"
        visits: Mut(Int, Txn) := 0
        x = 1
        x + 1
    "}
)]
#[case::in_an_imported_function(
    indoc! {"
        import lib
        lib::f(1)
    "},
    indoc! {"
        pub def f(n):
            n + 1
            n
    "}
)]
fn an_expression_statement_that_causes_nothing_is_refused(#[case] root: &str, #[case] lib: &str) {
    let modules: &[(&str, &str)] = if lib.is_empty() { &[] } else { &[("lib", lib)] };
    let errors = super::modules::compile_errors(&program(root, modules));
    assert!(
        errors.contains("this statement causes nothing and its value is discarded"),
        "{errors}"
    );
}

/// The root's last statement is the program's value, so `cambra check` keeps it, as running the
/// program does.
#[test]
fn a_roots_last_statement_is_its_value() {
    interface_of(indoc! {"
        x = 1
        x + 1
    "});
}

/// A statement calling a function parameter does what the function each use passes does,
/// which the definition does not know, so the definition does not refuse it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_statement_calling_a_parameter_is_kept() {
    super::helpers::check_program_scalar(
        &program(
            indoc! {"
                def each(f, x):
                    f(x)
                    x
                each(\\y -> y + 1, 2)
            "},
            &[],
        ),
        cambra::interpreter::Value::Int(2),
    );
}

/// A public function whose type names an induction variable of its module would let another
/// module read or write it (`docs/chl-spec.md`, "9.10 Induction variables stay in their
/// module"), whether the module is checked on its own or is the root of a program that runs.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_read(
    indoc! {"
        pub def current(n: Int):
            cnt + n
    "},
    "has `Read(cnt)`"
)]
#[case::in_a_tuple("pub api = (\\n -> cnt + n, 0)\n", "has `Read(cnt)`")]
#[case::in_a_record("pub api = (read=\\n -> cnt + n)\n", "has `Read(cnt)`")]
#[case::in_a_returned_function(
    indoc! {r#"
        pub def maker(n: Int):
            \x -> cnt + x + n
    "#},
    "has `Read(cnt)`"
)]
#[case::a_write(
    indoc! {"
        def bump(c: Mut(Int)):
            c += 1
        pub def tick(n: Int):
            bump(cnt)
            n
    "},
    "has `Write(cnt)`"
)]
fn a_public_function_naming_an_induction_variable_is_refused(
    #[case] code: &str,
    #[case] needle: &str,
) {
    let code = format!("cnt := 0\nfor x in [1, 2]:\n    cnt += x\n{code}");
    let errors = errors_of(&code);
    assert!(errors.contains(needle), "{errors}");
    let errors = super::modules::compile_errors(&program(&format!("{code}0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// A transactional variable belongs to the run, so its capabilities name no variable, and it is
/// declared at a module's top level (`docs/chl-spec.md`, "Discharging requirements and
/// effects").
#[rstest]
#[case::in_a_def(
    indoc! {"
        pub def scratch(n: Int) => Int:
            c: Mut(Int, Txn) := 0
            with begin():
                c := c + n
            n
    "},
    "`c` is a transactional mutable variable, which belongs to the run, so it is declared at a \
     module's top level"
)]
#[case::in_a_branch(
    indoc! {"
        if True:
            c: Mut(Int, Txn) := 0
            with begin():
                c := 1
            await_final(c)
        else:
            0
    "},
    "`c` is a transactional mutable variable, which belongs to the run"
)]
#[case::in_a_match_arm(
    indoc! {"
        match `some(1):
            case `some(n):
                c: Mut(Int, Txn) := 0
                with begin():
                    c := n
                await_final(c)
    "},
    "`c` is a transactional mutable variable, which belongs to the run"
)]
#[case::named_in_a_clause(
    indoc! {"
        stock: Mut(Int, Txn) := 10
        pub def take(n: Int) => Int causes Write(stock):
            n
    "},
    "`Write(stock)` names no variable in scope of the kind it takes"
)]
fn a_transactional_variable_is_the_runs(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

/// Each node of a specialization has the capabilities of the use that minted it, its arguments'
/// included, and uses that differ in what they cause share no specialization: the call of
/// `apply`'s parameter commits in the clone `take` reaches and does nothing in the one `keep`
/// reaches, though both uses are at one type, and each reaches `apply` through a use in its own
/// clone of `apply_inside` (`src/ccl/design/type-inference.md`, "Capabilities on every expression").
#[test]
fn a_specialization_has_its_uses_effects() {
    use cambra::ccl::context::{Phase, compile_to};
    use cambra::ccl::{Expr, TypedExprNode};
    let code = indoc! {"
        stock: Mut(Int, Txn) := 10

        def take(n: Int):
            with begin():
                stock := stock - n

        def keep(n: Int):
            ()

        def apply(f, x):
            f(x)

        def apply_inside(f, x):
            apply(f, x)

        apply_inside(take, 1)
        apply_inside(keep, 1)
    "};
    /// The capabilities of each call of a function `apply`'s parameters hold.
    fn parameter_calls(e: &Expr, out: &mut Vec<String>) {
        if let TypedExprNode::Apply { function, .. } = &e.node
            && cambra::ccl::symbolic::symbolic(function).starts_with("__arg_tuple")
        {
            out.push(e.capabilities.to_string());
        }
        e.walk_children(|c| parameter_calls(c, out));
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    let expr = compile_to(&loaded, Phase::Infer).expect("the program compiles");
    let mut calls = Vec::new();
    parameter_calls(&expr, &mut calls);
    calls.sort();
    assert_eq!(
        calls,
        [
            "",
            " requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction"
        ]
    );
}

/// A read of a mutable variable is its mention's own capability, so it stays with the mention
/// wherever a pass moves it (`src/ccl/design/type-inference.md`, "Capabilities on every
/// expression").
#[test]
fn a_read_is_its_mentions_effect() {
    use cambra::ccl::context::{Phase, compile_to};
    use cambra::ccl::{Expr, TypedExprNode};
    let code = indoc! {"
        n: Mut(Int, Txn) := 0
        for r in [1, 2]:
            with begin():
                n := n + r
        await_final(n)
    "};
    fn mentions_of_n(e: &Expr, out: &mut Vec<String>) {
        if let TypedExprNode::Var(name) = &e.node
            && name.base() == "n"
        {
            out.push(e.capabilities.to_string());
        }
        e.walk_children(|c| mentions_of_n(c, out));
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    let expr = compile_to(&loaded, Phase::Infer).expect("the program compiles");
    let mut mentions = Vec::new();
    mentions_of_n(&expr, &mut mentions);
    assert_eq!(mentions, [" requires Transaction, ReadTxn(n)", ""]);
}

/// The run's transactional capabilities are written as they print.
#[rstest]
// No other module names a private variable, so the interface writes it as the module's own
// state.
#[case::a_def(
    indoc! {"
        stock: Mut(Int, Txn) := 10
        pub def take(n: Int) => Int requires ReadTxn(stock) causes WriteTxn(stock):
            n
    "},
    "pub take: Int => Int requires ReadTxn(Module::*) causes WriteTxn(Module::*)"
)]
fn transactional_capabilities_are_written(#[case] code: &str, #[case] line: &str) {
    let interface = interface_of(code);
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// The module that runs `helper`, whose `f` commits a write to its private `stock`, and passes
/// it to `lib`, whose parameter's entry for `f` is `entry`, above `root`.
fn passing_helper(entry: &str, root: &str) -> cambra::ccl::load::LoadedProgram {
    let main = indoc! {"
        run helper as h
        run lib(p=h) as l
    "};
    let lib = indoc! {"
        param p: Module{f: {entry}}
        pub def use_it(x: Int) => Int:
            p::f(x)
    "}
    .replace("{entry}", entry);
    program(
        &format!("{main}{root}"),
        &[
            ("lib", &lib),
            (
                "helper",
                indoc! {"
                    stock: Mut(Int, Txn) := 10
                    pub def f(x: Int) => Int:
                        with begin():
                            stock := stock - x
                        x
                "},
            ),
        ],
    )
}

/// A clause bounding what reaches a run's state names the run, `h::*`: `h`'s `stock` is within
/// it and within no other run's.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::the_run_written("h", None)]
#[case::another_run(
    "l",
    Some("this has `ReadTxn(h::stock)`, which the definition's clause")
)]
fn a_runs_state_bounds_a_clause(#[case] run: &str, #[case] refused: Option<&str>) {
    let root = indoc! {"
        def g(x: Int) => Int requires only ReadTxn({run}::*) causes only RunTransaction, WriteTxn({run}::*):
            h::f(x)
        g(1)
    "}
    .replace("{run}", run);
    let entry = "Int => Int requires ReadTxn(Module::*) causes WriteTxn(Module::*), RunTransaction";
    match refused {
        None => super::helpers::check_program_scalar(&passing_helper(entry, &root), Value::Int(1)),
        Some(needle) => super::modules::assert_refused(&passing_helper(entry, &root), needle),
    }
}

/// Checked on its own, a module's Module-typed parameter takes no run, so a call through it
/// reaches the parameter's state, `p::*`, which its interface writes.
#[test]
fn a_parameters_state_is_written_through_it() {
    let interface = interface_of(indoc! {"
        param p: Module{f: Int => Int requires ReadTxn(Module::*) causes WriteTxn(Module::*), RunTransaction}
        pub def use_it(x: Int) => Int:
            p::f(x)
    "});
    assert!(
        interface.lines().any(|l| l
            == "pub use_it: Int => Int requires ReadTxn(p::*) causes RunTransaction, WriteTxn(p::*)"),
        "{interface}"
    );
}

/// `Module::*` stands only in a Module type's entry, and `x::*` names a run.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::module_outside_a_module_type(
    indoc! {"
        def f(n: Int) causes WriteTxn(Module::*):
            n
    "},
    "`Module::*` is the state of the module a Module type describes"
)]
#[case::a_qualifier_naming_no_module(
    indoc! {"
        def f(n: Int) causes WriteTxn(q::*):
            n
    "},
    "`q` does not name a module here"
)]
fn a_runs_state_is_written_where_it_has_one(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

/// A top in a clause stands for every capability of its direction, `Effect` or `Context`, or of
/// its family, `Write(*)`; `except` takes capabilities and families out of it and out of a
/// clause variable's bound; and a set holds each capability once, through the widest top
/// holding it (`docs/chl-spec.md`, "Writing requirements and effects", "Kinds and bounds").
#[rstest]
#[case::every_effect(
    "pub def apply(f: (Int => Int causes Effect), x: Int) => Int causes Effect:\n    f(x)\n",
    "pub apply: {(Int => Int causes Effect), Int} => Int causes Effect"
)]
#[case::every_write(
    "pub def apply(f: (Int => Int causes Write(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Write(*)), Int} => Int causes Write(*)"
)]
#[case::every_append(
    "pub def apply(f: (Int => Int causes Append(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Append(*)), Int} => Int causes Append(*)"
)]
#[case::every_read(
    "pub def apply(f: (Int => Int requires Read(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int requires Read(*)), Int} => Int requires Read(*)"
)]
#[case::two_families(
    "pub def apply(f: (Int => Int causes Write(*), Append(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Write(*), Append(*)), Int} => Int causes Write(*), Append(*)"
)]
#[case::a_family_within_effect(
    "pub def apply(f: (Int => Int causes Effect, Write(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Effect), Int} => Int causes Effect"
)]
#[case::a_family_taken_from_effect(
    "pub def apply(f: (Int => Int causes Effect except Write(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Effect except Write(*)), Int} => Int causes Effect except \
     Write(*)"
)]
#[case::reads_taken_from_context(
    "pub def apply(f: (Int => Int requires Context except Read(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int requires Context except Read(*)), Int} => Int requires Context \
     except Read(*)"
)]
#[case::one_top_holding_what_another_takes_away(
    indoc! {"
        pub def both(f: (Int => Int causes Effect except Write(*)), g: (Int => Int causes Write(*)), x: Int) => Int:
            f(x) + g(x)
    "},
    "pub both: {(Int => Int causes Effect except Write(*)), (Int => Int causes Write(*)), Int} => \
     Int causes Effect"
)]
#[case::a_variable_beside_a_top_taking_away_on_its_own(
    indoc! {"
        pub def both(E <: Effect, f: (Int => Int causes E), g: (Int => Int causes Effect except RunTransaction), x: Int) => Int:
            f(x) + g(x)
    "},
    "pub both: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Effect except \
     RunTransaction), Int} => Int causes E, (Effect except RunTransaction)"
)]
#[case::a_variable_written_beside_every_write(
    indoc! {"
        pub def both(E <: Effect, f: (Int => Int causes E), g: (Int => Int causes Write(*)), x: Int) => Int:
            f(x) + g(x)
        pub h: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Write(*)), Int} => Int causes E, Write(*) = both
    "},
    "pub h: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Write(*)), Int} => Int \
     causes E, Write(*)"
)]
#[case::a_variable_taking_away(
    "pub def g(E <: Effect, f: (Int => Int causes E except RunTransaction), x: Int) => Int:\n    \
     f(x)\n",
    "pub g: forall (E <: Effect) {(Int => Int causes E except RunTransaction), Int} => Int causes \
     E except RunTransaction"
)]
#[case::a_variable_in_parentheses(
    "pub def g(E <: Effect, f: (Int => Int causes (E except AffectWorld)), x: Int) => Int:\n    \
     f(x)\n",
    "pub g: forall (E <: Effect) {(Int => Int causes E except AffectWorld), Int} => Int causes E \
     except AffectWorld"
)]
#[case::variables_taking_away_differently(
    indoc! {"
        pub def g(E <: Effect, F <: Effect, f: (Int => Int causes (E except RunTransaction), F), x: Int) => Int:
            f(x)
        pub h: forall (E <: Effect, F <: Effect) {(Int => Int causes (E except RunTransaction), F), Int} => Int causes (E except RunTransaction), F = g
    "},
    "pub h: forall (E <: Effect, F <: Effect) {(Int => Int causes (E except RunTransaction), F), \
     Int} => Int causes (E except RunTransaction), F"
)]
#[case::a_variable_taking_away_beside_a_top(
    indoc! {"
        pub def g(E <: Effect, f: (Int => Int causes E except RunTransaction), h: (Int => Int causes Write(*)), x: Int) => Int:
            f(x) + h(x)
    "},
    "pub g: forall (E <: Effect) {(Int => Int causes E except RunTransaction), (Int => Int causes \
     Write(*)), Int} => Int causes E, Write(*) except RunTransaction"
)]
#[case::a_clause_taking_from_its_variable_what_an_argument_does(
    "pub def apply(E <: Effect, f: (Int => Int causes E except RunTransaction), x: Int) => Int \
     causes only E except RunTransaction:\n    f(x)\n",
    "pub apply: forall (E <: Effect) {(Int => Int causes E except RunTransaction), Int} => Int \
     causes E except RunTransaction"
)]
#[case::a_top_in_parentheses(
    "pub def apply(f: (Int => Int requires (Context except ObserveWorld)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int requires Context except ObserveWorld), Int} => Int requires Context \
     except ObserveWorld"
)]
#[case::a_bounded_variable_within_a_top(
    "pub def apply(E <: Effect except RunTransaction, f: (Int => Int causes E), x: Int) => Int \
     causes only (Effect except RunTransaction):\n    f(x)\n",
    "pub apply: forall (E <: Effect except RunTransaction) {(Int => Int causes E), Int} => Int \
     causes Effect except RunTransaction"
)]
#[case::a_bound_taking_capabilities_away(
    "pub def apply(E <: Effect except (RunTransaction, AffectWorld), f: (Int => Int causes E), \
     x: Int) => Int causes only E:\n    f(x)\n",
    "pub apply: forall (E <: Effect except (RunTransaction, AffectWorld)) {(Int => Int causes E), \
     Int} => Int causes E"
)]
#[case::a_bound_taking_a_family_away(
    "pub def apply(E <: Effect except Write(*), f: (Int => Int causes E), x: Int) => Int causes \
     only E:\n    f(x)\n",
    "pub apply: forall (E <: Effect except Write(*)) {(Int => Int causes E), Int} => Int causes E"
)]
fn a_top_is_written(#[case] code: &str, #[case] line: &str) {
    let interface = interface_of(code);
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// What a top holds is checked like any capability, and a clause or a bound taking away what
/// none of its tops holds, or naming what is not a capability, is refused.
#[rstest]
#[case::a_commit_the_type_takes_away(
    indoc! {"
        stock: Mut(Int, Txn) := 0
        def commits(x: Int) => Int:
            with begin():
                stock := x
            x
        pub def apply(f: (Int => Int causes Effect except RunTransaction), x: Int) => Int:
            f(x)
        pub def bad(x: Int) => Int:
            apply(commits, x)
    "},
    "this has `RunTransaction`, which the function type it must have does not state"
)]
#[case::a_transactional_write_beyond_every_write(
    indoc! {"
        stock: Mut(Int, Txn) := 0
        def commits(x: Int) => Int:
            with begin():
                stock := x
            x
        pub def apply(f: (Int => Int causes Write(*)), x: Int) => Int:
            f(x)
        pub def bad(x: Int) => Int:
            apply(commits, x)
    "},
    "this has `WriteTxn(stock)`, which the function type it must have does not state"
)]
#[case::a_commit_the_bound_takes_away(
    indoc! {"
        stock: Mut(Int, Txn) := 0
        def commits(x: Int) => Int:
            with begin():
                stock := x
            x
        pub def apply(E <: Effect except RunTransaction, f: (Int => Int causes E), x: Int) => Int causes only E:
            f(x)
        pub def bad(x: Int) => Int:
            apply(commits, x)
    "},
    "this has `RunTransaction`, which the bound of the clause variable it reaches takes away"
)]
#[case::a_write_the_bound_takes_away(
    indoc! {"
        cnt := 0
        for x in [1, 2]:
            cnt += x
        def bump(x: Int) => Int:
            cnt += x
            x
        def apply(E <: Effect except Write(*), f: (Int => Int requires Read(*) causes E), x: Int) => Int causes only E:
            f(x)
        y = apply(bump, 1)
    "},
    "this has `Write(cnt)`, which the bound of the clause variable it reaches takes away"
)]
#[case::a_variable_beyond_a_top_taking_away(
    "pub def apply(E <: Effect, f: (Int => Int causes E), x: Int) => Int causes only Effect except \
     RunTransaction:\n    f(x)\n",
    "this has `E`, which the definition's clause, bounded by `only` or `nothing`, does not list"
)]
#[case::a_variable_beyond_its_clause_taking_less(
    "pub def apply(E <: Effect, f: (Int => Int causes E except RunTransaction), x: Int) => Int \
     causes only (E except AffectWorld):\n    f(x)\n",
    "this has `E except RunTransaction`, which the definition's clause, bounded by `only` or \
     `nothing`, does not list"
)]
#[case::a_function_beyond_a_variable_taking_away(
    indoc! {"
        stock: Mut(Int, Txn) := 0
        def commits(x: Int) => Int:
            with begin():
                stock := x
            x
        def apply(E <: Effect, f: (Int => Int causes E except RunTransaction), x: Int) => Int:
            f(x)
        pub def bad(x: Int) => Int:
            apply(commits, x)
    "},
    "this has `RunTransaction`, which the function type it must have does not state"
)]
#[case::a_capability_in_parentheses(
    "pub def g(f: (Int => Int causes (RunTransaction except AffectWorld)), x: Int) => Int:\n    \
     f(x)\n",
    "parentheses give a top or a clause variable an `except` of its own"
)]
#[case::a_top_in_parentheses_taking_nothing(
    "pub def g(f: (Int => Int causes (Write(*) except RunTransaction)), x: Int) => Int:\n    f(x)\n",
    "`except RunTransaction` takes nothing away"
)]
#[case::except_with_nothing_to_take(
    "pub def f(x: Int) => Int causes RunTransaction except AffectWorld:\n    x\n",
    "`except` takes capabilities out of a clause's variables and its tops"
)]
#[case::except_taking_nothing_from_its_tops(
    "pub def f(g: (Int => Int causes Write(*) except RunTransaction), x: Int) => Int:\n    g(x)\n",
    "`except RunTransaction` takes nothing away: no top of this clause holds any of it"
)]
#[case::except_taking_effect(
    "pub def f(g: (Int => Int causes Effect except Effect), x: Int) => Int:\n    g(x)\n",
    "`except` takes capabilities away, such as `RunTransaction` or `Write(*)`, not a clause \
     variable, `Effect`, `Context` or `_`"
)]
#[case::except_naming_no_variable(
    "pub def f(g: (Int => Int causes Write(*) except Write(q)), x: Int) => Int:\n    g(x)\n",
    "`Write(q)` names no variable in scope of the kind it takes"
)]
#[case::every_read_in_causes(
    "pub def f(g: (Int => Int causes Read(*)), x: Int) => Int:\n    g(x)\n",
    "`Read` is not an effect"
)]
#[case::every_write_in_requires(
    "pub def f(g: (Int => Int requires Write(*)), x: Int) => Int:\n    g(x)\n",
    "`Read(x)`, the tops `Context`, `ReadTxn(*)` and `Read(*)`, clause variables bounded by \
     `Context`"
)]
#[case::a_top_in_parentheses_taking_everything(
    indoc! {"
        pub def g(f: (Int => Int causes (Write(*) except Write(*))), x: Int) => Int:
            f(x)
    "},
    "this `except` takes away all of `Write(*)`, so it holds nothing"
)]
#[case::except_taking_everything_from_a_top(
    indoc! {"
        pub def g(f: (Int => Int causes Write(*), Append(*) except Write(*)), x: Int) => Int:
            f(x)
    "},
    "this `except` takes away all of `Write(*)`, so it holds nothing"
)]
fn a_top_is_checked(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

/// A capability that takes an argument takes a list, which is the capabilities it names
/// (`docs/chl-spec.md`, "Writing requirements and effects").
#[rstest]
#[case::writes(
    "causes RunTransaction, WriteTxn(stock, orders)",
    "causes RunTransaction, WriteTxn(stock), WriteTxn(orders)"
)]
#[case::reads(
    "requires ReadTxn(stock, orders)",
    "requires ReadTxn(stock), ReadTxn(orders)"
)]
#[case::taken_away(
    "causes Effect except WriteTxn(stock, orders)",
    "causes Effect except (WriteTxn(stock), WriteTxn(orders))"
)]
fn a_capability_takes_a_list(#[case] list: &str, #[case] items: &str) {
    let code = |clause: &str| {
        indoc! {"
            stock: Mut(Int, Txn) := 10
            orders: Mut(Int, Txn) := 0
            pub def apply(f: (Int => Int {clause}), x: Int) => Int:
                f(x)
        "}
        .replace("{clause}", clause)
    };
    assert_eq!(interface_of(&code(list)), interface_of(&code(items)));
}

/// Each capability a list names is in its clause, so a body writing both variables meets `only`
/// with a list naming both.
#[test]
fn a_list_bounds_a_clause() {
    interface_of(indoc! {"
        stock: Mut(Int, Txn) := 10
        orders: Mut(Int, Txn) := 0
        pub def take(n: Int) => Int causes only RunTransaction, WriteTxn(stock, orders):
            with begin():
                stock := stock - n
                orders := orders + n
            n
    "});
}

/// A top is written with `*`, so `_`, a hole in a clause, is refused as a capability's argument,
/// and a list naming a top beside what the top holds is refused.
#[rstest]
#[case::a_hole_for_a_top(
    "pub def f(g: (Int => Int causes Write(_)), x: Int) => Int:\n    g(x)\n",
    "`_` in a clause is a hole that inference fills, so a top is written with `*`: `Write(*)`"
)]
#[case::a_hole_for_a_runs_top(
    "pub def f(x: Int) => Int requires ReadTxn(h::_):\n    x\n",
    "a top is written with `*`: `ReadTxn(h::*)`"
)]
#[case::a_top_beside_what_it_holds(
    indoc! {"
        stock: Mut(Int, Txn) := 10
        pub def f(g: (Int => Int causes WriteTxn(*, stock)), x: Int) => Int:
            g(x)
    "},
    "`WriteTxn(*)` holds `WriteTxn(stock)`, so this list names it twice"
)]
#[case::a_top_twice(
    "pub def f(g: (Int => Int causes Write(*, *)), x: Int) => Int:\n    g(x)\n",
    "`Write(*)` holds `Write(*)`, so this list names it twice"
)]
fn a_capability_list_is_checked(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

/// A top holding writes or reads names every mutable variable, and one holding appends every
/// feed, so a function whose type holds one leaves no scope that binds what it names: a body
/// binding one, or a module whose top level binds an induction variable (`docs/chl-spec.md`,
/// "Discharging requirements and effects").
#[rstest]
#[case::effect_public_beside_an_induction_variable(
    "cnt := 0\nfor x in [1, 2]:\n    cnt += x\npub g: Int => Int causes Effect = \\x -> x\n",
    "`g` is public and its type has `Effect`"
)]
#[case::every_write_public_beside_an_induction_variable(
    "cnt := 0\nfor x in [1, 2]:\n    cnt += x\npub g: Int => Int causes Write(*) = \\x -> x\n",
    "`g` is public and its type has `Write(*)`"
)]
#[case::an_annotation_naming_an_induction_variable(
    "cnt := 0\nfor x in [1, 2]:\n    cnt += x\npub g: Int => Int causes Write(cnt) = \\x -> x\n",
    "`g` is public and its type has `Write(cnt)`"
)]
fn a_top_names_every_variable(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

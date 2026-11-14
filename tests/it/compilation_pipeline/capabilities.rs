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
    "requires r: Iterable(A), r::Elements <: C |=> D causes Append(out)"
)]
#[case(
    indoc! {"
        pub def take_listed(xs):
            [take(x) for x in xs]
    "},
    "take_listed",
    "requires r: Iterable(A), r::Elements <: C |=> D, ReadTxn(Module::*) causes RunTransaction, \
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
    "requires r: Iterable(A), r::Elements <: C |=> D, r1: Addable(B ∨ Int, D), r1::Output <: B, \
     Orderable(C, C)"
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
    "requires r: Iterable(A), r::Elements <: B |=> C"
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
    "requires r: Iterable(A), r::Elements <: B |=> C, Orderable(B, B)"
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
    "pub keep: forall (A) {A, Int} => Int  # callable in a constant"
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
#[case::a_requirement_its_block_discharges(
    indoc! {"
        stock: Mut(Int, Txn) := 10
        pub def with_txn(R <: Context, f: (Int => Int requires R, Transaction), x: Int) requires only R:
            with begin():
                stock := f(x)
    "},
    "pub with_txn: forall (R <: Context) {(Int => Int requires Transaction, R), Int} => {} \
     requires R causes RunTransaction, WriteTxn(Module::*)"
)]
#[case::a_declared_requirement_parameter(
    indoc! {"
        pub def with_ctx(R <: Context, f: (Int => Int requires R), x: Int) requires only R:
            f(x)
    "},
    "pub with_ctx: forall (R <: Context) {(Int => Int requires R), Int} => Int requires R"
)]
#[case::a_raised_nominal_type(
    indoc! {"
        pub type Negative = {qty: Int}
        pub def checked(qty: Int):
            if qty < 0:
                raise Negative::new((qty=qty))
            qty
    "},
    "pub checked: Int => Int causes Raise(main::Negative)"
)]
#[case::an_exception_the_definition_catches(
    indoc! {"
        pub def recover(E <: Effect, f: (Int => Int causes E, Raise(Int)), x: Int) => Int causes only E:
            try:
                f(x)
            except Int as e:
                e + 1
    "},
    "pub recover: forall (E <: Effect) {(Int => Int causes Raise(Int), E), Int} => Int causes E"
)]
#[case::a_raised_parameter(
    indoc! {"
        pub def f(x):
            raise x
    "},
    "pub f: forall (A, B) A => B causes Raise(A)"
)]
#[case::a_type_parameter_caught_by_itself(
    indoc! {"
        pub def g(A, x: A) => Int:
            try:
                raise x
            except A:
                1
    "},
    "pub g: forall (A) A => Int"
)]
#[case::a_raised_collection(
    indoc! {"
        pub def h(x: Int) => Int:
            if x > 1:
                raise [x, x]
            x
    "},
    "pub h: Int => Int causes Raise(Array(2, Int))"
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
// An ordering requirement over positions inference typed names them as the printed contract
// does, beside the requirement on the source it loops over.
#[case::an_inferred_ordering_requirement(
    indoc! {"
        def each(E <: Effect, f: (Int => Int causes E), xs) requires nothing causes E:
            for x in xs:
                f(x)
            0
    "},
    "this has `OrderableIfRequiredBy(B, E)`, which the definition's clause"
)]
#[case::the_source_of_an_inferred_ordering_requirement(
    indoc! {"
        def each(E <: Effect, f: (Int => Int causes E), xs) requires nothing causes E:
            for x in xs:
                f(x)
            0
    "},
    "this has `r: Iterable(A), r::Elements <: B |=> Int`, which the definition's clause"
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

/// A clause naming no variable is reported at the item naming it, which no node of the tree
/// stands for, rather than at the whole definition.
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
    assert_eq!(&code[span.start..span.end], "Write(nope)");
}

/// A clause form this compiler does not implement yet, and one written where it cannot stand,
/// is refused where it is written.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_exception_without_its_type(
    indoc! {"
        def f(n: Int) causes Raise:
            n
    "},
    "`Raise` takes one type"
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

/// A trait whose instances write state through an associated effect type, an instance that
/// writes the transactional variable its call passes, and a polymorphic definition calling the
/// trait. An instance reaches no variable of its module: the caller's is its argument.
const TAKE: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    type Box = Int

    trait Take(T):
        Writes <: Effect
        def take(t: T, s: Mut(Int, Txn), n: Int) => Int causes RunTransaction, Writes

    instance Take(Box):
        def take(t, s, n):
            with begin():
                s := s - n
            n

    def generic(T, a: T, s: Mut(Int, Txn), n: Int) requires t: Take(T) causes only RunTransaction, t::Writes:
        t::take(a, s, n)
"};

/// A checked module prints a trait's associated effect types and its functions' clauses, and a
/// requirement by the name its associated effect type is read through. What an instance's
/// function causes that its signature lists is the signature's, so it does not reach the
/// associated effect type, whose bound takes away `RunTransaction` here (`docs/chl-spec.md`,
/// "Effects in traits").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_prints_what_its_traits_cause() {
    let interface = interface_of(indoc! {"
        pub type Box = Int
        pub trait Take(T):
            Writes <: Effect except RunTransaction
            def take(t: T, s: Mut(Int, Txn), n: Int) => Int causes RunTransaction, Writes
        instance Take(Box):
            def take(t, s, n):
                with begin():
                    s := s - n
                n
        pub def generic(T, a: T, s: Mut(Int, Txn), n: Int) requires t: Take(T):
            t::take(a, s, n)
    "});
    assert_eq!(
        interface,
        indoc! {"
            module main
            pub type Box = Int
            pub trait Take(T):
                Writes <: Effect except RunTransaction
                take: {T, Mut(Int, Txn), Int} => Int causes RunTransaction, Writes
            pub generic: forall (T) {T, Mut(Int, Txn), Int} => Int requires t: Take(T) causes RunTransaction, t::Writes
        "}
    );
}

/// An operator's signature is the compiler's, so an instance's function doing more than it lists
/// is refused with no label at the signature and no hint to add an associated type, which a
/// compiler trait does not take.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_operator_instance_beyond_its_signature_is_refused_at_the_call() {
    let errors = super::modules::compile_errors(&program(
        indoc! {"
            type Money = Int
            def shout(n: Int) => Int causes AffectWorld:
                n
            instance Addable(Money, Money):
                Output = Money
                def add(a, b):
                    Money::new(shout(1))
            0
        "},
        &[],
    ));
    assert!(
        errors.contains("this has `AffectWorld`, which the trait's signature does not list"),
        "{errors}"
    );
    assert!(!errors.contains("associated type"), "{errors}");
    assert!(!errors.contains("main.cambra:1:1"), "{errors}");
}

/// An unnamed requirement's associated effect type is named through a binder printing picks, so
/// two requirements of one trait keep their members apart (`docs/chl-spec.md`, "Effects in
/// traits").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_names_each_unnamed_requirement() {
    let interface = interface_of(indoc! {"
        pub type Box = Int
        pub trait Act(T):
            Does <: Effect
            def act(t: T) => Int causes Does
        instance Act(Box):
            def act(t):
                1
        pub def go(T, U, x: T, y: U) => Int requires Act(T), Act(U):
            summon(Act(T))::act(x) + summon(Act(U))::act(y)
    "});
    assert!(
        interface.contains(
            "pub go: forall (T, U) {T, U} => Int requires r: Act(T), r1: Act(U) causes r::Does, \
             r1::Does"
        ),
        "{interface}"
    );
}

/// What a call of a trait's function does is its signature's, and what an instance's
/// function does beyond it is the instance's associated effect type, which a call at that
/// instance does (`docs/chl-spec.md`, "Effects in traits").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_call_at_an_instance(
    indoc! {"
        def direct(n: Int) causes only RunTransaction:
            summon(Take(Box))::take(Box::new(1), stock, n)
    "},
    "this has `WriteTxn(stock)`, which the definition's clause"
)]
#[case::a_call_through_a_requirement(
    indoc! {"
        def through(n: Int) causes only RunTransaction:
            generic(Box::new(1), stock, n)
    "},
    "this has `WriteTxn(stock)`, which the definition's clause"
)]
// A requirement inference adds to a definition is answered at each use, by the instance the
// use selects.
#[case::a_call_through_an_inferred_requirement(
    indoc! {"
        def inferred(a, s: Mut(Int, Txn), n: Int):
            summon(Take(_))::take(a, s, n)
        def through_inferred(n: Int) causes only RunTransaction:
            inferred(Box::new(1), stock, n)
    "},
    "this has `WriteTxn(stock)`, which the definition's clause"
)]
#[case::a_requirement_beyond_its_bound(
    indoc! {"
        def narrow(T, a: T, s: Mut(Int, Txn), n: Int) requires t: Take(T) causes only RunTransaction:
            t::take(a, s, n)
    "},
    "this has `t::Writes`, which the definition's clause"
)]
fn a_trait_call_does_what_its_instance_does(#[case] code: &str, #[case] needle: &str) {
    let errors = super::modules::compile_errors(&program(&format!("{TAKE}\n{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// A module whose `inferred` leaves its `Take` requirement to inference, and an instance that
/// does nothing; the root declares another that commits.
const INFERRED_LIB: &str = indoc! {"
    pub type Pure = Int
    pub trait Take(T):
        Writes <: Effect
        def take(t: T, s: Mut(Int, Txn), n: Int) => Int causes Writes
    instance Take(Pure):
        def take(t, s, n):
            n
    pub def inferred(a, s: Mut(Int, Txn), n: Int):
        summon(Take(_))::take(a, s, n)
"};

/// A requirement inference adds to a definition states a member for each associated effect type
/// of its trait, as a written one does, so the interface shows that a call does what the instance
/// it selects does (`docs/chl-spec.md`, "Effects in traits").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_inferred_requirement_states_its_associated_effect_types() {
    let interface = interface_of(INFERRED_LIB);
    assert!(
        interface.contains(
            "pub inferred: forall (A) {A, Mut(Int, Txn), Int} => Int requires r: Take(A) causes \
             r::Writes"
        ),
        "{interface}"
    );
}

/// Each use of a definition with an inferred requirement does what the instance it selects
/// does, and no other instance's effects: a use selecting the instance that does nothing stays
/// under `causes only WriteTxn(stock)`, and one selecting the committing instance does not.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::the_pure_instance("lib::Pure::new(1)", None)]
#[case::the_committing_instance(
    "Box::new(1)",
    Some("this has `RunTransaction`, which the definition's clause")
)]
fn an_inferred_requirement_does_what_each_use_selects(
    #[case] argument: &str,
    #[case] refused: Option<&str>,
) {
    let root = format!(
        "{}    lib::inferred({argument}, stock, n)\nvia(3)\n",
        indoc! {"
            import lib
            stock: Mut(Int, Txn) := 10
            type Box = Int
            instance lib::Take(Box):
                def take(t, s, n):
                    with begin():
                        s := s - n
                    n
            def via(n: Int) causes only WriteTxn(stock):
        "}
    );
    let loaded = program(&root, &[("lib", INFERRED_LIB)]);
    match refused {
        None => super::helpers::check_program_scalar(&loaded, cambra::interpreter::Value::Int(3)),
        Some(needle) => {
            let errors = super::modules::compile_errors(&loaded);
            assert!(errors.contains(needle), "{errors}");
        }
    }
}

/// A program calling an instance whose function writes state, directly and through a
/// requirement, compiles and runs.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::directly("summon(Take(Box))::take(Box::new(1), stock, 3)")]
#[case::through_a_requirement("generic(Box::new(1), stock, 3)")]
fn a_trait_whose_instance_writes_state_runs(#[case] call: &str) {
    super::helpers::check_program_scalar(
        &program(&format!("{TAKE}\n{call}\n"), &[]),
        cambra::interpreter::Value::Int(3),
    );
}

/// A trait's declarations that cannot state what instances do are refused where they are
/// written.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_instance_beyond_its_signature(
    indoc! {"
        type Box = Int
        trait Take(T):
            def take(t: T, s: Mut(Int, Txn), n: Int) => Int
        instance Take(Box):
            def take(t, s, n):
                with begin():
                    s := s - n
                n
    "},
    "this has `RunTransaction`, which the trait's signature does not list"
)]
#[case::a_signature_naming_a_variable(
    indoc! {"
        count := 0
        trait Take(T):
            def take(t: T, n: Int) => Int causes Write(count)
    "},
    "a trait's signature names no variable"
)]
#[case::an_instance_writing_a_clause(
    indoc! {"
        type Box = Int
        trait Take(T):
            def take(t: T, n: Int) => Int
        instance Take(Box):
            def take(t, n) causes nothing:
                n
    "},
    "so it writes no clause"
)]
#[case::a_hole_in_a_signature(
    indoc! {"
        trait App(T):
            def app(t: T, n: Int) => Int causes _
    "},
    "`_` in the signature of `App::app`"
)]
#[case::a_hole_in_a_function_type_in_a_signature(
    indoc! {"
        trait App(T):
            def app(t: T, f: (Int => Int requires _ causes _), n: Int) => Int
    "},
    "`_` in the signature of `App::app`"
)]
#[case::an_effect_bounded_parameter_of_a_trait_function(
    indoc! {"
        trait App(T):
            def app(E <: Effect, t: T, f: (Int => Int causes E), n: Int) => Int
    "},
    "a trait function's type parameters take neither yet"
)]
#[case::an_associated_effect_type_of_no_requirement(
    indoc! {"
        def f(n: Int) causes s::Writes:
            n
    "},
    "`s` names no requirement in scope"
)]
fn a_trait_declaration_that_cannot_state_effects_is_refused(
    #[case] code: &str,
    #[case] needle: &str,
) {
    let errors = super::modules::compile_errors(&program(&format!("{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// `Module::*` in a Module type's entry is the state of the run the parameter takes, so the
/// run `h` meets it, and a call through the parameter writes `h`'s state
/// (`docs/chl-spec.md`, "Writing requirements and effects").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_module_entry_states_the_runs_own_state() {
    super::helpers::check_program_scalar(
        &passing_helper(
            "Int => Int requires ReadTxn(Module::*) causes WriteTxn(Module::*), RunTransaction",
            "l::use_it(1)",
        ),
        Value::Int(1),
    );
}

/// A Module type's entry is a written type, whose clauses are exact, so a run whose argument
/// does more is refused at the argument (`docs/chl-spec.md`, "Writing requirements and
/// effects").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_module_argument_beyond_its_entry_is_refused() {
    let errors = super::modules::compile_errors(&program(
        indoc! {"
            run helper as h
            run lib(p=h) as l
            l::use_it(1)
        "},
        &[
            (
                "lib",
                indoc! {"
                    param p: Module{f: Int => Int}
                    pub def use_it(x: Int) => Int:
                        p::f(x)
                "},
            ),
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
    ));
    assert!(
        errors.contains("this has `ReadTxn(h::stock)`, which the function type it must have"),
        "{errors}"
    );
}

/// A function returning a function that requires or causes something naming a variable the
/// returning function binds is refused: the returned function would outlive the variable.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_read(
    indoc! {"
        def counter(start: Int):
            c := start
            \\x -> c + x
    "},
    "this returns a function that has `Read(c)`"
)]
#[case::through_a_record(
    indoc! {"
        def counter(start: Int):
            c := start
            (get=\\x -> c + x, n=1)
    "},
    "this returns a function that has `Read(c)`"
)]
fn a_function_returning_a_closure_over_its_variable_is_refused(
    #[case] code: &str,
    #[case] needle: &str,
) {
    let errors = super::modules::compile_errors(&program(&format!("{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
    // The error is at the value returned, beside the function returning it.
    assert!(errors.contains("main.cambra:3:"), "{errors}");
    assert!(errors.contains("returned by this function"), "{errors}");
}

/// A write or an append handing a variable a function that names a variable whose scope ends
/// first is refused: the variable would hold the function past that scope
/// (`docs/chl-spec.md`, "Discharging requirements and effects").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::written_to_a_parameter(
    indoc! {"
        def stash(m: Mut(_)):
            c := 1
            m := \\x -> c + x
        f := \\x -> x
        stash(f)
    "},
    "this writes to `m` a function that has `Read(c)`"
)]
#[case::appended_to_a_feed(
    indoc! {"
        fs: Feed(_)
        def push(n: Int):
            c := n
            fs << (\\x -> c + x)
        push(1)
    "},
    "this appends to `fs` a function that has `Read(c)`"
)]
fn a_function_handed_to_an_outer_variable_is_refused(#[case] code: &str, #[case] needle: &str) {
    let errors = super::modules::compile_errors(&program(&format!("{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// A returned function naming only what outlives the returning function, a parameter's
/// value, is kept.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_parameter(indoc! {"
    def adder(n: Int):
        \\x -> x + n
    f = adder(1)
    f(2)
"})]
fn a_returned_closure_over_what_outlives_it_is_kept(#[case] root: &str) {
    super::helpers::check_program_scalar(&program(root, &[]), cambra::interpreter::Value::Int(3));
}

/// A program whose `in_txn` calls its parameter inside a block.
const IN_TXN: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    def taken(n: Int) => Int:
        with begin():
            stock := stock - n
        n
    def in_txn(f, x: Int):
        with begin():
            stock := stock - f(x)
"};

/// A commit inside a `with begin():` block's body is refused, including a call of a function a
/// polymorphic definition takes as a parameter, which each use decides: each use passing a
/// committing function is refused there, with the call in the definition and its block as
/// secondary labels (`docs/chl-spec.md`, "8.2 Transactions: `with begin():`").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_commit_through_a_polymorphic_definition_is_refused_at_each_use() {
    let errors = super::modules::compile_errors(&program(
        &format!("{IN_TXN}\nin_txn(taken, 1)\nin_txn(taken, 2)\n0\n"),
        &[],
    ));
    for at in ["main.cambra:9:1", "main.cambra:10:1"] {
        assert!(errors.contains(at), "{errors}");
    }
    assert_eq!(
        errors
            .matches("this passes a function that commits a transaction")
            .count(),
        2,
        "{errors}"
    );
    assert!(errors.contains("this commits"), "{errors}");
    assert!(errors.contains("inside this block"), "{errors}");
}

/// A use passing a function that does not commit compiles, beside the definition that would
/// refuse a committing one.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_pure_function_through_a_polymorphic_block_runs() {
    super::helpers::check_program_scalar(
        &program(
            &format!("{IN_TXN}\nin_txn(\\x -> x, 1)\nawait_final(stock)\n"),
            &[],
        ),
        cambra::interpreter::Value::Int(9),
    );
}

/// A call inside a block of a function whose type holds a top holding `RunTransaction` is
/// refused: the top says what the call may do, so the error names it rather than a commit.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_top_holding_a_commit_inside_a_block_is_refused() {
    let errors = super::modules::compile_errors(&program(
        indoc! {"
            stock: Mut(Int, Txn) := 10
            def tops(f: (Int => Int causes Effect), x: Int):
                with begin():
                    stock := stock - f(x)
            0
        "},
        &[],
    ));
    assert!(
        errors.contains("this has `Effect`, which holds `RunTransaction`, so it may commit"),
        "{errors}"
    );
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

/// Transactional capabilities are written in a `def`'s clauses naming the variable, and in a
/// trait's signature as the tops, since a signature names no variable.
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
#[case::a_trait_signature(
    indoc! {"
        stock: Mut(Int, Txn) := 10
        type Box = Int
        trait Take(T):
            def take(t: T, s: Mut(Int, Txn), n: Int) => Int requires ReadTxn(*) causes WriteTxn(*), RunTransaction
        instance Take(Box):
            def take(t, s, n):
                with begin():
                    s := s - n
                n
        pub def run_take(n: Int) => Int:
            summon(Take(Box))::take(Box::new(1), stock, n)
    "},
    "pub run_take: Int => Int requires ReadTxn(*) causes RunTransaction, WriteTxn(*)"
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
#[case::an_associated_bound_taking_capabilities_away(
    indoc! {"
        trait Act(T):
            Does <: Effect except RunTransaction
            def act(t: T) => Int causes Does
        type Box = Int
        instance Act(Box):
            def act(t):
                3
        pub def go(x: Int) => Int:
            summon(Act(Box))::act(Box::new(x))
    "},
    "pub go: Int => Int"
)]
#[case::returned_naming_no_variable(
    indoc! {"
        pub def maker(f: (Int => Int causes Effect except (Write(*), Append(*)))) => Int => Int causes Effect except (Write(*), Append(*)):
            c := 0
            for x in [1, 2]:
                c += x
            \\x -> f(x) + 1
    "},
    "pub maker: (Int => Int causes Effect except (Write(*), Append(*))) => Int => Int causes \
     Effect except (Write(*), Append(*))"
)]
#[case::returned_naming_only_feeds(
    indoc! {"
        pub def maker(f: (Int => Int causes Append(*))) => Int => Int causes Append(*):
            c := 0
            for x in [1, 2]:
                c += x
            \\x -> f(x) + 1
    "},
    "pub maker: (Int => Int causes Append(*)) => Int => Int causes Append(*)"
)]
#[case::a_loop_running_appends(
    indoc! {"
        def loop_over(f: (Int => Int causes Append(*)), xs):
            for x in xs:
                f(x)
            0
        pub def go(a, b) => Int:
            loop_over(\\y -> y, a ++ b)
    "},
    "pub go: forall (A, B) {A => Int, B => Int} => Int causes Append(*)"
)]
#[case::a_block_discharging_from_context(
    indoc! {"
        pub def apply(f: (Int => Int requires Context causes Effect except RunTransaction), x: Int) => Int:
            with begin():
                f(x)
            x
    "},
    "pub apply: {(Int => Int requires Context causes Effect except RunTransaction), Int} => Int \
     requires Context except Transaction causes Effect"
)]
#[case::a_top_level_requiring_context_but_a_transaction(
    "g: Int => Int requires Context except Transaction = \\x -> x\ny = g(1)\n",
    "run, since its top level requires `Context except Transaction`"
)]
#[case::every_raise(
    "pub def apply(f: (Int => Int causes Raise(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Raise(*)), Int} => Int causes Raise(*)"
)]
#[case::a_raise_within_every_raise(
    "pub def apply(f: (Int => Int causes Raise(Int), Raise(*)), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Raise(*)), Int} => Int causes Raise(*)"
)]
#[case::a_raise_taken_from_every_raise(
    "pub def apply(f: (Int => Int causes Write(*), Raise(*) except Raise(Int)), x: Int) => Int:\n    \
     f(x)\n",
    "pub apply: {(Int => Int causes Write(*), Raise(*) except Raise(Int)), Int} => Int causes \
     Write(*), Raise(*) except Raise(Int)"
)]
#[case::a_variable_beside_a_raise_top_written_back(
    indoc! {"
        pub def both(E <: Effect, f: (Int => Int causes E), g: (Int => Int causes (Raise(*) except Raise(Int))), x: Int) => Int causes E, (Raise(*) except Raise(Int)):
            f(x) + g(x)
        pub h: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Raise(*) except Raise(Int)), Int} => Int causes E, (Raise(*) except Raise(Int)) = both
    "},
    "pub h: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Raise(*) except \
     Raise(Int)), Int} => Int causes E, (Raise(*) except Raise(Int))"
)]
#[case::a_raise_held_by_a_wider_one(
    indoc! {"
        def thrower(x: Int) => Int:
            raise 5
        pub def both(E <: Effect, f: (Int => Int causes E), x: Int) => Int:
            f(x) + thrower(x)
        pub h: forall (E <: Effect) {(Int => Int causes E), Int} => Int causes E, Raise(Int) = both
    "},
    "pub h: forall (E <: Effect) {(Int => Int causes E), Int} => Int causes Raise(Int), E"
)]
#[case::raises_of_one_type_from_two_sites(
    "g: Int => Int causes Raise(Int) = \\x -> x\npub h: Int => Int causes Raise(Int) = g\n",
    "pub h: Int => Int causes Raise(Int)"
)]
#[case::raises_taken_from_effect_caught_by_type(
    indoc! {"
        pub def safe(f: (Int => Int causes Raise(Int), Effect except Raise(*)), x: Int) => Int:
            try:
                f(x)
            except Int:
                0
    "},
    "pub safe: {(Int => Int causes Raise(Int), Effect except Raise(*)), Int} => Int causes Effect \
     except Raise(*)"
)]
#[case::a_loop_running_effect_but_writes_and_raises(
    indoc! {"
        def loop_over(f: (Int => Int causes Effect except (Write(*), Raise(*))), xs):
            for x in xs:
                f(x)
            0
        pub def go(a, b) => Int:
            loop_over(\\y -> y, a ++ b)
    "},
    "pub go: forall (A, B) {A => Int, B => Int} => Int causes Effect except (Write(*), Raise(*))"
)]
#[case::returned_raising(
    indoc! {"
        pub def maker(f: (Int => Int causes Raise(*))) => Int => Int causes Raise(*):
            c := 0
            for x in [1, 2]:
                c += x
            \\x -> f(x) + 1
    "},
    "pub maker: (Int => Int causes Raise(*)) => Int => Int causes Raise(*)"
)]
#[case::public_raising_beside_an_induction_variable(
    "cnt := 0\nfor x in [1, 2]:\n    cnt += x\npub g: Int => Int causes Raise(*) = \\x -> x\n",
    "pub g: Int => Int causes Raise(*)"
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
#[case::a_transaction_beyond_every_read(
    indoc! {"
        stock: Mut(Int, Txn) := 0
        def reads(x: Int) => Int requires Transaction:
            stock + x
        pub def apply(f: (Int => Int requires Read(*)), x: Int) => Int:
            f(x)
        pub def bad(x: Int) => Int:
            apply(reads, x)
    "},
    "this has `Transaction`, which the function type it must have does not state"
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
#[case::an_associated_type_bound_taking_capabilities(
    indoc! {"
        trait Sized(T):
            Size <: Int except RunTransaction
            def size(t: T) => Size
    "},
    "`except` takes capabilities out of a bound of `Effect` or `Context`, and this bound is a type"
)]
#[case::a_block_around_effect(
    indoc! {"
        pub def apply(f: (Int => Int causes Effect), x: Int) => Int:
            with begin():
                f(x)
            x
    "},
    "transactions do not nest"
)]
#[case::a_top_level_requiring_context(
    "g: Int => Int requires Context = \\x -> x\ny = g(1)\n",
    "this requires `Transaction` outside a `with begin():` block"
)]
#[case::a_raise_the_type_takes_away(
    indoc! {"
        def thrower(x: Int) => Int:
            raise 5
        pub def apply(f: (Int => Int causes Effect except Raise(Int)), x: Int) => Int:
            f(x)
        pub def bad(x: Int) => Int:
            apply(thrower, x)
    "},
    "this has `Raise({Int where _ == 5})`, which the function type it must have does not state"
)]
#[case::an_instance_beyond_its_associated_bound(
    indoc! {"
        trait Act(T):
            Does <: Effect except Raise(*)
            def act(t: T) => Int causes Does
        type Box = Int
        instance Act(Box):
            def act(t):
                raise 3
    "},
    "this has `Raise({Int where _ == 3})`, which the bound of the clause variable it reaches takes \
     away"
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
#[case::effect_returned_from_a_body_binding_a_variable(
    indoc! {"
        def maker(f: (Int => Int causes Effect)) => Int => Int causes Effect:
            c := 0
            for x in [1, 2]:
                c += x
            \\x -> f(x) + 1
    "},
    "which names every variable, a variable this function binds among them"
)]
#[case::every_write_returned_from_a_body_binding_a_variable(
    indoc! {"
        def maker(f: (Int => Int causes Write(*))) => Int => Int causes Write(*):
            c := 0
            for x in [1, 2]:
                c += x
            \\x -> f(x) + 1
    "},
    "this returns a function that has `Write(*)`, which names every variable"
)]
#[case::every_read_returned_from_a_body_binding_a_variable(
    indoc! {"
        def maker(f: (Int => Int requires Read(*))) => Int => Int requires Read(*):
            c := 0
            for x in [1, 2]:
                c += x
            \\x -> f(x) + 1
    "},
    "this returns a function that has `Read(*)`, which names every variable"
)]
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

/// A top holding what makes iterations interact orders a loop running it, so a loop over a
/// concatenation is refused (`docs/chl-spec.md`, "Ordered loops").
#[rstest]
#[case::effect("Effect")]
#[case::every_write("Write(*)")]
#[case::every_raise("Raise(*)")]
fn a_top_orders_a_loop(#[case] top: &str) {
    let errors = errors_of(&format!(
        "def loop_over(f: (Int => Int causes {top}), xs):\n    for x in xs:\n        f(x)\n    \
         0\npub def go(a, b) => Int:\n    loop_over(\\y -> y, a ++ b)\n"
    ));
    assert!(
        errors.contains(&format!(
            "since its body causes `{top}`, but this source has the positions of a concatenation"
        )),
        "{errors}"
    );
}

/// A clause variable bounded by `Effect` may hold `Raise(*)`, so a `try` around a call causing it
/// is refused as one around `Raise(*)` is, naming the variable, whatever a use passes
/// (`docs/chl-spec.md`, "Exceptions").
#[test]
fn a_try_around_a_raising_clause_variable_names_it() {
    let errors = errors_of(indoc! {"
        def recover(E <: Effect, f: (Int => Int causes E), x: Int) => Int causes E:
            try:
                f(x)
            except Int as e:
                e + 1
    "});
    assert!(
        errors.contains(
            "this `except Int` is around a call that may cause `E`, whose bound holds `Raise(*)`"
        ),
        "{errors}"
    );
}

/// `Effect` and `Raise(*)` raise every type: a `try` around either catches nothing, and a top
/// level calling either raises past the program (`docs/chl-spec.md`, "Exceptions").
#[rstest]
#[case::effect("Effect")]
#[case::every_raise("Raise(*)")]
fn a_top_raises_every_type(#[case] top: &str) {
    let errors = errors_of(&format!(
        "pub def safe(f: (Int => Int causes {top}), x: Int) => Int:\n    try:\n        f(x)\n    \
         except Int:\n        0\n"
    ));
    assert!(
        errors.contains(&format!(
            "this `except Int` is around a call that may cause `{top}`, which raises every type"
        )),
        "{errors}"
    );
    let errors = errors_of(&format!("g: Int => Int causes {top} = \\x -> x\ng(1)\n"));
    assert!(
        errors.contains(&format!("this raises `{top}`, which nothing catches")),
        "{errors}"
    );
}

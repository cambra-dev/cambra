//! What a function requires and causes, as inference collects it and a module's interface
//! prints it (`docs/chl-spec.md`, "6.9 Capabilities";
//! `src/ccl/design/type-inference.md`, "Effect variables").

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

/// The `causes` clause after the codomain of `member`'s contract, as `cambra check` prints it:
/// the last one on the line, after any a parameter's type writes.
fn clauses_of(code: &str, member: &str) -> String {
    let interface = interface_of(&format!("{PRELUDE}\n{code}"));
    let prefix = format!("pub {member}: ");
    let line = interface
        .lines()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("no `{member}` in the interface:\n{interface}"));
    match line.rfind(" causes ") {
        Some(at) => line[at + 1..].to_owned(),
        None => String::new(),
    }
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// A `with begin():` block commits, and its write is of the module's own state, which the
// interface writes `Module::_` since no other module names the private `stock`.
#[case("", "take", "causes RunTransaction, WriteTxn(Module::_)")]
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
    "causes RunTransaction, WriteTxn(Module::_)"
)]
// A loop body runs where the loop stands, and so does a comprehension's element.
#[case(
    indoc! {"
        pub def report_all(xs):
            for x in xs:
                out << x
    "},
    "report_all",
    "causes Append(out)"
)]
#[case(
    indoc! {"
        pub def take_listed(xs):
            [take(x) for x in xs]
    "},
    "take_listed",
    "causes RunTransaction, WriteTxn(Module::_)"
)]
// Each use of a polymorphic function collects its own effects, so a call that passes it a
// committing function commits and one that passes it a pure function does not.
#[case(
    indoc! {"
        pub def committing_use(x: Int):
            apply(take, x)
    "},
    "committing_use",
    "causes RunTransaction, WriteTxn(Module::_)"
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
    ""
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
    ""
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
    ""
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
    "causes RunTransaction, WriteTxn(Module::_)"
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
    "causes RunTransaction, WriteTxn(Module::_)"
)]
// A written function type's clauses are exact, so a function meeting them is passed, and the
// call does what the type states.
#[case(
    indoc! {"
        def call_with(f: Int => Int requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction, x: Int):
            f(x)
        pub def call_taken(n: Int):
            call_with(taken, n)
    "},
    "call_taken",
    "causes RunTransaction, WriteTxn(Module::_)"
)]
// A parameter's `_` is what each call passes.
#[case(
    indoc! {"
        def call_with(f: Int => Int requires _ causes _, x: Int):
            f(x)
        pub def via_hole(n: Int):
            call_with(taken, n)
    "},
    "via_hole",
    "causes RunTransaction, WriteTxn(Module::_)"
)]
// A declared parameter is what each call passes.
#[case(
    indoc! {"
        def call_all(R <: Context, E <: Effect, f: Int => Int requires R causes E, x: Int) causes only E:
            f(x)
        pub def via_param(n: Int):
            call_all(taken, n)
    "},
    "via_param",
    "causes RunTransaction, WriteTxn(Module::_)"
)]
// A `let` annotation's `_` is what its value fills.
#[case(
    indoc! {"
        g: Int => Int requires _ causes _ = taken
        pub def via_g(n: Int):
            g(n)
    "},
    "via_g",
    "causes RunTransaction, WriteTxn(Module::_)"
)]
fn a_contract_states_what_the_function_causes(
    #[case] code: &str,
    #[case] member: &str,
    #[case] expected: &str,
) {
    assert_eq!(clauses_of(code, member), expected);
}

/// A function whose effects are what a function argument's are is polymorphic in them, and
/// its contract names each part a written clause leaves open (`docs/chl-spec.md`, "Writing
/// requirements and effects").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_called_parameter(
    "pub def call(f, x):\n    f(x)\n",
    "pub call: forall (A, B, R <: Context, E <: Effect) {(A => B requires R causes E), A} => \
     B requires R causes E"
)]
#[case::a_hole_in_a_written_parameter_type(
    "pub def call_with(f: Int => Int causes _, x: Int):\n    f(x)\n",
    "pub call_with: forall (E <: Effect) {(Int => Int causes E), Int} => Int causes E"
)]
#[case::a_parameter_called_twice(
    "pub def twice(f, x: Int) => Int:\n    f(f(x))\n",
    "pub twice: forall (R <: Context, E <: Effect) {(Int => Int requires R causes E), Int} => Int \
     requires R causes E"
)]
#[case::a_parameter_never_called(
    "pub def keep(f, x: Int):\n    x\n",
    "pub keep: forall (A) {A, Int} => Int"
)]
#[case::a_returned_function(
    "pub def compose(f, g):\n    \\x -> g(f(x))\n",
    "pub compose: forall (A, B, C, R <: Context, E <: Effect, R1 <: Context, E1 <: Effect) \
     {(A => B requires R causes E), (B => C requires R1 causes E1)} => A => C requires R, R1 \
     causes E, E1"
)]
#[case::a_declared_effect_parameter(
    "pub def call_all(E <: Effect, f: Int => Int causes E, x: Int) causes only E:\n    f(x)\n",
    "pub call_all: forall (E <: Effect) {(Int => Int causes E), Int} => Int causes E"
)]
#[case::a_declared_requirement_parameter(
    "pub def with_ctx(R <: Context, f: Int => Int requires R, x: Int) requires only R:\n    \
     f(x)\n",
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
            def call_with(f: Int => Int causes _, x: Int):
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
        def f(E <: Effect, g: Int => Int causes E, n: Int) causes only E:
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

/// A clause form this compiler does not implement yet, and one written where it cannot stand,
/// is refused where it is written.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_exception(
    "def f(n: Int) causes Raise(Int):\n    n\n",
    "`Raise` is not supported yet"
)]
#[case::an_effect_variable("def f(n: Int) causes E:\n    n\n", "`E` is not an effect")]
#[case::a_hole_under_only(
    "def f(n: Int) causes only _:\n    n\n",
    "`only` makes a clause an upper bound"
)]
#[case::a_trait_requirement_in_a_function_type(
    "def call_with(f: Int => Int requires Orderable(Int, Int), x: Int):\n    f(x)\n",
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
    "def f(R <: Context, g: Int => Int causes R, n: Int):\n    g(n)\n",
    "`R` is bounded by `Context`, so it stands in a `requires` clause"
)]
#[case::a_bound_as_a_value_type(
    "def f(x: Effect):\n    x\n",
    "`Effect` bounds a type parameter standing for a clause"
)]
fn an_unsupported_or_misplaced_clause_is_refused(#[case] code: &str, #[case] needle: &str) {
    let errors = super::modules::compile_errors(&program(&format!("{PRELUDE}\n{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// An expression statement before its block's last statement is evaluated only for what it
/// causes, so one that causes nothing is refused (`docs/chl-spec.md`, "4.9 Expression
/// statement"), in every module of the program.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_pure_call("def f(x):\n    x + 1\nf(3)\n2\n", "")]
#[case::arithmetic("x = 1\nx + 1\n2\n", "")]
#[case::in_a_run_module("run lib as l\n1\n", "visits: Mut(Int, Txn) := 0\nx = 1\nx + 1\n")]
#[case::in_an_imported_function("import lib\nlib::f(1)\n", "pub def f(n):\n    n + 1\n    n\n")]
fn an_expression_statement_that_causes_nothing_is_refused(#[case] root: &str, #[case] lib: &str) {
    let modules: &[(&str, &str)] = if lib.is_empty() { &[] } else { &[("lib", lib)] };
    let errors = super::modules::compile_errors(&program(root, modules));
    assert!(
        errors.contains("this statement causes nothing and its value is discarded"),
        "{errors}"
    );
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
/// module").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_read("pub def current(n: Int):\n    cnt + n\n", "has `Read(cnt)`")]
#[case::a_write(
    "def bump(c: Mut(Int)):\n    c += 1\npub def tick(n: Int):\n    bump(cnt)\n    n\n",
    "has `Write(cnt)`"
)]
fn a_public_function_naming_an_induction_variable_is_refused(
    #[case] code: &str,
    #[case] needle: &str,
) {
    let errors = errors_of(&format!("cnt := 0\nfor x in [1, 2]:\n    cnt += x\n{code}"));
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
    "pub take: Int => Int requires ReadTxn(Module::_) causes WriteTxn(Module::_)"
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

/// A clause bounding what reaches a run's state names the run, `h::_`: `h`'s `stock` is within
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
        def g(x: Int) => Int requires only ReadTxn({run}::_) causes only RunTransaction, WriteTxn({run}::_):
            h::f(x)
        g(1)
    "}
    .replace("{run}", run);
    let entry = "Int => Int requires ReadTxn(Module::_) causes WriteTxn(Module::_), RunTransaction";
    match refused {
        None => super::helpers::check_program_scalar(&passing_helper(entry, &root), Value::Int(1)),
        Some(needle) => super::modules::assert_refused(&passing_helper(entry, &root), needle),
    }
}

/// Checked on its own, a module's Module-typed parameter takes no run, so a call through it
/// reaches the parameter's state, `p::_`, which its interface writes.
#[test]
fn a_parameters_state_is_written_through_it() {
    let interface = interface_of(indoc! {"
        param p: Module{f: Int => Int requires ReadTxn(Module::_) causes WriteTxn(Module::_), RunTransaction}
        pub def use_it(x: Int) => Int:
            p::f(x)
    "});
    assert!(
        interface.lines().any(|l| l
            == "pub use_it: Int => Int requires ReadTxn(p::_) causes RunTransaction, WriteTxn(p::_)"),
        "{interface}"
    );
}

/// `Module::_` stands only in a Module type's entry, and `x::_` names a run.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::module_outside_a_module_type(
    indoc! {"
        def f(n: Int) causes WriteTxn(Module::_):
            n
    "},
    "`Module::_` is the state of the module a Module type describes"
)]
#[case::a_qualifier_naming_no_module(
    indoc! {"
        def f(n: Int) causes WriteTxn(q::_):
            n
    "},
    "`q` does not name a module here"
)]
fn a_runs_state_is_written_where_it_has_one(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

/// A top in a clause stands for every capability of its direction, `Effect` or `Context`, or of
/// its family, `Write(_)`; `except` takes capabilities and families out of it and out of a
/// clause variable's bound; and a set holds each capability once, through the widest top
/// holding it (`docs/chl-spec.md`, "Writing requirements and effects", "Kinds and bounds").
#[rstest]
#[case::every_effect(
    "pub def apply(f: Int => Int causes Effect, x: Int) => Int causes Effect:\n    f(x)\n",
    "pub apply: {(Int => Int causes Effect), Int} => Int causes Effect"
)]
#[case::every_write(
    "pub def apply(f: Int => Int causes Write(_), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Write(_)), Int} => Int causes Write(_)"
)]
#[case::every_append(
    "pub def apply(f: Int => Int causes Append(_), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Append(_)), Int} => Int causes Append(_)"
)]
#[case::every_read(
    "pub def apply(f: Int => Int requires Read(_), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int requires Read(_)), Int} => Int requires Read(_)"
)]
#[case::two_families(
    "pub def apply(f: Int => Int causes Write(_), Append(_), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Write(_), Append(_)), Int} => Int causes Write(_), Append(_)"
)]
#[case::a_family_within_effect(
    "pub def apply(f: Int => Int causes Effect, Write(_), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Effect), Int} => Int causes Effect"
)]
#[case::a_family_taken_from_effect(
    "pub def apply(f: Int => Int causes Effect except Write(_), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int causes Effect except Write(_)), Int} => Int causes Effect except \
     Write(_)"
)]
#[case::reads_taken_from_context(
    "pub def apply(f: Int => Int requires Context except Read(_), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int requires Context except Read(_)), Int} => Int requires Context \
     except Read(_)"
)]
#[case::one_top_holding_what_another_takes_away(
    indoc! {"
        pub def both(f: Int => Int causes Effect except Write(_), g: Int => Int causes Write(_), x: Int) => Int:
            f(x) + g(x)
    "},
    "pub both: {(Int => Int causes Effect except Write(_)), (Int => Int causes Write(_)), Int} => \
     Int causes Effect"
)]
#[case::a_variable_beside_a_top_taking_away_on_its_own(
    indoc! {"
        pub def both(E <: Effect, f: Int => Int causes E, g: Int => Int causes Effect except RunTransaction, x: Int) => Int:
            f(x) + g(x)
    "},
    "pub both: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Effect except \
     RunTransaction), Int} => Int causes E, (Effect except RunTransaction)"
)]
#[case::a_variable_written_beside_every_write(
    indoc! {"
        pub def both(E <: Effect, f: Int => Int causes E, g: Int => Int causes Write(_), x: Int) => Int:
            f(x) + g(x)
        pub h: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Write(_)), Int} => Int causes E, Write(_) = both
    "},
    "pub h: forall (E <: Effect) {(Int => Int causes E), (Int => Int causes Write(_)), Int} => Int \
     causes E, Write(_)"
)]
#[case::a_variable_taking_away(
    "pub def g(E <: Effect, f: Int => Int causes E except RunTransaction, x: Int) => Int:\n    \
     f(x)\n",
    "pub g: forall (E <: Effect) {(Int => Int causes E except RunTransaction), Int} => Int causes \
     E except RunTransaction"
)]
#[case::a_variable_in_parentheses(
    "pub def g(E <: Effect, f: Int => Int causes (E except AffectWorld), x: Int) => Int:\n    \
     f(x)\n",
    "pub g: forall (E <: Effect) {(Int => Int causes E except AffectWorld), Int} => Int causes E \
     except AffectWorld"
)]
#[case::variables_taking_away_differently(
    indoc! {"
        pub def g(E <: Effect, F <: Effect, f: Int => Int causes (E except RunTransaction), F, x: Int) => Int:
            f(x)
        pub h: forall (E <: Effect, F <: Effect) {(Int => Int causes (E except RunTransaction), F), Int} => Int causes (E except RunTransaction), F = g
    "},
    "pub h: forall (E <: Effect, F <: Effect) {(Int => Int causes (E except RunTransaction), F), \
     Int} => Int causes (E except RunTransaction), F"
)]
#[case::a_variable_taking_away_beside_a_top(
    indoc! {"
        pub def g(E <: Effect, f: Int => Int causes E except RunTransaction, h: Int => Int causes Write(_), x: Int) => Int:
            f(x) + h(x)
    "},
    "pub g: forall (E <: Effect) {(Int => Int causes E except RunTransaction), (Int => Int causes \
     Write(_)), Int} => Int causes E, Write(_) except RunTransaction"
)]
#[case::a_clause_taking_from_its_variable_what_an_argument_does(
    "pub def apply(E <: Effect, f: Int => Int causes E except RunTransaction, x: Int) => Int \
     causes only E except RunTransaction:\n    f(x)\n",
    "pub apply: forall (E <: Effect) {(Int => Int causes E except RunTransaction), Int} => Int \
     causes E except RunTransaction"
)]
#[case::a_top_in_parentheses(
    "pub def apply(f: Int => Int requires (Context except ObserveWorld), x: Int) => Int:\n    f(x)\n",
    "pub apply: {(Int => Int requires Context except ObserveWorld), Int} => Int requires Context \
     except ObserveWorld"
)]
#[case::a_bounded_variable_within_a_top(
    "pub def apply(E <: Effect except RunTransaction, f: Int => Int causes E, x: Int) => Int \
     causes only (Effect except RunTransaction):\n    f(x)\n",
    "pub apply: forall (E <: Effect except RunTransaction) {(Int => Int causes E), Int} => Int \
     causes Effect except RunTransaction"
)]
#[case::a_bound_taking_capabilities_away(
    "pub def apply(E <: Effect except (RunTransaction, AffectWorld), f: Int => Int causes E, \
     x: Int) => Int causes only E:\n    f(x)\n",
    "pub apply: forall (E <: Effect except (RunTransaction, AffectWorld)) {(Int => Int causes E), \
     Int} => Int causes E"
)]
#[case::a_bound_taking_a_family_away(
    "pub def apply(E <: Effect except Write(_), f: Int => Int causes E, x: Int) => Int causes \
     only E:\n    f(x)\n",
    "pub apply: forall (E <: Effect except Write(_)) {(Int => Int causes E), Int} => Int causes E"
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
        pub def apply(f: Int => Int causes Effect except RunTransaction, x: Int) => Int:
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
        pub def apply(f: Int => Int causes Write(_), x: Int) => Int:
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
        pub def apply(E <: Effect except RunTransaction, f: Int => Int causes E, x: Int) => Int causes only E:
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
        def apply(E <: Effect except Write(_), f: Int => Int requires Read(_) causes E, x: Int) => Int causes only E:
            f(x)
        y = apply(bump, 1)
    "},
    "this has `Write(cnt)`, which the bound of the clause variable it reaches takes away"
)]
#[case::a_variable_beyond_a_top_taking_away(
    "pub def apply(E <: Effect, f: Int => Int causes E, x: Int) => Int causes only Effect except \
     RunTransaction:\n    f(x)\n",
    "this has `E`, which the definition's clause, bounded by `only` or `nothing`, does not list"
)]
#[case::a_variable_beyond_its_clause_taking_less(
    "pub def apply(E <: Effect, f: Int => Int causes E except RunTransaction, x: Int) => Int \
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
        def apply(E <: Effect, f: Int => Int causes E except RunTransaction, x: Int) => Int:
            f(x)
        pub def bad(x: Int) => Int:
            apply(commits, x)
    "},
    "this has `RunTransaction`, which the function type it must have does not state"
)]
#[case::a_capability_in_parentheses(
    "pub def g(f: Int => Int causes (RunTransaction except AffectWorld), x: Int) => Int:\n    \
     f(x)\n",
    "parentheses give a top or a clause variable an `except` of its own"
)]
#[case::a_top_in_parentheses_taking_nothing(
    "pub def g(f: Int => Int causes (Write(_) except RunTransaction), x: Int) => Int:\n    f(x)\n",
    "`except RunTransaction` takes nothing away"
)]
#[case::except_with_nothing_to_take(
    "pub def f(x: Int) => Int causes RunTransaction except AffectWorld:\n    x\n",
    "`except` takes capabilities out of a clause's variables and its tops"
)]
#[case::except_taking_nothing_from_its_tops(
    "pub def f(g: Int => Int causes Write(_) except RunTransaction, x: Int) => Int:\n    g(x)\n",
    "`except RunTransaction` takes nothing away: no top of this clause holds any of it"
)]
#[case::except_taking_effect(
    "pub def f(g: Int => Int causes Effect except Effect, x: Int) => Int:\n    g(x)\n",
    "`except` takes capabilities away, such as `RunTransaction` or `Write(_)`, not a clause \
     variable, `Effect`, `Context` or `_`"
)]
#[case::except_naming_no_variable(
    "pub def f(g: Int => Int causes Write(_) except Write(q), x: Int) => Int:\n    g(x)\n",
    "`Write(q)` names no variable in scope of the kind it takes"
)]
#[case::every_read_in_causes(
    "pub def f(g: Int => Int causes Read(_), x: Int) => Int:\n    g(x)\n",
    "`Read` is not an effect"
)]
#[case::every_write_in_requires(
    "pub def f(g: Int => Int requires Write(_), x: Int) => Int:\n    g(x)\n",
    "`Read(x)`, the tops `Context`, `ReadTxn(_)` and `Read(_)`, clause variables bounded by \
     `Context`"
)]
fn a_top_is_checked(#[case] code: &str, #[case] needle: &str) {
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
    "cnt := 0\nfor x in [1, 2]:\n    cnt += x\npub g: Int => Int causes Write(_) = \\x -> x\n",
    "`g` is public and its type has `Write(_)`"
)]
#[case::an_annotation_naming_an_induction_variable(
    "cnt := 0\nfor x in [1, 2]:\n    cnt += x\npub g: Int => Int causes Write(cnt) = \\x -> x\n",
    "`g` is public and its type has `Write(cnt)`"
)]
fn a_top_names_every_variable(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

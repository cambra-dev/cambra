//! What a function requires and causes, as inference collects it and a module's interface
//! prints it (`docs/chl-spec.md`, "6.9 Effects and requirements [Decided]";
//! `src/ccl/design/type-inference.md`, "Effect variables").

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use indoc::indoc;
use rstest_log::rstest;

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

/// The `causes` clause after the codomain of `member`'s contract, as `cambra check` prints it:
/// the last one on the line, after any a parameter's type writes.
fn clauses_of(code: &str, member: &str) -> String {
    let source = format!("{PRELUDE}\n{code}");
    let interface = check_program(&mut GlobalContext::default(), &program(&source, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"));
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
// A `with begin():` block commits, and its write names the variable it writes.
#[case("", "take", "causes Write(stock), Commit")]
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
    "causes Write(stock), Commit"
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
    "causes Write(stock), Commit"
)]
// Each use of a polymorphic function collects its own effects, so a call that passes it a
// committing function commits and one that passes it a pure function does not.
#[case(
    indoc! {"
        pub def committing_use(x: Int):
            apply(take, x)
    "},
    "committing_use",
    "causes Write(stock), Commit"
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
    "causes Write(stock), Commit"
)]
// A written clause is a lower bound: the body adds what it does, and a call sees what the
// clause lists whether or not the body does it.
#[case(
    indoc! {"
        pub def report(n: Int) causes Emit:
            out << n
    "},
    "report",
    "causes Append(out), Emit"
)]
#[case(
    indoc! {"
        pub def later(n: Int) causes Commit:
            n
    "},
    "later",
    "causes Commit"
)]
// `only` makes the clause an upper bound that the body meets.
#[case(
    indoc! {"
        pub def take_only(n: Int) causes only Write(stock), Commit:
            take(n)
    "},
    "take_only",
    "causes Write(stock), Commit"
)]
// A written function type's clauses are exact, so a function meeting them is passed, and the
// call does what the type states.
#[case(
    indoc! {"
        def call_with(f: Int => Int causes Write(stock), Commit, x: Int):
            f(x)
        pub def call_taken(n: Int):
            call_with(taken, n)
    "},
    "call_taken",
    "causes Write(stock), Commit"
)]
// A parameter's `_` is what each call passes.
#[case(
    indoc! {"
        def call_with(f: Int => Int causes _, x: Int):
            f(x)
        pub def via_hole(n: Int):
            call_with(taken, n)
    "},
    "via_hole",
    "causes Write(stock), Commit"
)]
// A declared parameter is what each call passes.
#[case(
    indoc! {"
        def call_all(E <: Effect, f: Int => Int causes E, x: Int) causes only E:
            f(x)
        pub def via_param(n: Int):
            call_all(taken, n)
    "},
    "via_param",
    "causes Write(stock), Commit"
)]
// A `let` annotation's `_` is what its value fills.
#[case(
    indoc! {"
        g: Int => Int causes _ = taken
        pub def via_g(n: Int):
            g(n)
    "},
    "via_g",
    "causes Write(stock), Commit"
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
    "pub call: forall (A, B, R <: Context, E <: Effect) {A => B requires R causes E, A} => B \
     requires R causes E"
)]
#[case::a_hole_in_a_written_parameter_type(
    "pub def call_with(f: Int => Int causes _, x: Int):\n    f(x)\n",
    "pub call_with: forall (E <: Effect) {Int => Int causes E, Int} => Int causes E"
)]
#[case::a_parameter_never_called(
    "pub def keep(f, x: Int):\n    x\n",
    "pub keep: forall (A) {A, Int} => Int  # callable in a constant"
)]
#[case::a_returned_function(
    "pub def compose(f, g):\n    \\x -> g(f(x))\n",
    "pub compose: forall (A, B, C, R <: Context, E <: Effect, R1 <: Context, E1 <: Effect) \
     {A => B requires R causes E, B => C requires R1 causes E1} => A => C requires R, R1 causes \
     E, E1"
)]
#[case::a_declared_effect_parameter(
    "pub def call_all(E <: Effect, f: Int => Int causes E, x: Int) causes only E:\n    f(x)\n",
    "pub call_all: forall (E <: Effect) {Int => Int causes E, Int} => Int causes E"
)]
#[case::a_declared_requirement_parameter(
    "pub def with_ctx(R <: Context, f: Int => Int requires R, x: Int) requires only R:\n    \
     f(x)\n",
    "pub with_ctx: forall (R <: Context) {Int => Int requires R, Int} => Int requires R"
)]
fn a_contract_names_the_effects_an_argument_brings(#[case] code: &str, #[case] line: &str) {
    let interface = check_program(&mut GlobalContext::default(), &program(code, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// A clause bounding what a function may require or cause refuses a body or an argument that
/// exceeds it, and a clause naming no variable of the kind it takes is refused
/// (`docs/chl-spec.md`, "Writing requirements and effects").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::beyond_only(
    indoc! {"
        def f(n: Int) causes only Commit:
            with begin():
                stock := stock - n
            n
    "},
    "this has `Write(stock)`, which the definition's clause"
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
    "this has `Write(stock)`, which the function type it must have does not state"
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
#[case::an_exception_without_its_type(
    "def f(n: Int) causes Raise:\n    n\n",
    "`Raise` takes one type"
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
        impl Twice(Count):
            def twice(t: Count) => Count causes Commit:
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
/// statement").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_pure_call("def f(x):\n    x + 1\nf(3)\n2\n")]
#[case::arithmetic("x = 1\nx + 1\n2\n")]
fn an_expression_statement_that_causes_nothing_is_refused(#[case] root: &str) {
    let errors = super::modules::compile_errors(&program(root, &[]));
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
    let source = format!("cnt := 0\nfor x in [1, 2]:\n    cnt += x\n{code}");
    let errors = check_program(&mut GlobalContext::default(), &program(&source, &[]))
        .expect_err("a public function naming an induction variable is refused");
    let rendered = format!("{errors:?}");
    assert!(rendered.contains(needle), "{rendered}");
}

/// A trait whose instances write state through an associated effect type, an instance that
/// writes a transactional variable, and a polymorphic definition calling the trait.
const TAKE: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    type Box = Int

    trait Take(T):
        Writes <: Effect
        def take(t: T, n: Int) => Int causes Commit, Writes

    impl Take(Box):
        def take(t, n):
            with begin():
                stock := stock - n
            n

    def generic(T, s: T, n: Int) requires t: Take(T) causes only Commit, t::Writes:
        t::take(s, n)
"};

/// What a call of a trait's function does is its signature's, and what an instance's
/// function does beyond it is the instance's associated effect type, which a call at that
/// instance does (`docs/chl-spec.md`, "Effects in traits").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_call_at_an_instance(
    indoc! {"
        def direct(n: Int) causes only Commit:
            summon(Take(Box))::take(Box::new(1), n)
    "},
    "this has `Write(stock)`, which the definition's clause"
)]
#[case::a_call_through_a_requirement(
    indoc! {"
        def through(n: Int) causes only Commit:
            generic(Box::new(1), n)
    "},
    "this has `Write(stock)`, which the definition's clause"
)]
// A requirement inference adds to a definition is answered at each use; until then a call
// does what any instance answering it does.
#[case::a_call_through_an_inferred_requirement(
    indoc! {"
        def inferred(s, n: Int):
            summon(Take(_))::take(s, n)
        def through_inferred(n: Int) causes only Commit:
            inferred(Box::new(1), n)
    "},
    "this has `Write(stock)`, which the definition's clause"
)]
#[case::a_requirement_beyond_its_bound(
    indoc! {"
        def narrow(T, s: T, n: Int) requires t: Take(T) causes only Commit:
            t::take(s, n)
    "},
    "this has `t::Writes`, which the definition's clause"
)]
fn a_trait_call_does_what_its_instance_does(#[case] code: &str, #[case] needle: &str) {
    let errors = super::modules::compile_errors(&program(&format!("{TAKE}\n{code}\n0\n"), &[]));
    assert!(errors.contains(needle), "{errors}");
}

/// A program calling an instance whose function writes state, directly and through a
/// requirement, compiles and runs.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::directly("summon(Take(Box))::take(Box::new(1), 3)")]
#[case::through_a_requirement("generic(Box::new(1), 3)")]
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
        stock: Mut(Int, Txn) := 10
        type Box = Int
        trait Take(T):
            def take(t: T, n: Int) => Int causes Commit
        impl Take(Box):
            def take(t, n):
                with begin():
                    stock := stock - n
                n
    "},
    "this has `Write(stock)`, which the trait's signature does not list"
)]
#[case::a_signature_naming_a_variable(
    indoc! {"
        stock: Mut(Int, Txn) := 10
        trait Take(T):
            def take(t: T, n: Int) => Int causes Write(stock)
    "},
    "a trait's signature names no variable"
)]
#[case::an_instance_writing_a_clause(
    indoc! {"
        type Box = Int
        trait Take(T):
            def take(t: T, n: Int) => Int
        impl Take(Box):
            def take(t, n) causes nothing:
                n
    "},
    "so it writes no clause"
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
        errors.contains("this has `Write(h::stock)`, which the function type it must have"),
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

/// A commit inside a `with begin():` block's body is refused, directly or through a call,
/// including a call of a function a polymorphic definition takes as a parameter, which each
/// use decides (`docs/chl-spec.md`, "8.2 Transactions: `with begin():`").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::through_a_parameter(indoc! {"
    stock: Mut(Int, Txn) := 10
    def taken(n: Int) => Int:
        with begin():
            stock := stock - n
        n
    def in_txn(f, x: Int):
        with begin():
            stock := stock - f(x)
    in_txn(taken, 1)
    0
"})]
fn a_commit_inside_a_transaction_is_refused(#[case] root: &str) {
    let errors = super::modules::compile_errors(&program(root, &[]));
    assert!(errors.contains("transactions do not nest"), "{errors}");
}

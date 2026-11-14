//! Public mutable variables: a module's transactional variable that other modules read and write
//! through its qualifier, name in their clauses, and take through a Module type's entry
//! (`docs/chl-spec.md`, "9.9 Running").

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::check_program_scalar;
use super::modules::{assert_refused, program};

/// A run of it holds a public `stock` and a private `hidden`.
const INVENTORY: &str = indoc! {"
    pub stock: Mut(Int, Txn) := 10
    hidden: Mut(Int, Txn) := 0
    pub def restock(n: Int):
        with begin():
            stock := stock + n
"};

/// `root` below a run `inv` of [`INVENTORY`], with `lib` beside it if given.
fn with_inventory(root: &str, lib: Option<&str>) -> LoadedProgram {
    let mut modules = vec![("inventory", INVENTORY)];
    modules.extend(lib.map(|lib| ("lib", lib)));
    program(&format!("run inventory as inv\n{root}"), &modules)
}

/// The interface `code`, checked as a module, prints.
fn interface_of(code: &str) -> String {
    check_program(&mut GlobalContext::default(), &program(code, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"))
}

/// Another module reads and writes a public variable through its qualifier: in a block, in a
/// function a block calls, and passed to a `Mut` parameter. Each write commits to the run's
/// one history, which `await_final` reads to its end.
#[rstest]
#[timeout(Duration::from_secs(20))]
#[case::a_write(
    indoc! {"
        with begin():
            inv::stock := inv::stock - 3
    "},
    7
)]
#[case::a_compound_write(
    indoc! {"
        with begin():
            inv::stock -= 3
    "},
    7
)]
#[case::in_a_function_a_block_calls(
    indoc! {"
        def take(n: Int) => Int:
            inv::stock -= n
            n
        with begin():
            take(3)
    "},
    7
)]
#[case::through_a_mut_parameter(
    indoc! {"
        def bump(x: Mut(Int, Txn)):
            with begin():
                x += 1
        bump(inv::stock)
    "},
    11
)]
#[case::beside_the_modules_own_writes(
    indoc! {"
        inv::restock(5)
        with begin():
            inv::stock -= 3
    "},
    12
)]
fn a_public_variable_is_written_through_its_qualifier(#[case] root: &str, #[case] expected: i64) {
    check_program_scalar(
        &with_inventory(&format!("{root}await_final(inv::stock)\n"), None),
        Value::Int(expected),
    );
}

/// A clause names another run's public variable, or the run's top, which holds it too.
#[rstest]
#[timeout(Duration::from_secs(20))]
#[case::the_variable("ReadTxn(inv::stock)", "WriteTxn(inv::stock)")]
#[case::the_runs_top("ReadTxn(inv::*)", "WriteTxn(inv::*)")]
fn a_clause_names_another_runs_public_variable(#[case] reads: &str, #[case] writes: &str) {
    let take =
        format!("def take(n: Int) => Int requires only Transaction, {reads} causes only {writes}:");
    let root = indoc! {"
        {take}
            inv::stock -= n
            n
        with begin():
            take(3)
        await_final(inv::stock)
    "}
    .replace("{take}", &take);
    check_program_scalar(&with_inventory(&root, None), Value::Int(7));
}

/// A module's interface writes its public variable, and the reads and writes of it, by name.
#[test]
fn an_interface_names_its_public_variable() {
    let interface = interface_of(INVENTORY);
    for line in [
        "pub stock: Mut(Int, Txn)",
        "pub restock: Int => {} requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction",
    ] {
        assert!(interface.lines().any(|l| l == line), "{interface}");
    }
}

/// The module `lib`, whose parameter's entry `stock` is a transactional variable.
const LIB: &str = indoc! {"
    param p: Module{stock: Mut(Int, Txn)}
    pub def take(n: Int):
        with begin():
            p::stock := p::stock - n
"};

/// A Module type's entry takes the argument's public variable itself: `lib`'s writes through
/// its parameter are writes to `inv`'s `stock`.
#[rstest]
#[timeout(Duration::from_secs(20))]
fn a_module_entry_takes_the_arguments_variable() {
    let root = indoc! {"
        run lib(p=inv) as l
        l::take(3)
        await_final(inv::stock)
    "};
    check_program_scalar(&with_inventory(root, Some(LIB)), Value::Int(7));
}

/// A module passing its Module-typed parameter on to a run of [`LIB`]: the run's entry is the
/// variable the outer argument holds, so writes through either reach `inv`'s `stock`.
#[rstest]
#[timeout(Duration::from_secs(20))]
fn a_module_entry_passed_on_takes_the_outer_arguments_variable() {
    let relay = indoc! {"
        param q: Module{stock: Mut(Int, Txn)}
        run lib(p=q) as inner
        pub def go():
            with begin():
                q::stock -= 1
            inner::take(2)
    "};
    let root = indoc! {"
        run relay(q=inv) as r
        r::go()
        await_final(inv::stock)
    "};
    let program = program(
        &format!("run inventory as inv\n{root}"),
        &[("inventory", INVENTORY), ("lib", LIB), ("relay", relay)],
    );
    check_program_scalar(&program, Value::Int(7));
}

/// Checked on its own, a module reaches its parameter's variable through the parameter, which
/// its interface names it by.
#[test]
fn a_parameters_variable_is_named_through_it() {
    let interface = interface_of(LIB);
    let line =
        "pub take: Int => {} requires ReadTxn(p::stock) causes WriteTxn(p::stock), RunTransaction";
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// What another module may not do with a module's mutable state.
#[rstest]
#[timeout(Duration::from_secs(20))]
#[case::a_private_variable(
    indoc! {"
        with begin():
            inv::hidden := 1
    "},
    "`hidden` is private to module `inventory`"
)]
#[case::a_private_variable_in_a_clause(
    indoc! {"
        def f() causes WriteTxn(inv::hidden):
            0
        f()
    "},
    "`hidden` is private to module `inventory`"
)]
#[case::a_rebinding(
    "inv::stock = 1\n",
    "`inv::stock` is a member of another module, which `=` cannot rebind"
)]
#[case::an_annotated_declaration_at_the_top_level(
    "inv::stock: Mut(Int, Txn) := 5\n",
    "`inv::stock` is a member of another module, which an annotated `:=` cannot declare"
)]
#[case::an_annotated_declaration_in_a_function(
    indoc! {"
        def f():
            inv::stock: Mut(Int) := 5
        f()
    "},
    "`inv::stock` is a member of another module, which an annotated `:=` cannot declare"
)]
#[case::an_annotated_declaration_in_a_block(
    indoc! {"
        with begin():
            inv::stock: Int := 1
    "},
    "`inv::stock` is a member of another module, which an annotated `:=` cannot declare"
)]
#[case::a_write_outside_a_block(
    indoc! {"
        def f():
            inv::stock := 1
        f()
    "},
    "this requires `Transaction` outside a `with begin():` block"
)]
#[case::a_read_beyond_a_clause(
    indoc! {"
        def peek() => Int requires only Transaction:
            inv::stock
        with begin():
            peek()
    "},
    "this has `ReadTxn(inv::stock)`, which the definition's clause"
)]
fn another_modules_state_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(&with_inventory(root, None), needle);
}

/// A run of it publishes `stock`'s final value as `last`. A block writing `stock` and `reserved`
/// together puts both in one commit store.
const AWAITING: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    pub reserved: Mut(Int, Txn) := 0
    for r in [3]:
        with begin():
            stock := stock - r
            reserved := reserved + r
    pub last = await_final(stock)
    pub def reserve(n: Int):
        with begin():
            reserved := reserved + n
"};

/// A writer of `stock`'s store that depends on `await_final(stock)` through `inv`'s public
/// `last` is the cycle `await_final` refuses in one module (`docs/chl-spec.md`, "8.6
/// `await_final`"). It writes `reserved`, since a later reference to `stock` itself is refused
/// as reading a consumed variable.
#[rstest]
#[timeout(Duration::from_secs(20))]
#[case::in_a_blocks_body(
    indoc! {"
        with begin():
            inv::reserved := inv::reserved + inv::last
    "},
    "body depends on `await_final(stock)`"
)]
#[case::in_a_writers_source(
    indoc! {"
        for r in [x + inv::last for x in [1, 2]]:
            with begin():
                inv::reserved += r
    "},
    "iteration source depends on `await_final(stock)`"
)]
#[case::through_the_modules_function(
    indoc! {"
        for r in [x + inv::last for x in [1, 2]]:
            inv::reserve(r)
    "},
    "iteration source depends on `await_final(stock)`"
)]
fn a_writer_awaiting_through_another_module_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            &format!("run inventory as inv\n{root}"),
            &[("inventory", AWAITING)],
        ),
        needle,
    );
}

/// A public mutable variable is transactional: an induction variable stays in its module.
#[rstest]
#[timeout(Duration::from_secs(20))]
#[case::unannotated("pub x := 0\n")]
#[case::annotated("pub x: Mut(Int) := 0\n")]
fn a_public_induction_variable_is_refused(#[case] code: &str) {
    assert_refused(
        &LoadedProgram::test(code),
        "a public mutable variable is transactional, `pub x: Mut(V, Txn) := …`",
    );
}

/// A Module type's entry names a transactional variable, of the argument's value type exactly,
/// since `Mut` is invariant.
#[rstest]
#[timeout(Duration::from_secs(20))]
#[case::an_induction_entry(
    "Mut(Int)",
    "`stock` is a mutable variable, which another module reaches only when it is transactional"
)]
#[case::an_entry_of_another_type(
    "Mut(String, Txn)",
    "Type mismatch for write to mutable variable `inv::stock`: expected Int, found String"
)]
fn a_module_entry_is_the_arguments_type(#[case] entry: &str, #[case] needle: &str) {
    let lib = indoc! {"
        param p: Module{stock: {entry}}
        pub def peek() => Int:
            1
    "}
    .replace("{entry}", entry);
    assert_refused(&with_inventory("run lib(p=inv) as l\n", Some(&lib)), needle);
}

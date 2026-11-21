//! Module interfaces expose values and functions; writable place declarations remain private.

use indoc::indoc;
use rstest_log::rstest;

use super::modules::{assert_refused, program};

#[rstest]
#[case::unannotated_mut("pub stock := 10")]
#[case::induction_mut("pub stock: Mut(Int) := 10")]
#[case::transactional_mut("pub stock: Mut(Int, Txn) := 10")]
#[case::feed("pub events: Feed(Int)")]
#[case::inferred_feed("pub events: Feed(_)")]
fn a_place_declaration_cannot_be_exported(#[case] declaration: &str) {
    assert_refused(
        &program("run inventory as inv", &[("inventory", declaration)]),
        "a place declaration cannot be public",
    );
}

const INVENTORY: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    hidden: Mut(Int, Txn) := 0
    pub last = await_final(stock)
"};

#[rstest]
#[case::a_private_variable(indoc! {"
    with begin():
        inv::hidden := 1
"}, "`hidden` is private to module `inventory`")]
#[case::a_private_variable_in_a_clause(indoc! {"
    def f() causes WriteTxn(inv::hidden):
        0
    f()
"}, "`hidden` is private to module `inventory`")]
#[case::a_private_read(indoc! {"
    with begin():
        inv::stock
"}, "`stock` is private to module `inventory`")]
#[case::a_rebinding(
    "inv::last = 1",
    "`inv::last` is a member of another module, which `=` cannot rebind"
)]
#[case::an_annotated_declaration_at_the_top_level(
    "inv::stock: Mut(Int, Txn) := 5",
    "`inv::stock` is a member of another module, which an annotated `:=` cannot declare"
)]
#[case::an_annotated_declaration_in_a_function(indoc! {"
    def f():
        inv::stock: Mut(Int) := 5
    f()
"}, "`inv::stock` is a member of another module, which an annotated `:=` cannot declare")]
#[case::an_annotated_declaration_in_a_block(indoc! {"
    with begin():
        inv::stock: Int := 1
"}, "`inv::stock` is a member of another module, which an annotated `:=` cannot declare")]
#[case::writing_a_value_export(indoc! {"
    with begin():
        inv::last := 1
"}, "not a mutable variable")]
fn a_module_keeps_its_places_private(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            &format!("run inventory as inv\n{root}"),
            &[("inventory", INVENTORY)],
        ),
        needle,
    );
}

#[rstest]
#[case::induction("Mut(Int)")]
#[case::transactional("Mut(Int, Txn)")]
#[case::deferred("Feed(Int)")]
fn a_module_type_cannot_store_a_place_entry(#[case] entry: &str) {
    let library = format!("param p: Module{{stock: {entry}}}\npub value = 0");
    assert_refused(
        &program("import lib", &[("lib", &library)]),
        "`stock` is a place, and a Module entry cannot be one",
    );
}

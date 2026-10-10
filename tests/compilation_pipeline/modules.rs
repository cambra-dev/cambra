//! Programs of several modules: an imported module's public members reached
//! through its import name, and labels that belong to a module
//! (`docs/chl-spec.md`, "9. Modules [Decided]").

use std::collections::BTreeSet;
use std::panic::{self, AssertUnwindSafe};
use std::time::Duration;

use cambra::ccl::context::GlobalContext;
use cambra::ccl::load::{InMemory, LoadedProgram, RootFile};
use cambra::ccl::lower::modules::lower_program;
use cambra::ccl::{Home, TypedExprNode};
use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::*;
use crate::panic_message::panic_message;

/// The program rooted at `root`, with `modules` as its other modules' files, by
/// module path.
pub(crate) fn program(root: &str, modules: &[(&str, &str)]) -> LoadedProgram {
    let mut files = modules
        .iter()
        .fold(InMemory::default(), |files, (path, text)| {
            files.with(path, *text)
        });
    let root = RootFile {
        path: "main.cambra".to_owned(),
        module: None,
        text: root.to_owned(),
    };
    LoadedProgram::load(root, &mut files)
}

/// The rendered errors of a program that does not compile.
pub(crate) fn compile_errors(program: &LoadedProgram) -> String {
    let result = panic::catch_unwind(AssertUnwindSafe(|| run_program(program)));
    let Err(payload) = result else {
        panic!("expected the program not to compile");
    };
    panic_message(&*payload)
}

pub(crate) fn assert_refused(program: &LoadedProgram, needle: &str) {
    let errors = compile_errors(program);
    assert!(errors.contains(needle), "expected {needle:?} in:\n{errors}");
}

const CATALOG: &str = indoc! {"
    pub limit = 10
    pub def double(x):
        x * 2
    pub def id(x):
        x
    hidden = 3
    pub def item(p):
        (price=p, cost=1)
    pub def cost_of(r):
        r.cost
"};

#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_qualified_reference_reaches_a_public_member() {
    check_program_scalar(
        &program(
            indoc! {"
                import catalog
                catalog::double(catalog::limit) + 1
            "},
            &[("catalog", CATALOG)],
        ),
        Value::Int(21),
    );
}

/// A generic member keeps its polymorphism through a qualified reference
/// (`docs/chl-spec.md`, "9.6 Qualified references").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_qualified_generic_member_keeps_its_polymorphism() {
    check_program_scalar(
        &program(
            indoc! {"
                import catalog
                catalog::id(3) if catalog::id(True) else 0
            "},
            &[("catalog", CATALOG)],
        ),
        Value::Int(3),
    );
}

/// `import a::b as c` binds `c`, and a module reaches the modules it imports.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_import_binds_its_alias_and_a_module_imports_another() {
    check_program_scalar(
        &program(
            indoc! {"
                import shop::pricing as p
                import base
                p::plus(base::n)
            "},
            &[
                ("base", "pub n = 5\n"),
                (
                    "shop::pricing",
                    indoc! {"
                        import base
                        pub def plus(x):
                            x + base::n
                    "},
                ),
            ],
        ),
        Value::Int(10),
    );
}

/// `use` binds a member unqualified, under its own name or an alias, and a
/// generic member keeps its polymorphism (`docs/chl-spec.md`, "9.2 Imports").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_use_item_binds_a_member_unqualified() {
    check_program_scalar(
        &program(
            indoc! {"
                import catalog use id, double as twice
                twice(id(3)) if id(True) else 0
            "},
            &[("catalog", CATALOG)],
        ),
        Value::Int(6),
    );
}

/// A `use` name is in scope throughout its module, above its `import` too.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_use_name_is_in_scope_above_its_import() {
    check_program_scalar(
        &program(
            indoc! {"
                four = double(2)
                import catalog use double
                four
            "},
            &[("catalog", CATALOG)],
        ),
        Value::Int(4),
    );
}

/// A local binder shadows a `use` name, a parameter and a binding in a `def`
/// alike (`docs/chl-spec.md`, "9.6 Qualified references").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_local_shadows_a_use_name() {
    check_program_scalar(
        &program(
            indoc! {"
                import catalog use double, limit
                def by_parameter(double):
                    double + 1
                def by_binding(x):
                    limit = x + 100
                    limit
                by_parameter(1) + by_binding(1) + double(limit)
            "},
            &[("catalog", CATALOG)],
        ),
        Value::Int(2 + 101 + 20),
    );
}

/// An imported module's own `use` names resolve within it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_imported_module_uses_a_member_of_another() {
    check_program_scalar(
        &program(
            "import pricing use plus
plus(1)
",
            &[
                (
                    "base",
                    "pub n = 5
",
                ),
                (
                    "pricing",
                    indoc! {"
                        import base use n
                        pub def plus(x):
                            x + n
                    "},
                ),
            ],
        ),
        Value::Int(6),
    );
}

#[rstest]
#[case::private_member(
    "import catalog use hidden\n",
    "`hidden` is private to module `catalog`"
)]
#[case::missing_member(
    "import catalog use missing\n",
    "module `catalog` has no member `missing`"
)]
#[case::missing_type_member(
    "import catalog use Item\n",
    "module `catalog` has no type member `Item`"
)]
#[case::bound_by_a_member(
    "import catalog use limit\nlimit = 1\n",
    "`limit` is a `use` name, so no member of its module takes it"
)]
#[case::bound_by_a_def(
    "import catalog use double\ndef double(x):\n    x\n",
    "`double` is a `use` name, so no member of its module takes it"
)]
#[case::an_import_name(
    "import other\nimport catalog use limit as other\n",
    "`other` is an import name or a run name, so no binder in its module takes it"
)]
#[case::bound_twice(
    "import catalog use limit, double as limit\n",
    "`limit` is already a `use` name"
)]
#[case::bound_by_two_imports(
    "import catalog use limit\nimport other use x as limit\n",
    "`limit` is already a `use` name"
)]
#[case::a_builtin("import catalog use double as sum\n", "`sum` is a builtin")]
#[timeout(Duration::from_secs(10))]
fn a_misused_use_item_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            &format!("{root}1\n"),
            &[("catalog", CATALOG), ("other", "pub x = 1\n")],
        ),
        needle,
    );
}

#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_private_member_is_refused_with_its_declaration() {
    let errors = compile_errors(&program(
        "import catalog\ncatalog::hidden\n",
        &[("catalog", CATALOG)],
    ));
    assert!(
        errors.contains("`hidden` is private to module `catalog`"),
        "{errors}"
    );
    assert!(errors.contains("declared here without `pub`"), "{errors}");
    assert!(errors.contains("catalog.cambra"), "{errors}");
}

#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_missing_member_is_refused() {
    assert_refused(
        &program(
            "import catalog\ncatalog::missing\n",
            &[("catalog", CATALOG)],
        ),
        "module `catalog` has no member `missing`",
    );
}

/// A module's type aliases, as `shapes` declares them: `Small` names a
/// refinement over the private `cap`, `Pair` a record, and `Hidden` is private.
const SHAPES: &str = indoc! {"
    cap = 10
    pub Small = {Int where _ < cap}
    pub Pair = {left: Int, right: Int}
    Hidden = Int
    pub def first(p: Pair) => Int:
        p.left
"};

/// An imported alias names the type its module declares, by qualified name and
/// through `use`, under its own name or an alias (`docs/chl-spec.md`, "9.2
/// Imports").
#[rstest]
#[case::qualified("import shapes\nx: shapes::Small = 5\nx\n")]
#[case::used("import shapes use Small\nx: Small = 5\nx\n")]
#[case::used_under_an_alias("import shapes use Small as Tiny\nx: Tiny = 5\nx\n")]
#[timeout(Duration::from_secs(10))]
fn an_imported_alias_names_its_modules_type(#[case] root: &str) {
    check_program_scalar(&program(root, &[("shapes", SHAPES)]), Value::Int(5));
}

/// An imported alias's predicate reads the bindings its declaration sees, so
/// the importer's own `cap` does not capture it, and a value it rejects is
/// rejected wherever the alias is used.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_imported_alias_is_closed_over_its_module() {
    let importer =
        |value: i64| format!("import shapes\ncap = 100\nx: shapes::Small = {value}\nx + cap\n");
    check_program_scalar(
        &program(&importer(5), &[("shapes", SHAPES)]),
        Value::Int(105),
    );
    let errors = compile_errors(&program(&importer(50), &[("shapes", SHAPES)]));
    assert!(
        errors.contains("annotated as {Int where _ < shapes::cap}"),
        "{errors}"
    );
}

/// An imported record alias is the record type its module writes, labels and
/// all, so the importer builds it with that module's labels.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_imported_record_alias_carries_its_modules_labels() {
    check_program_scalar(
        &program(
            indoc! {"
                import shapes use Pair
                p: Pair = (shapes::left=1, shapes::right=2)
                shapes::first(p) + p.shapes::right
            "},
            &[("shapes", SHAPES)],
        ),
        Value::Int(3),
    );
}

/// An alias may be built from another module's alias, and carries its type.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_alias_is_built_from_another_modules_alias() {
    check_program_scalar(
        &program(
            "import sizes use Medium\nx: Medium = 5\nx\n",
            &[
                ("shapes", SHAPES),
                ("sizes", "import shapes\npub Medium = shapes::Small\n"),
            ],
        ),
        Value::Int(5),
    );
}

#[rstest]
#[case::private(
    "import shapes\nx: shapes::Hidden = 1\nx\n",
    "`Hidden` is private to module `shapes`"
)]
#[case::private_through_use(
    "import shapes use Hidden\n1\n",
    "`Hidden` is private to module `shapes`"
)]
#[case::bound_by_an_alias(
    "import shapes use Small\nSmall = Int\n1\n",
    "`Small` is a `use` name, so no member of its module takes it"
)]
#[case::a_builtin_type("import shapes use Small as Int\n1\n", "`Int` is a built-in type")]
#[timeout(Duration::from_secs(10))]
fn a_misused_type_member_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(&program(root, &[("shapes", SHAPES)]), needle);
}

/// A label written in a module is that module's: the library's `price` is
/// `catalog::price` to the root, and the root's own `price` is another label.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_label_belongs_to_the_module_that_writes_it() {
    let root = |body: &str| format!("import catalog\n{body}\n");
    check_program_scalar(
        &program(
            &root("catalog::item(5).catalog::price"),
            &[("catalog", CATALOG)],
        ),
        Value::Int(5),
    );
    check_program_scalar(
        &program(
            &root("catalog::cost_of((catalog::cost=3))"),
            &[("catalog", CATALOG)],
        ),
        Value::Int(3),
    );
    assert_refused(
        &program(&root("catalog::item(5).price"), &[("catalog", CATALOG)]),
        "No field .price for Apply: {catalog::cost: Int@1, catalog::price: Int@5}",
    );
    assert_refused(
        &program(&root("catalog::cost_of((cost=3))"), &[("catalog", CATALOG)]),
        "No field .catalog::cost for Apply: {cost: Int@3}",
    );
}

/// `this::` spells the current module's own label.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn this_qualifies_the_current_modules_label() {
    check_program_scalar(&program("(this::a=1).a\n", &[]), Value::Int(1));
}

/// `Option`'s tags are one tag in every module until `Option` is a nominal
/// variant, so a library's lookup result matches the root's `` `some ``.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn options_tags_are_every_modules() {
    check_program_scalar(
        &program(
            indoc! {"
                import prices
                match prices::find(1):
                    case `some(v):
                        v
                    case `none:
                        0
            "},
            &[(
                "prices",
                indoc! {"
                    table = map([(1, 10), (2, 20)])
                    pub def find(k):
                        table[k]?
                "},
            )],
        ),
        Value::Int(10),
    );
}

/// A module whose parameters an import passes: `scale` has no default.
const SCALED: &str = indoc! {"
    param scale: Int
    param offset: Int = 0
    pub def by(x):
        x * scale + offset
"};

/// An import passes its arguments to the module's parameters, and a parameter
/// without one takes its default (`docs/chl-spec.md`, "9.2 Imports").
#[rstest]
#[case::an_argument("import scaled(scale=3)\nscaled::by(2)\n", 6)]
#[case::overriding_a_default("import scaled(scale=3, offset=1)\nscaled::by(2)\n", 7)]
#[case::a_negative_literal("import scaled(scale=-3)\nscaled::by(2)\n", -6)]
#[case::a_boolean("import flag(on=True)\nflag::n\n", 1)]
#[case::through_use("import scaled(scale=3) use by\nby(2)\n", 6)]
#[case::two_sets_of_arguments("import scaled(scale=2)\nimport nine\nscaled::by(1) + nine::v\n", 11)]
#[timeout(Duration::from_secs(10))]
fn an_imports_arguments_reach_its_modules_parameters(#[case] root: &str, #[case] expected: i64) {
    check_program_scalar(
        &program(
            root,
            &[
                ("scaled", SCALED),
                ("flag", "param on: Bool\npub n = 1 if on else 0\n"),
                ("nine", "import scaled(scale=3)\npub v = scaled::by(3)\n"),
            ],
        ),
        Value::Int(expected),
    );
}

/// The shared runs `program` lowers, by their homes: each `let` its chains bind
/// stands on the spine above the root's.
fn shared_runs(program: &LoadedProgram) -> BTreeSet<String> {
    let mut ctx = GlobalContext::default();
    let lowered = lower_program(program, ctx.lowering_ctx());
    assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);
    let tree = lowered.value.expect("the program lowers");
    let mut homes = BTreeSet::new();
    let mut at = &tree;
    loop {
        match &at.node {
            TypedExprNode::Let { binding, body, .. } => {
                if let Some(Home::Shared(run)) = binding.name.home() {
                    homes.insert(run.to_string());
                }
                at = body;
            }
            TypedExprNode::MutDecl { body, .. } | TypedExprNode::ExprStmt { body, .. } => {
                at = body;
            }
            _ => return homes,
        }
    }
}

/// Imports of one module with equal arguments reach one shared run, whichever
/// order they write them in, and imports with different arguments reach two
/// (`docs/chl-spec.md`, "9.2 Imports").
#[rstest]
#[case::equal_arguments("import scaled(scale=3)", "import scaled(scale=3)", &["scaled(scale=3)"])]
#[case::in_another_order(
    "import scaled(offset=1, scale=3)",
    "import scaled(scale=3, offset=1)",
    &["scaled(offset=1, scale=3)"]
)]
#[case::different_arguments(
    "import scaled(scale=2)",
    "import scaled(scale=3)",
    &["scaled(scale=2)", "scaled(scale=3)"]
)]
#[timeout(Duration::from_secs(10))]
fn an_import_reaches_one_shared_run_per_set_of_arguments(
    #[case] root: &str,
    #[case] other: &str,
    #[case] expected: &[&str],
) {
    assert_shared_runs(root, other, expected);
}

/// An omitted argument is its parameter's default, so an import that omits it
/// and one that passes the default reach one shared run (`docs/chl-spec.md`,
/// "9.2 Imports").
#[rstest]
#[ignore = "arguments are compared as written (docs/modules.md, \"Imports\")"]
#[timeout(Duration::from_secs(10))]
fn an_omitted_argument_is_its_default() {
    assert_shared_runs(
        "import scaled(scale=3)",
        "import scaled(scale=3, offset=0)",
        &["scaled(scale=3)"],
    );
}

/// Assert that a program whose root imports `scaled` with the statement `root`,
/// and imports `nine`, which imports it with `other`, lowers the shared runs of
/// `scaled` in `expected`.
fn assert_shared_runs(root: &str, other: &str, expected: &[&str]) {
    let program = program(
        &format!("{root}\nimport nine\nscaled::by(1) + nine::v\n"),
        &[
            ("scaled", SCALED),
            ("nine", &format!("{other}\npub v = scaled::by(3)\n")),
        ],
    );
    let expected: BTreeSet<String> = expected.iter().map(|s| s.to_string()).collect();
    let mut runs = shared_runs(&program);
    runs.remove("nine");
    assert_eq!(runs, expected);
}

#[rstest]
#[case::missing(
    "import scaled\n1\n",
    "this import passes no argument for the parameter `scale`, which has no default"
)]
#[case::unknown(
    "import scaled(scale=1, nope=2)\n1\n",
    "module `scaled` has no parameter `nope`"
)]
#[case::twice(
    "import scaled(scale=1, scale=2)\n1\n",
    "the parameter `scale` already has an argument"
)]
#[case::not_a_literal(
    "import scaled(scale=1 + 2)\n1\n",
    "an argument to an import is supported only as a literal for now"
)]
#[case::mistyped("import scaled(scale=\"x\")\nscaled::by(1)\n", "annotated as Int")]
#[timeout(Duration::from_secs(10))]
fn a_misused_import_argument_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(&program(root, &[("scaled", SCALED)]), needle);
}

/// Importing a module that performs IO is an error at the `import`, pointing at
/// the IO (`docs/chl-spec.md`, "9.7 Importing asserts no IO and no state").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn importing_a_module_that_performs_io_is_refused() {
    let errors = compile_errors(&program(
        "import audit\n1\n",
        &[("audit", "out = test_sink()\nout << 1\n")],
    ));
    assert!(
        errors.contains("module `audit` performs IO, so importing it is an error"),
        "{errors}"
    );
    assert!(errors.contains("the IO it performs"), "{errors}");
}

/// Importing a module that declares mutable state is an error at the `import`,
/// pointing at the state: a module with state is run, not imported
/// (`docs/chl-spec.md`, "9.7 Importing asserts no IO and no state").
#[rstest]
#[case::transactional_variable("pub stock: Mut(Int, Txn) := 0\n")]
#[case::private_variable("stock: Mut(Int, Txn) := 0\npub n = 1\n")]
#[case::mutable_variable("total := 0\n")]
#[timeout(Duration::from_secs(10))]
fn importing_a_module_that_declares_state_is_refused(#[case] library: &str) {
    let errors = compile_errors(&program("import inventory\n1\n", &[("inventory", library)]));
    assert!(
        errors.contains(
            "module `inventory` declares mutable state, so importing it is an error: run it instead"
        ),
        "{errors}"
    );
    assert!(errors.contains("the state it declares"), "{errors}");
}

/// A module of functions over the caller's state is imported: a call to its
/// function with a `Mut` parameter takes the curried shape the function lowers
/// to, by qualified name and through `use` (`docs/chl-spec.md`, "9.6 Qualified
/// references").
#[rstest]
#[case::qualified("import bank\n", "bank::draw", "bank::transfer")]
#[case::used("import bank use draw, transfer\n", "draw", "transfer")]
#[timeout(Duration::from_secs(10))]
fn an_imported_function_writes_the_callers_state(
    #[case] import: &str,
    #[case] draw: &str,
    #[case] transfer: &str,
) {
    let bank = indoc! {"
        pub def draw(p: Mut(Int, Txn), amt: Int):
            with begin():
                p := p - amt
        pub def transfer(src: Mut(Int, Txn), dst: Mut(Int, Txn), amt):
            with begin():
                src := src - amt
                dst := dst + amt
    "};
    let root = format!(
        "{import}a: Mut(Int, Txn) := 100\nb: Mut(Int, Txn) := 0\n{draw}(a, 10)\n\
         {transfer}(a, b, 30)\nawait_final(a) * 1000 + await_final(b)\n"
    );
    check_program_scalar(&program(&root, &[("bank", bank)]), Value::Int(60_030));
}

#[rstest]
#[case::module_as_a_value("import catalog\ncatalog\n", "`catalog` names a module")]
#[case::import_name_rebound(
    "import catalog\ncatalog = 1\ncatalog\n",
    "`catalog` is an import name, so no binder in its module takes it"
)]
#[case::import_name_as_a_parameter(
    "import catalog\ndef f(catalog):\n    1\nf(2)\n",
    "`catalog` is an import name"
)]
#[case::missing_type_member(
    "import catalog\nx: catalog::Item = 1\nx\n",
    "module `catalog` has no type member `Item`"
)]
#[case::type_member_as_a_value(
    "import catalog\ncatalog::Item\n",
    "`catalog::Item` is a type, not a value"
)]
#[case::value_member_as_a_type(
    "import catalog\nx: catalog::limit = 1\nx\n",
    "`catalog::limit` is a value, not a type"
)]
#[case::unknown_qualifier(
    "(nope::a=1).a\n",
    "`nope` is not an import name or a run name of this module"
)]
#[case::value_qualified_by_this("this::a\n", "`this` qualifies a label or a tag")]
#[case::member_of_a_run("shop::eu::stock\n", "names a member of a run")]
#[case::second_import_of_a_name(
    "import catalog\nimport other as catalog\n1\n",
    "`catalog` is already an import name"
)]
#[timeout(Duration::from_secs(10))]
fn a_misused_module_name_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(root, &[("catalog", CATALOG), ("other", "pub x = 1\n")]),
        needle,
    );
}

#[rstest]
#[case::expression_statement("pub x = 1\nx + 1\n", "an imported module has none")]
#[case::top_level_loop("for x in [1]:\n    pass\n", "an imported module holds value bindings")]
#[case::public_name_bound_twice(
    "pub x = 1\nx = 2\n",
    "`x` is public, so it is bound exactly once at its module's top level"
)]
#[timeout(Duration::from_secs(10))]
fn an_unsupported_library_statement_is_refused(#[case] library: &str, #[case] needle: &str) {
    assert_refused(&program("import lib\n1\n", &[("lib", library)]), needle);
}

/// A reference or a `use` item into a module with errors of its own reports
/// nothing more: the module's errors account for it.
#[rstest]
#[case::qualified("import lib\nlib::missing\n")]
#[case::used("import lib use missing\nmissing\n")]
#[timeout(Duration::from_secs(10))]
fn a_reference_into_a_module_with_errors_adds_no_error(#[case] root: &str) {
    let errors = compile_errors(&program(root, &[("lib", "pub x = = 1\n")]));
    assert!(!errors.contains("has no member"), "{errors}");
    assert!(!errors.contains("missing"), "{errors}");
}

/// A module two others import is evaluated once: its bindings stand once in the
/// linked tree, ahead of both importers' (`docs/chl-spec.md`, "9.7 Importing
/// asserts no IO and no state").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_imported_module_is_linked_once() {
    use cambra::ccl::context::{Phase, compile_to};
    use cambra::ccl::symbolic::symbolic;
    let program = program(
        indoc! {"
            import left
            import right
            left::n + right::n
        "},
        &[
            ("base", "pub shared = 7\n"),
            ("left", "import base\npub n = base::shared + 1\n"),
            ("right", "import base\npub n = base::shared + 2\n"),
        ],
    );
    let tree = symbolic(&compile_to(&program, Phase::Lower).expect("compiles"));
    assert_eq!(tree.matches("let base::shared =").count(), 1, "{tree}");
    let order: Vec<usize> = [
        "let base::shared =",
        "let left::n = base::shared + 1",
        "let right::n = base::shared + 2",
    ]
    .iter()
    .map(|binding| {
        tree.find(binding)
            .unwrap_or_else(|| panic!("{binding} in {tree}"))
    })
    .collect();
    assert!(order.windows(2).all(|w| w[0] < w[1]), "link order: {tree}");
    check_program_scalar(&program, Value::Int(17));
}

/// A type alias among a module's top-level statements leaves the members below
/// it top-level, so they carry their module too.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_member_below_a_type_alias_carries_its_module() {
    let errors = compile_errors(&program(
        "import lib\nx: {Int where _ > lib::limit} = 5\nx\n",
        &[("lib", "Small = Int\npub limit: Small = 10\n")],
    ));
    assert!(
        errors.contains("annotated as {Int where _ > lib::limit}"),
        "{errors}"
    );
}

/// An imported member renders with its module, so a diagnostic names
/// `catalog::limit` rather than a bare `limit` (`docs/modules.md`, "Names carry
/// their home").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_diagnostic_qualifies_an_imported_member() {
    let errors = compile_errors(&program(
        "import catalog\nx: {Int where _ > catalog::limit} = 5\nx\n",
        &[("catalog", CATALOG)],
    ));
    assert!(
        errors.contains("annotated as {Int where _ > catalog::limit}"),
        "{errors}"
    );
}

/// The inspector's payload carries one file, so a program of several modules
/// gets the degraded payload, saying why.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn the_inspector_refuses_a_program_of_several_modules() {
    let payload = cambra::inspector_server::snapshot_body_pretty(&program(
        "import base\nbase::n\n",
        &[("base", "pub n = 1\n")],
    ));
    assert!(payload.contains(r#""payloadKind": "failed""#), "{payload}");
    assert!(
        payload.contains("a program of several modules is not supported yet"),
        "{payload}"
    );
}

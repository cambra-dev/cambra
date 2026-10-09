//! Programs of several modules: an imported module's public members reached
//! through its import name, and labels that belong to a module
//! (`docs/chl-spec.md`, "9. Modules").

use std::panic::{self, AssertUnwindSafe};
use std::time::Duration;

use cambra::ccl::load::{InMemory, LoadedProgram, RootFile};
use cambra::interpreter::Value;
use indoc::{formatdoc, indoc};
use rstest_log::rstest;

use super::helpers::*;
use super::panic_message::panic_message;

/// The program rooted at `root`, with `modules` as its other modules' files, by
/// module path.
fn program(root: &str, modules: &[(&str, &str)]) -> LoadedProgram {
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
fn compile_errors(program: &LoadedProgram) -> String {
    let result = panic::catch_unwind(AssertUnwindSafe(|| run_program(program)));
    let Err(payload) = result else {
        panic!("expected the program not to compile");
    };
    panic_message(&*payload)
}

fn assert_refused(program: &LoadedProgram, needle: &str) {
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
            indoc! {"
                import pricing use plus
                plus(1)
            "},
            &[
                ("base", "pub n = 5\n"),
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
#[case::type_member(
    "import catalog use Item\n",
    "the type member `catalog::Item` is not supported yet"
)]
#[case::bound_by_a_member(
    indoc! {"
        import catalog use limit
        limit = 1
    "},
    "`limit` is a `use` name, so no member of its module takes it"
)]
#[case::bound_by_a_def(
    indoc! {"
        import catalog use double
        def double(x):
            x
    "},
    "`double` is a `use` name, so no member of its module takes it"
)]
#[case::an_import_name(
    indoc! {"
        import other
        import catalog use limit as other
    "},
    "`other` is an import name, so no binder in its module takes it"
)]
#[case::bound_twice(
    "import catalog use limit, double as limit\n",
    "`limit` is already a `use` name"
)]
#[case::bound_by_two_imports(
    indoc! {"
        import catalog use limit
        import other use x as limit
    "},
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

/// A `use` name spelled like a registered source is refused: the source resolves by its
/// spelling before scope is consulted, so the name would never reach its member.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_use_name_spelled_like_a_source_is_refused() {
    use cambra::ccl::{BaseType, Type};
    use cambra::interpreter::{Extent, TestDataSource};
    let mut ctx = cambra::ccl::context::GlobalContext::default();
    ctx.register_source(std::rc::Rc::new(std::cell::RefCell::new(
        TestDataSource::new(
            "orders",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ),
    )));
    let program = program(
        "import catalog use double as orders\n1\n",
        &[("catalog", CATALOG)],
    );
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        run_program_with_ctx(&mut ctx, &program)
    }));
    let Err(payload) = result else {
        panic!("expected the program not to compile");
    };
    let errors = panic_message(&*payload);
    assert!(
        errors.contains("`orders` is a registered source"),
        "{errors}"
    );
}

#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_private_member_is_refused_with_its_declaration() {
    let errors = compile_errors(&program(
        indoc! {"
            import catalog
            catalog::hidden
        "},
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
            indoc! {"
                import catalog
                catalog::missing
            "},
            &[("catalog", CATALOG)],
        ),
        "module `catalog` has no member `missing`",
    );
}

/// A label written in a module is that module's: the library's `price` is
/// `catalog::price` to the root, and the root's own `price` is another label.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_label_belongs_to_the_module_that_writes_it() {
    let root = |body: &str| {
        formatdoc! {"
            import catalog
            {body}
        "}
    };
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

/// `Option` is one type in every module, so a library's lookup result matches the
/// root's `Option::some`.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn option_is_one_type_in_every_module() {
    check_program_scalar(
        &program(
            indoc! {"
                import prices
                match prices::find(1):
                    case Option::some(v):
                        v
                    case Option::none:
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

/// Importing a module that performs IO is an error at the `import`, pointing at
/// the IO (`docs/chl-spec.md`, "9.7 Importing asserts no IO"): a sink it binds, or
/// a source it reads.
#[rstest]
#[case::a_sink(indoc! {"
    out = test_sink()
    out << 1
"}, "out = test_sink()")]
#[case::a_source(indoc! {"
    pub xs = stdin()
"}, "pub xs = stdin()")]
#[timeout(Duration::from_secs(10))]
fn importing_a_module_that_performs_io_is_refused(#[case] audit: &str, #[case] io: &str) {
    let errors = compile_errors(&program(
        indoc! {"
            import audit
            1
        "},
        &[("audit", audit)],
    ));
    assert!(
        errors.contains("module `audit` performs IO, so importing it is an error"),
        "{errors}"
    );
    assert!(errors.contains("the IO it performs"), "{errors}");
    assert!(errors.contains(io), "{errors}");
}

#[rstest]
#[case::module_as_a_value(indoc! {"
    import catalog
    catalog
"}, "`catalog` names a module")]
#[case::import_name_rebound(
    indoc! {"
        import catalog
        catalog = 1
        catalog
    "},
    "`catalog` is an import name, so no binder in its module takes it"
)]
#[case::import_name_as_a_parameter(
    indoc! {"
        import catalog
        def f(catalog):
            1
        f(2)
    "},
    "`catalog` is an import name"
)]
#[case::type_member(
    indoc! {"
        import catalog
        x: catalog::Item = 1
        x
    "},
    "the type member `catalog::Item`"
)]
#[case::unknown_qualifier("(nope::a=1).a\n", "`nope` is not an import name of this module")]
#[case::value_qualified_by_this("this::a\n", "`this` qualifies a label or a tag")]
#[case::member_of_a_run("shop::eu::stock\n", "names a member of a run")]
#[case::second_import_of_a_name(
    indoc! {"
        import catalog
        import other as catalog
        1
    "},
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
#[case::expression_statement(indoc! {"
    pub x = 1
    x + 1
"}, "an imported module has none")]
#[case::mutable_state(
    "stock := 1\n",
    "mutable state in an imported module is not supported yet"
)]
#[case::top_level_loop(indoc! {"
    for x in [1]:
        pass
"}, "an imported module holds value bindings")]
#[case::public_name_bound_twice(
    indoc! {"
        pub x = 1
        x = 2
    "},
    "`x` is public, so it is bound exactly once at its module's top level"
)]
#[timeout(Duration::from_secs(10))]
fn an_unsupported_library_statement_is_refused(#[case] library: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            indoc! {"
                import lib
                1
            "},
            &[("lib", library)],
        ),
        needle,
    );
}

/// A reference or a `use` item into a module with errors of its own reports
/// nothing more: the module's errors account for it.
#[rstest]
#[case::qualified(indoc! {"
    import lib
    lib::missing
"})]
#[case::used(indoc! {"
    import lib use missing
    missing
"})]
#[timeout(Duration::from_secs(10))]
fn a_reference_into_a_module_with_errors_adds_no_error(#[case] root: &str) {
    let errors = compile_errors(&program(root, &[("lib", "pub x = = 1\n")]));
    assert!(!errors.contains("has no member"), "{errors}");
    assert!(!errors.contains("missing"), "{errors}");
}

/// A module two others import is evaluated once: its bindings stand once in the
/// linked tree, ahead of both importers' (`docs/chl-spec.md`, "9.7 Importing
/// asserts no IO").
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
            (
                "left",
                indoc! {"
                    import base
                    pub n = base::shared + 1
                "},
            ),
            (
                "right",
                indoc! {"
                    import base
                    pub n = base::shared + 2
                "},
            ),
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
        indoc! {"
            import lib
            x: {Int where _ > lib::limit} = 5
            x
        "},
        &[(
            "lib",
            indoc! {"
                Small = Int
                pub limit: Small = 10
            "},
        )],
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
        indoc! {"
            import catalog
            x: {Int where _ > catalog::limit} = 5
            x
        "},
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
        indoc! {"
            import base
            base::n
        "},
        &[("base", "pub n = 1\n")],
    ));
    assert!(payload.contains(r#""payloadKind": "failed""#), "{payload}");
    assert!(
        payload.contains("a program of several modules is not supported yet"),
        "{payload}"
    );
}

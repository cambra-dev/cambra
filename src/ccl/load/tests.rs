use super::*;
use crate::ccl::context::render_errors;
use indoc::indoc;
use std::sync::atomic::{AtomicUsize, Ordering};

fn path(spelled: &str) -> ModulePath {
    ModulePath::new(spelled.split("::").map(SmolStr::from))
}

/// The program rooted at module `main`, `text`, with `files` as its other
/// modules.
fn load(text: &str, files: InMemory) -> LoadedProgram {
    load_std(text, files, &[])
}

fn load_std(text: &str, mut files: InMemory, std: &[(&str, &str)]) -> LoadedProgram {
    let root = RootFile {
        path: "main.cambra".to_owned(),
        module: Some(path("main")),
        text: text.to_owned(),
    };
    load_with(root, &mut files, std)
}

/// How diagnostics name each module of `files`.
fn names(program: &LoadedProgram, files: &[FileId]) -> Vec<String> {
    files
        .iter()
        .map(|&file| module_name(program.sources(), file))
        .collect()
}

fn messages(program: &LoadedProgram) -> Vec<String> {
    program
        .compile_errors()
        .iter()
        .map(CompileError::message)
        .collect()
}

/// The text a span of `program` covers.
fn text_at(program: &LoadedProgram, span: Span) -> &str {
    &program.sources().text(span.file)[span.start..span.end]
}

#[test]
fn a_program_of_one_file_loads_it_alone() {
    let program = LoadedProgram::test("x = 1\n");
    assert!(messages(&program).is_empty());
    assert_eq!(names(&program, program.link_order().unwrap()), ["<test>"]);
}

#[test]
fn imports_and_runs_load_each_module_once() {
    let program = load(
        indoc! {"
            import catalog
            run shop
        "},
        InMemory::default()
            .with("catalog", "pub limit = 10\n")
            .with("shop", "import catalog\nrun audit::log\n")
            .with("audit::log", "x = 1\n"),
    );
    assert!(messages(&program).is_empty(), "{:?}", messages(&program));
    assert_eq!(program.sources().files().count(), 4);
    assert_eq!(
        names(&program, program.link_order().unwrap()),
        ["audit::log", "catalog", "shop", "main"]
    );
    let shop = program.module(program.sources().root()).edges[1].target;
    let kinds: Vec<_> = program
        .edges(shop)
        .map(|(kind, target)| (kind, module_name(program.sources(), target)))
        .collect();
    assert_eq!(
        kinds,
        [
            (EdgeKind::Import, "catalog".to_owned()),
            (EdgeKind::Run, "audit::log".to_owned())
        ]
    );
    assert_eq!(program.sources().path(shop), "shop.cambra");
}

/// Ties in the link order break by module path, so neither the order of
/// statements nor the order modules are found in changes it.
#[test]
fn the_link_order_does_not_follow_statement_order() {
    let files = || {
        InMemory::default()
            .with("alpha", "x = 1\n")
            .with("mid", "import alpha\n")
            .with("zeta", "x = 1\n")
    };
    for root in [
        "run zeta\nimport mid\nimport alpha\n",
        "import alpha\nimport mid\nrun zeta\n",
    ] {
        let program = load(root, files());
        assert_eq!(
            names(&program, program.link_order().unwrap()),
            ["alpha", "mid", "zeta", "main"],
            "{root}"
        );
    }
}

#[test]
fn pub_run_names_a_module() {
    let program = load(
        "pub run shop as eu\n",
        InMemory::default().with("shop", "x = 1\n"),
    );
    assert!(messages(&program).is_empty(), "{:?}", messages(&program));
    assert_eq!(
        names(&program, program.link_order().unwrap()),
        ["shop", "main"]
    );
}

#[test]
fn each_statement_naming_a_missing_module_is_an_error_at_its_path() {
    let program = load(
        indoc! {"
            import shop::cart
            run shop::cart as eu
        "},
        InMemory::default(),
    );
    let errors = program.compile_errors();
    assert_eq!(errors.len(), 2, "{:?}", messages(&program));
    for error in &errors {
        assert_eq!(
            error.message(),
            "no module `shop::cart`: there is no file `shop/cart.cambra`"
        );
        assert_eq!(text_at(&program, error.span().unwrap()), "shop::cart");
    }
    assert!(program.link_order().is_some());
}

/// Only top-level statements name modules. A nested `import` is refused by
/// lowering and loads nothing.
#[test]
fn a_nested_import_names_no_module() {
    let program = load(
        indoc! {"
            def f():
                import shop
                1
        "},
        InMemory::default(),
    );
    assert!(messages(&program).is_empty(), "{:?}", messages(&program));
    assert_eq!(program.sources().files().count(), 1);
}

/// A segment the parser refuses names no module, so the parse error is the
/// only one.
#[test]
fn a_refused_segment_names_no_module() {
    let program = load("import Shop\n", InMemory::default());
    let messages = messages(&program);
    assert_eq!(messages.len(), 1, "{messages:?}");
    assert!(
        messages[0].contains("must begin with a lowercase letter"),
        "{messages:?}"
    );
}

#[test]
fn every_files_parse_errors_are_reported() {
    let program = load(
        indoc! {"
            import a
            import b
            x = = 1
        "},
        InMemory::default()
            .with("a", "y = = 2\n")
            .with("b", "z = 1\n"),
    );
    let files: Vec<_> = program
        .compile_errors()
        .iter()
        .map(|e| program.sources().path(e.span().unwrap().file).to_owned())
        .collect();
    assert!(files.contains(&"main.cambra".to_owned()), "{files:?}");
    assert!(files.contains(&"a.cambra".to_owned()), "{files:?}");
    assert!(!files.contains(&"b.cambra".to_owned()), "{files:?}");
}

#[test]
fn a_cycle_is_refused_with_a_label_at_each_statement() {
    let program = load(
        "import a\n",
        InMemory::default()
            .with("a", "import b\n")
            .with("b", "x = 1\nrun a\n"),
    );
    assert!(program.link_order().is_none());
    let errors = program.compile_errors();
    assert_eq!(errors.len(), 1, "{:?}", messages(&program));
    assert_eq!(
        errors[0].message(),
        "the module graph has a cycle: `a` imports `b`, `b` runs `a`"
    );
    let rendered = render_errors(&errors, program.sources());
    assert!(rendered.contains("a.cambra:1:8"), "{rendered}");
    assert!(rendered.contains("b.cambra:2:5"), "{rendered}");
    assert!(
        rendered.contains("`a` imports `b`") && rendered.contains("`b` runs `a`"),
        "{rendered}"
    );
}

#[test]
fn a_module_that_runs_itself_is_a_cycle() {
    let program = load("run a\n", InMemory::default().with("a", "run a\n"));
    assert_eq!(
        messages(&program),
        ["the module graph has a cycle: `a` runs `a`"]
    );
}

/// A module naming the root reaches the root's own file, not a second copy.
#[test]
fn a_module_that_imports_the_root_is_a_cycle() {
    let program = load(
        "import lib\n",
        InMemory::default().with("lib", "import main\n"),
    );
    assert_eq!(program.sources().files().count(), 2);
    assert_eq!(
        messages(&program),
        ["the module graph has a cycle: `lib` imports `main`, `main` imports `lib`"]
    );
}

/// Two cycles in separate components are each reported, in the order of their
/// least modules.
#[test]
fn each_cyclic_component_is_reported() {
    let program = load(
        "import z\nimport a\n",
        InMemory::default()
            .with("a", "import b\n")
            .with("b", "import a\n")
            .with("z", "import y\n")
            .with("y", "import z\n"),
    );
    assert_eq!(
        messages(&program),
        [
            "the module graph has a cycle: `a` imports `b`, `b` imports `a`",
            "the module graph has a cycle: `y` imports `z`, `z` imports `y`",
        ]
    );
}

#[test]
fn a_std_path_resolves_against_the_std_root() {
    let program = load(
        indoc! {"
            import std::http
            import std
        "},
        InMemory::default().with("std", "x = 1\n"),
    );
    assert_eq!(
        messages(&program),
        [
            "no module `std::http`: the std root has no module `http`",
            "`std` is the std root, not a module",
        ]
    );

    let program = load_std(
        "import std::http as web\n",
        InMemory::default(),
        &[("std::http", "pub def ok(body):\n    body\n")],
    );
    assert!(messages(&program).is_empty(), "{:?}", messages(&program));
    let order = program.link_order().unwrap();
    assert_eq!(names(&program, order), ["std::http", "main"]);
    assert_eq!(program.sources().path(order[0]), "<std>/http.cambra");
}

/// A directory of module files, removed when dropped.
struct ModuleRoot(PathBuf);

impl ModuleRoot {
    fn new(files: &[(&str, &str)]) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "cambra-load-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        for (file, text) in files {
            let file = dir.join(file);
            std::fs::create_dir_all(file.parent().unwrap()).unwrap();
            std::fs::write(file, text).unwrap();
        }
        ModuleRoot(dir)
    }

    fn read(&self, root: &str) -> Result<LoadedProgram, String> {
        LoadedProgram::read(&self.0.join(root))
    }
}

impl Drop for ModuleRoot {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

use std::path::PathBuf;

#[test]
fn disk_files_resolve_under_the_root_files_directory() {
    let dir = ModuleRoot::new(&[
        ("deploy.cambra", "import shop::cart\n"),
        ("shop/cart.cambra", "pub limit = 10\n"),
    ]);
    let program = dir.read("deploy.cambra").unwrap();
    assert!(messages(&program).is_empty(), "{:?}", messages(&program));
    let order = program.link_order().unwrap();
    assert_eq!(names(&program, order), ["shop::cart", "deploy"]);
    assert_eq!(
        program.sources().path(order[0]),
        dir.0.join("shop/cart.cambra").display().to_string()
    );
}

#[test]
fn a_missing_disk_file_names_where_it_would_be() {
    let dir = ModuleRoot::new(&[("deploy.cambra", "import shop::cart\n")]);
    let program = dir.read("deploy.cambra").unwrap();
    assert_eq!(
        messages(&program),
        [format!(
            "no module `shop::cart`: there is no file `{}`",
            dir.0.join("shop/cart.cambra").display()
        )]
    );
}

#[test]
fn a_disk_file_differing_in_case_is_not_the_module() {
    let dir = ModuleRoot::new(&[
        ("deploy.cambra", "import cart\n"),
        ("Cart.cambra", "x = 1\n"),
    ]);
    let program = dir.read("deploy.cambra").unwrap();
    assert_eq!(
        messages(&program),
        [format!(
            "no module `cart`: there is no file `{}`, and `{}` differs from it in case",
            dir.0.join("cart.cambra").display(),
            dir.0.join("Cart.cambra").display()
        )]
    );
}

#[cfg(unix)]
#[test]
fn a_disk_file_two_module_paths_reach_is_refused() {
    let dir = ModuleRoot::new(&[
        ("deploy.cambra", "import a\nimport b\n"),
        ("a.cambra", "x = 1\n"),
    ]);
    std::os::unix::fs::symlink(dir.0.join("a.cambra"), dir.0.join("b.cambra")).unwrap();
    let program = dir.read("deploy.cambra").unwrap();
    assert_eq!(
        messages(&program),
        [format!(
            "module `b` is the file `{}`, which is already module `a`; a file is one module",
            dir.0.join("b.cambra").display()
        )]
    );
}

#[test]
fn the_root_files_name_is_its_module_path() {
    let dir = ModuleRoot::new(&[
        ("deploy.cambra", "import lib\n"),
        ("lib.cambra", "import deploy\n"),
        ("My-App.cambra", "x = 1\n"),
        ("std.cambra", "x = 1\n"),
        ("prog.chl", "x = 1\n"),
    ]);
    // The root is module `deploy`, so `lib` importing it closes a cycle rather
    // than reading the file again.
    let program = dir.read("deploy.cambra").unwrap();
    assert_eq!(
        messages(&program),
        ["the module graph has a cycle: `deploy` imports `lib`, `lib` imports `deploy`"]
    );

    for (root, why) in [
        ("My-App.cambra", "is not an identifier"),
        ("std.cambra", "is the std root"),
        ("prog.chl", "is not a `.cambra` file"),
        ("absent.cambra", "cannot read"),
    ] {
        let err = dir.read(root).unwrap_err();
        assert!(err.contains(why), "{root}: {err}");
    }
}

/// Compiling a program of several modules reports every file's errors together,
/// and a reference into a module with errors of its own adds none.
#[test]
fn a_program_of_several_modules_reports_every_files_errors() {
    use crate::ccl::context::{Phase, compile_to};
    let program = load(
        indoc! {"
            import lib
            import gone
            lib::y + gone::z
        "},
        InMemory::default().with("lib", "pub y = = 2\n"),
    );
    let errors = compile_to(&program, Phase::Lower).unwrap_err();
    let located: Vec<(&str, String)> = errors
        .iter()
        .map(|e| {
            let span = e.span().unwrap();
            (program.sources().path(span.file), e.message())
        })
        .collect();
    assert_eq!(located.len(), 2, "{located:#?}");
    assert_eq!(located[0].0, "lib.cambra");
    assert_eq!(
        located[1],
        (
            "main.cambra",
            "no module `gone`: there is no file `gone.cambra`".to_owned()
        )
    );
}

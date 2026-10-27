//! The std root's CHL sources (`stdlib/README.md`), loaded through the programs under
//! `stdlib/tests/` that import or run them.
//!
//! The compiler does not embed the std root, so each program loads against the sources under
//! `stdlib/src/` in its place ([`LoadedProgram::load_with_std`]). Every std module uses constructs the
//! compiler lacks, so the programs are loaded and not compiled: each program, and every std module
//! it reaches, must parse and resolve its module paths. The `[proposed]` lines in the modules record
//! what each one waits on.

use std::path::{Path, PathBuf};

use cambra::ccl::context::render_errors;
use cambra::ccl::load::{InMemory, LoadedProgram, RootFile};
use chl_parser::ModulePath;

fn stdlib() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib")
}

/// The std modules' sources: a module's file is its path under this directory, `std` included.
fn std_root() -> PathBuf {
    stdlib().join("src")
}

/// The directory of the programs that load the std modules.
fn std_tests() -> PathBuf {
    stdlib().join("tests")
}

fn cambra_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        .map(|entry| entry.expect("a readable directory entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "cambra"))
        .collect();
    files.sort();
    files
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()))
}

/// Every std module, by module path and source text: `stdlib/src/std/time.cambra` is
/// `std::time` (`docs/chl-spec.md`, "9.15 Module files").
fn std_modules() -> Vec<(String, String)> {
    let root = std_root();
    let mut found = Vec::new();
    let mut pending = vec![root.clone()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).expect("a std directory is readable") {
            let path = entry.expect("a readable directory entry").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|e| e == "cambra") {
                let rel = path
                    .strip_prefix(&root)
                    .expect("a walked file is under the std root")
                    .with_extension("");
                let segments: Vec<String> = rel
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect();
                found.push((segments.join("::"), read(&path)));
            }
        }
    }
    found.sort();
    assert!(
        !found.is_empty(),
        "no .cambra file under {}: the walk is wrong, not the std root",
        root.display()
    );
    found
}

/// `program` loaded against the std modules `std`. Diagnostics name the root by its path under
/// `stdlib/`, `tests/<name>.cambra`.
fn load(program: &Path, std: &[(String, String)]) -> LoadedProgram {
    let name = program.file_name().expect("a program has a file name");
    let root = RootFile {
        path: format!("tests/{}", name.to_string_lossy()),
        module: None,
        text: read(program),
    };
    let std: Vec<(&str, &str)> = std
        .iter()
        .map(|(path, text)| (path.as_str(), text.as_str()))
        .collect();
    LoadedProgram::load_with_std(root, &mut InMemory::default(), &std)
}

#[test]
fn every_std_program_parses_and_loads() {
    let std = std_modules();
    let programs = cambra_files(&std_tests());
    assert!(!programs.is_empty(), "no program under stdlib/tests/");
    let failures: Vec<String> = programs
        .iter()
        .filter_map(|program| {
            let loaded = load(program, &std);
            let errors = loaded.compile_errors();
            (!errors.is_empty()).then(|| {
                format!(
                    "{}:\n{}",
                    program.display(),
                    render_errors(&errors, loaded.sources())
                )
            })
        })
        .collect();
    assert!(
        failures.is_empty(),
        "these programs or the std modules they reach do not parse and load:\n{}",
        failures.join("\n")
    );
}

/// A std module no program loads is parsed by nothing.
#[test]
fn every_std_module_is_loaded_by_a_program() {
    let std = std_modules();
    let loaded: Vec<LoadedProgram> = cambra_files(&std_tests())
        .iter()
        .map(|program| load(program, &std))
        .collect();
    let unloaded: Vec<&str> = std
        .iter()
        .map(|(path, _)| path.as_str())
        .filter(|path| {
            let module = ModulePath::new(path.split("::").map(Into::into));
            loaded.iter().all(|l| l.file_of(&module).is_none())
        })
        .collect();
    assert!(
        unloaded.is_empty(),
        "no program under stdlib/tests/ imports or runs {unloaded:?}"
    );
}

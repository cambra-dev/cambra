//! The std root's CHL sources (`std/README.md`), compiled through the programs under
//! `std/tests/` that import or run them.
//!
//! The compiler does not embed the std root, so each program loads against the sources under
//! `std/` in its place ([`LoadedProgram::load_with_std`]). Every std module uses constructs the
//! compiler lacks, so a program's compile errors are pinned rather than required to be empty: each
//! program that fails to compile has a golden `.errors` file beside it holding its rendered errors,
//! and a program that compiles has none. `CAMBRA_BLESS=1` rewrites the goldens. A construct that
//! lands changes a golden, and the diff shows which error it removed.

use std::path::{Path, PathBuf};

use cambra::ccl::context::{GlobalContext, compile_program, render_errors};
use cambra::ccl::load::{InMemory, LoadedProgram, RootFile};
use cambra::interpreter::Consumer;
use chl_parser::ModulePath;

fn std_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("std")
}

/// The directory of the programs that compile the std modules. It is not a std module.
fn std_tests() -> PathBuf {
    std_root().join("tests")
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

/// Every std module, by module path and source text: `std/time/timer.cambra` is
/// `std::time::timer` (`docs/chl-spec.md`, "9.15 Module files").
fn std_modules() -> Vec<(String, String)> {
    let root = std_root();
    let mut found = Vec::new();
    let mut pending = vec![root.clone()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).expect("a std directory is readable") {
            let path = entry.expect("a readable directory entry").path();
            if path.is_dir() {
                if path != std_tests() {
                    pending.push(path);
                }
            } else if path.extension().is_some_and(|e| e == "cambra") {
                let rel = path
                    .strip_prefix(&root)
                    .expect("a walked file is under the std root")
                    .with_extension("");
                let segments: Vec<String> = rel
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect();
                found.push((format!("std::{}", segments.join("::")), read(&path)));
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
/// the std root, `tests/<name>.cambra`.
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

/// The rendered compile errors of `loaded`, or `None` when it compiles.
fn compile_errors(loaded: &LoadedProgram) -> Option<String> {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    compile_program(&mut ctx, loaded, consumer)
        .err()
        .map(|errs| render_errors(&errs, loaded.sources()))
}

#[test]
fn every_std_program_matches_its_golden_errors() {
    let std = std_modules();
    let programs = cambra_files(&std_tests());
    assert!(!programs.is_empty(), "no program under std/tests/");
    let bless = std::env::var_os("CAMBRA_BLESS").is_some();
    let mut differ = Vec::new();
    for program in &programs {
        let errors = compile_errors(&load(program, &std));
        let golden_path = program.with_extension("errors");
        if bless {
            match &errors {
                Some(errors) => std::fs::write(&golden_path, errors).expect("writing a golden"),
                None if golden_path.exists() => {
                    std::fs::remove_file(&golden_path).expect("removing a golden")
                }
                None => {}
            }
        }
        let golden = std::fs::read_to_string(&golden_path).ok();
        if errors != golden {
            differ.push(program.display().to_string());
        }
    }
    assert!(
        differ.is_empty(),
        "these programs' compile errors differ from their goldens: {differ:#?}; if the change is \
         intended, re-run with CAMBRA_BLESS=1 and review the goldens' diff"
    );
    for entry in std::fs::read_dir(std_tests()).expect("reading std/tests/") {
        let golden = entry.expect("a directory entry").path();
        if golden.extension().is_some_and(|e| e == "errors") {
            assert!(
                golden.with_extension("cambra").exists(),
                "{} has no program",
                golden.display()
            );
        }
    }
}

/// A std module no program loads is compiled by nothing, so its errors go unpinned.
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
        "no program under std/tests/ imports or runs {unloaded:?}"
    );
}

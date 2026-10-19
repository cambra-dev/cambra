//! The test tree's placement rules, checked. Cargo builds every top-level `tests/*.rs` and
//! `tests/*/main.rs` as a test binary of its own, and rustc compiles only the module files a
//! `mod` line names. A misplaced test file is therefore an extra binary, each of which
//! statically links the whole library, or a file nothing compiles; neither fails a build.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

fn tests_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

/// The `name` of each `[[test]]` table in `manifest`.
fn declared_test_targets(manifest: &str) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut in_test_table = false;
    for line in manifest.lines().map(str::trim) {
        if line.starts_with('[') {
            in_test_table = line == "[[test]]";
        } else if in_test_table
            && let Some(name) = line
                .strip_prefix("name = \"")
                .and_then(|rest| rest.strip_suffix('"'))
        {
            names.insert(name.to_string());
        }
    }
    names
}

/// The test targets Cargo discovers in `tests`: each `*.rs` file and each directory holding
/// a `main.rs`, by target name.
fn autodiscovered_targets(tests: &Path) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for entry in fs::read_dir(tests).expect("tests/ is readable") {
        let path = entry.expect("tests/ entry is readable").path();
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        if path.extension().is_some_and(|ext| ext == "rs") || path.join("main.rs").is_file() {
            names.insert(stem);
        }
    }
    names
}

#[test]
fn every_top_level_test_file_is_a_declared_target() {
    let manifest = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"))
        .expect("Cargo.toml is readable");
    let declared = declared_test_targets(&manifest);
    let undeclared: Vec<String> = autodiscovered_targets(&tests_dir())
        .into_iter()
        .filter(|name| name != "it" && !declared.contains(name))
        .collect();
    assert!(
        undeclared.is_empty(),
        "{undeclared:?} build as test binaries of their own, and each links the whole library. \
         Move the file under `tests/it/` and add a `mod` line to `tests/it/main.rs`, or, if it \
         cannot share a process, declare it as a `[[test]]` in `Cargo.toml` saying why."
    );
}

/// The file whose `mod` lines name the modules inside `dir`, for a module tree rooted at
/// `root_dir` with crate-or-module root `root_file`.
fn module_file_of_dir(dir: &Path, root_dir: &Path, root_file: &Path) -> PathBuf {
    if dir == root_dir {
        root_file.to_path_buf()
    } else if dir.join("mod.rs").is_file() {
        dir.join("mod.rs")
    } else {
        dir.with_extension("rs")
    }
}

/// Whether `source` has a `mod name;` item, `pub` or not.
fn declares_module(source: &str, name: &str) -> bool {
    let item = format!("{name};");
    source.lines().any(|line| {
        let mut tokens = line.split_whitespace().rev();
        tokens.next() == Some(item.as_str()) && tokens.next() == Some("mod")
    })
}

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).expect("test directory is readable") {
        let path = entry.expect("test directory entry is readable").path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// Every `.rs` file in each module tree whose parent module has no `mod` line for it.
///
/// The trees are `it`'s and the gallery's. The support modules under `tests/support/`,
/// `tests/type_gen/` and `tests/alloc_probe/` are mounted with `#[path]` from several roots,
/// which this textual walk does not follow.
#[test]
fn every_module_file_is_declared_by_its_parent() {
    let tests = tests_dir();
    let trees = [
        (tests.join("it"), tests.join("it/main.rs")),
        (tests.join("programs"), tests.join("programs/mod.rs")),
    ];
    let mut orphans = Vec::new();
    for (root_dir, root_file) in &trees {
        let mut files = Vec::new();
        rust_files(root_dir, &mut files);
        for file in files.iter().filter(|file| *file != root_file) {
            let dir = file.parent().unwrap();
            let (parent, name) = if file.file_name().unwrap() == "mod.rs" {
                let grandparent = dir.parent().unwrap();
                (
                    module_file_of_dir(grandparent, root_dir, root_file),
                    dir.file_name().unwrap().to_string_lossy().into_owned(),
                )
            } else {
                (
                    module_file_of_dir(dir, root_dir, root_file),
                    file.file_stem().unwrap().to_string_lossy().into_owned(),
                )
            };
            let declared =
                fs::read_to_string(&parent).is_ok_and(|source| declares_module(&source, &name));
            if !declared {
                orphans.push(format!(
                    "{} (no `mod {name};` in {})",
                    file.strip_prefix(&tests).unwrap().display(),
                    parent.strip_prefix(&tests).unwrap_or(&parent).display(),
                ));
            }
        }
    }
    assert!(
        orphans.is_empty(),
        "module files nothing compiles, so their tests never run:\n  {}",
        orphans.join("\n  ")
    );
}

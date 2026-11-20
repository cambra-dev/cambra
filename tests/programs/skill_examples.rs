//! The example programs of the `cambra-coding` skill, compiled and run.
//!
//! The skill teaches CHL through the commented programs in
//! `.claude/skills/cambra-coding/examples/`, and an agent imitates them. Each test asserts the result
//! its example's header comment states, so an example that stops compiling, or starts answering
//! differently, fails here rather than teaching a stale form. The tests live outside the skill so
//! that the skill directory holds only what an agent reads.

use std::{collections::BTreeSet, fs, path::Path, path::PathBuf};

use super::common::{expect_scalar, expect_scalar_file, expect_stdin_file};
use super::serving::{compile_sink, exchange, http_get, http_post, reserve_test_port};

/// Run `test` on a thread with a 16 MB stack. Compiling an example recurses deeper than a debug
/// build's 2 MB test thread holds: several passes, `ccl_utils::reduce_application` and exception
/// elimination's `elim` among them, recurse without `stacker::maybe_grow`. The `cambra` binary
/// compiles on its 8 MB main thread and does not overflow.
fn on_large_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(test)
        .expect("test thread spawns")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(".claude/skills/cambra-coding/examples")
}

/// Every example's path relative to [`examples_dir`]. A test below runs each one.
const EXAMPLES: &[&str] = &[
    "sales_report.cambra",
    "inventory_service.cambra",
    "command_stream.cambra",
    "modules/shop.cambra",
    "modules/ledger.cambra",
    "modules/pricing.cambra",
];

#[test]
fn sales_report() {
    on_large_stack(|| {
        expect_scalar(
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/.claude/skills/cambra-coding/examples/sales_report.cambra"
            )),
            r#"(by_customer: Function [ "ada" -> 1215, "bo" -> 1500 ], largest: 1500)"#,
        );
    });
}

#[test]
fn inventory_service() {
    on_large_stack(inventory_exchange);
}

fn inventory_exchange() {
    let port = reserve_test_port();
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/.claude/skills/cambra-coding/examples/inventory_service.cambra"
    ))
    .replace("\"8080\"", &format!("\"{port}\""));
    let mut ctx = compile_sink(&source);

    let replies = exchange(&mut ctx, move || {
        [
            http_post(port, "/reserve", "pen"),
            http_post(port, "/reserve", "pen"),
            http_post(port, "/reserve", "ink"),
            http_post(port, "/reserve", "cap"),
            http_post(port, "/restock", "ink"),
            http_post(port, "/restock", "cap"),
            http_post(port, "/reserve", "ink"),
            http_get(port, "/last"),
        ]
    });
    assert_eq!(
        replies,
        [
            "reserved pen",
            "sold out: pen",
            "sold out: ink",
            "sold out: cap",
            "restocked ink",
            "unknown cap",
            "reserved ink",
            "ink",
        ]
    );
}

#[test]
fn command_stream() {
    expect_stdin_file(
        &examples_dir().join("command_stream.cambra"),
        "inc\ninc\n\nreset\ninc\ndec\ninc\ninc\n",
        &["Ints(\n        [\n            2,"],
    );
}

/// `shop.cambra` is the root; it runs `ledger.cambra`, which imports `pricing.cambra`.
#[test]
fn modules() {
    on_large_stack(|| expect_scalar_file(&examples_dir().join("modules/shop.cambra"), "702"));
}

#[test]
fn every_example_is_tested() {
    fn cambra_files(dir: &Path, root: &Path, found: &mut BTreeSet<String>) {
        for entry in fs::read_dir(dir).expect("examples directory is readable") {
            let path = entry.expect("examples entry is readable").path();
            if path.is_dir() {
                cambra_files(&path, root, found);
            } else if path.extension().is_some_and(|ext| ext == "cambra") {
                let relative = path.strip_prefix(root).unwrap().to_string_lossy();
                found.insert(relative.into_owned());
            }
        }
    }
    let root = examples_dir();
    let mut found = BTreeSet::new();
    cambra_files(&root, &root, &mut found);
    let listed: BTreeSet<String> = EXAMPLES.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        found, listed,
        "each example under `.claude/skills/cambra-coding/examples/` needs a test in this file \
         and an entry in `EXAMPLES`"
    );
}

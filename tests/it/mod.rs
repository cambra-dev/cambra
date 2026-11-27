//! The integration tests, as a `cfg(test)` module of the library (`src/lib.rs`).
//!
//! They are part of the library's own test build rather than a crate linking the library, so
//! the suite compiles the library once: a test crate would need the library compiled again
//! without `cfg(test)`, the largest compile in the suite. They still reach it through its
//! public paths, `cambra::` (the library names itself so in test builds), and each file under
//! `tests/it/` is a module here. The tests that cannot be part of the suite are top-level
//! `tests/*.rs` files, each declared as a `[[test]]` in `Cargo.toml` with the reason;
//! [`test_layout`] fails on a top-level file that is not, and on a module file no `mod` line
//! names.

// Support modules the test modules share, mounted once: a file loaded as two
// modules of one crate is two copies of it (`clippy::duplicate_mod`).
#[path = "../support/differential.rs"]
mod differential;
#[path = "../support/panic_message.rs"]
mod panic_message;
#[path = "../support/quiet_panics.rs"]
mod quiet_panics;
#[path = "../support/serving.rs"]
mod serving;
#[path = "../type_gen/mod.rs"]
mod type_gen;

mod alloc_probe;
mod binding_nodes;
mod chl_parser_roundtrip;
mod cli_driver_convergence;
mod compilation_pipeline;
mod constraint_order_fuzz;
mod differential_interp;
mod editor_grammars;
mod generated_pairs;
mod hot_reload;
mod http_server;
mod inference_variants;
mod inspector_wire;
mod live_keys_readers;
mod loop_body_binding_cost;
mod nested_extract_allocations;
mod nested_filter_cost;
mod predicate_sharing;
mod predicate_sharing_review;
mod program_teardown;
// The gallery stays at `tests/programs/`: its `program.cambra` paths are read at run time
// and recorded in the inspector's dumps (`inspector_wire.rs`). Its root is `mod.rs` rather than
// `main.rs`, which autodiscovery would build as a binary of its own.
#[path = "../programs/mod.rs"]
mod programs;
mod reserve_port;
mod scope_walk_allocations;
mod std_root;
mod subtype_transitivity_fuzz;
mod test_layout;
mod test_sink;
mod type_check;

/// The `cambra` command line, run as this test executable.
///
/// The suite builds no `cambra` executable: that would need the library compiled again
/// without `cfg(test)` (`Cargo.toml`, above the `[[bin]]`). A test spawns this executable
/// instead, with [`AS_CLI`] set, and [`run_as_cli`] runs the command line before libtest's
/// `main` starts, exiting with its status.
pub(crate) mod cli {
    use std::path::PathBuf;
    use std::process::Command;

    /// Set in a spawned test executable's environment to make it the command line.
    pub(crate) const AS_CLI: &str = "CAMBRA_TEST_AS_CLI";

    /// This test executable, which runs as `cambra` under [`AS_CLI`]: for a caller that
    /// spawns it through another program and sets [`AS_CLI`] there.
    pub(crate) fn executable() -> PathBuf {
        std::env::current_exe().expect("the test executable has a path")
    }

    /// `cambra`, with no arguments yet.
    pub(crate) fn command() -> Command {
        let mut command = Command::new(executable());
        command.env(AS_CLI, "1");
        command
    }

    /// Runs the command line and exits, when this process was spawned as it.
    ///
    /// This runs before `main`, so before the start-up an executable's `main` gets: it
    /// ignores `SIGPIPE` here as that start-up would, so a write to a closed pipe is an
    /// error the command line reports rather than a signal that kills it. A panic exits with
    /// the status an executable's panicking `main` would, its message already printed by the
    /// panic hook.
    #[ctor::ctor(unsafe)]
    fn run_as_cli() {
        if std::env::var_os(AS_CLI).is_none() {
            return;
        }
        // SAFETY: the process is single-threaded here, before `main`, and `SIG_IGN` installs
        // no handler.
        #[cfg(unix)]
        unsafe {
            libc::signal(libc::SIGPIPE, libc::SIG_IGN);
        }
        let status = match std::panic::catch_unwind(crate::cli::main) {
            Ok(()) => 0,
            Err(_) => 101,
        };
        std::process::exit(status);
    }
}

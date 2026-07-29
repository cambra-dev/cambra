#!/usr/bin/env bash
# Use `set -x` so it's easy to pull out the failing commands.
set -euxo pipefail

ci_fmt() {
  if ((fix)); then cargo fmt; fi
  cargo fmt --check
}
# --all-targets lints the test/example/bench code too, not just the lib. It does
# *not* speed up the later `cargo test` compile: clippy runs via clippy-driver,
# which cargo fingerprints separately from plain rustc, so `test` rebuilds those
# targets regardless. That extra target-checking is why `ci_fast` drops
# `--all-targets` for the local iteration loop (it is kept here so the full gate
# still lints test code).
ci_clippy() { cargo clippy --all-targets -- -D warnings; }
# Same lint, in release. The debug checks never compile the test target in
# release, so a `#[cfg(debug_assertions)]`-gated item referenced by ungated code
# (e.g. a test calling a debug-only fn) only breaks here. `-- -D warnings` is
# scoped to our crate, not deps.
ci_clippy_release() { cargo clippy --release --all-targets -- -D warnings; }
# The `serde` feature is default-OFF, so the default passes above compile none of
# the serde-gated wire code — the hand-written `Serialize` impls and everything
# only they reach. Nothing else in the gate turns the feature on, so without this
# pass that code is compiled by nobody and its warnings (a dead `wire_str`, say)
# never surface.
ci_clippy_serde() { cargo clippy --features serde --all-targets -- -D warnings; }
# `DEEP_TYPECHECK=1` turns on the opt-in per-operation typecheck (see the
# `deep-typecheck` feature). The GitHub workflow sets it so automated runs keep
# exercising that check; it stays off for a bare local `./ci.sh` because it is
# superlinear on nested comprehensions (that cost is why it is gated).
ci_test() { cargo test -q ${DEEP_TYPECHECK:+--features deep-typecheck}; }
ci_doc() {
  RUSTDOCFLAGS="-A warnings -D rustdoc::broken_intra_doc_links" \
    cargo doc --no-deps
}
ci_shellcheck() { find . -name '*.sh' -not -path './.git/*' -exec shellcheck -a -o all {} +; }
# Validate intra-repo doc references so they can't silently rot: Markdown
# links/anchors (doc -> doc) and `<name>.md` citations in Rust comments
# (code -> doc). Stdlib Python only; no Rust toolchain needed. Unit tests for
# the checker run first so a checker bug can't mask real breakage.
ci_doc_refs() {
  python3 .github/scripts/doc-refs/test_check_doc_refs.py
  python3 .github/scripts/doc-refs/check_doc_refs.py
}

# Fast inner-loop gate for local iteration: format, lint (debug, lib+bins only),
# and test. Deliberately skips the phases whose cost is compile-bound and rarely
# relevant mid-iteration — the *release* clippy pass (~2x the debug one; only
# catches `cfg(debug_assertions)`-gated breakage), the doc build, shellcheck, and
# the doc-ref check — and drops clippy's `--all-targets` (see `ci_clippy`: it
# doubles the debug clippy time to check test targets `cargo test` then rebuilds
# anyway). Roughly a third of a full `./ci.sh` after a one-file edit. Run the
# full `./ci.sh` before pushing — CI gates on everything, and the release clippy
# pass in particular fails there if skipped locally. `--fix` still applies.
ci_fast() {
  local failed=0
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_fmt || failed=1
  # Lib+bins only (no --all-targets) — see the comment on `ci_clippy`.
  # shellcheck disable=SC2310
  { cargo clippy -- -D warnings; } || failed=1
  # shellcheck disable=SC2310
  ci_test || failed=1
  exit "${failed}"
}

ci_all() {
  local failed=0
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_shellcheck || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_doc_refs || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_fmt || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_clippy || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_clippy_release || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_clippy_serde || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_doc || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_test || failed=1
  exit "${failed}"
}

fix=0
cmd="all"
for arg in "$@"; do
  case "${arg}" in
  --fix) fix=1 ;;
  *) cmd="${arg}" ;;
  esac
done
"ci_${cmd}"

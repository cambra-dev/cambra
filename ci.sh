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
# The library alone, with no features unified in. Every pass above uses
# `--all-targets`, which pulls in the dev-dependencies — including the *self*
# dev-dependency that enables `test-helpers`. Cargo unifies that feature into the
# lib under test, so those passes only ever compile the library with
# `test-helpers` ON, and the feature-off configuration a consumer actually builds
# is compiled by nothing. Edition 2024 / resolver 3 keeps the feature out of a
# plain `cargo build --lib`, which is what makes the gap silent rather than loud:
# ungated library code calling a `test-helpers`-gated item passes the whole gate
# and fails `cargo build --lib`. Same argument as `ci_clippy_serde` — a
# configuration nothing compiles is a configuration that rots.
ci_clippy_lib() { cargo clippy --lib -- -D warnings; }
# `DEEP_TYPECHECK=1` turns on the opt-in per-operation typecheck (see the
# `deep-typecheck` feature). The GitHub workflow sets it so automated runs keep
# exercising that check; it stays off for a bare local `./ci.sh` because it is
# superlinear on nested comprehensions (that cost is why it is gated).
#
# `CAMBRA_REFINEMENT_ORDER=reverse` (read at runtime, debug builds only) flips
# the physical order of every refinement set. The workflow runs the suite
# both ways: set semantics makes that order meaningless by contract, but a
# consumer that lets it become observable — or a dedup keeping the
# first-inserted of two `eq`-equal refinements — compiles clean either way. Same
# argument as `ci_clippy_serde`: a configuration nothing runs is a
# configuration that rots.
ci_test() { cargo test -q ${DEEP_TYPECHECK:+--features deep-typecheck}; }
# The formal model (`formal/`): building it is what elaborates every theorem and
# evaluates every `#guard` in the Lean development, and the differential tests
# then diff the model's verdicts against the solver's. Those tests skip
# themselves when the oracle binary is absent, so without this gate nothing
# notices the model drifting from the solver — the same rot argument as
# `ci_clippy_serde`, and the drift is silent in both directions. A machine with
# no Lean toolchain skips, loudly; under CI a missing toolchain is a broken gate
# rather than a local convenience, so it fails instead.
ci_formal() {
  if ! command -v lake >/dev/null 2>&1; then
    if [[ -n "${CI:-}" ]]; then
      echo "ci_formal: no Lean toolchain (lake) under CI — this gate would be a no-op" >&2
      return 1
    fi
    echo "ci_formal: no Lean toolchain (lake) — formal model not checked" >&2
    return 0
  fi
  (cd formal && lake build) || return 1
  cargo test -q --test differential_oracle
}
ci_doc() {
  RUSTDOCFLAGS="-A warnings -D rustdoc::broken_intra_doc_links" \
    cargo doc --no-deps
}
ci_shellcheck() { find . -name '*.sh' -not -path './.git/*' -exec shellcheck -a -o all {} +; }
# Validate intra-repo doc references so they can't silently rot: Markdown
# links/anchors (doc -> doc) and `<name>.md` citations in Rust comments
# (code -> doc). Stdlib Python only; no Rust toolchain needed. Unit tests for
# the checker run first so a checker bug can't mask real breakage.
# `|| return 1` per command, not bare `set -e`: `ci_all` calls each gate on the
# left of a `||` to collect the failing gate's name, and that disables errexit
# for the whole dynamic extent — including this function. Without it a failing
# checker unit test would fall through to the check below and the function would
# report the *check's* status, defeating the very ordering this gate relies on.
# (`return`, not `exit`: this body is not a subshell, so `exit` would tear down
# the whole run instead of recording one failed gate.)
ci_doc_refs() {
  python3 .github/scripts/doc-refs/test_check_doc_refs.py || return 1
  python3 .github/scripts/doc-refs/check_doc_refs.py || return 1
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
  ci_clippy_lib || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_doc || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_test || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_formal || failed=1
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

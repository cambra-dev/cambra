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
ci_clippy() { cargo clippy -p cambra --all-targets -- -D warnings; }
# Same lint, in release. The debug checks never compile the test target in
# release, so a `#[cfg(debug_assertions)]`-gated item referenced by ungated code
# (e.g. a test calling a debug-only fn) only breaks here. `-- -D warnings` is
# scoped to our crate, not deps.
ci_clippy_release() { cargo clippy -p cambra --release --all-targets -- -D warnings; }
# The library alone, with no features unified in. Every pass above uses
# `--all-targets`, which pulls in the dev-dependencies — including the *self*
# dev-dependency that enables `test-helpers`. Cargo unifies that feature into the
# lib under test, so those passes only ever compile the library with
# `test-helpers` ON, and the feature-off configuration a consumer actually builds
# is compiled by nothing. Edition 2024 / resolver 3 keeps the feature out of a
# plain `cargo build --lib`, which is what makes the gap silent rather than loud:
# ungated library code calling a `test-helpers`-gated item passes the whole gate
# and fails `cargo build --lib`. A configuration nothing compiles is a
# configuration that rots.
ci_clippy_lib() { cargo clippy -p cambra --lib -- -D warnings; }
# `DEEP_TYPECHECK=1` turns on the opt-in per-operation typecheck (see the
# `deep-typecheck` feature). The GitHub workflow sets it so automated runs keep
# exercising that check; it stays off for a bare local `./ci.sh` because it is
# superlinear on nested comprehensions (that cost is why it is gated).
#
# `CAMBRA_REFINEMENT_ORDER=reverse` (read at runtime, debug builds only) flips
# the physical order of every refinement set. The workflow runs the suite
# both ways: set semantics makes that order meaningless by contract, but a
# consumer that lets it become observable — or a dedup keeping the
# first-inserted of two `eq`-equal refinements — compiles clean either way. It
# reaches planning too, which recovers the order a nested filter's predicate
# implies rather than reading it off the storage this reverses. Same argument as
# `ci_clippy_lib`: a configuration nothing runs is a configuration that rots.
ci_test() { cargo test -p cambra -q ${DEEP_TYPECHECK:+--features deep-typecheck}; }
# The formal model (`formal/`): building it is what elaborates every theorem,
# evaluates every `#guard`, and checks every headline result's axiom list
# (`CclFormal/Axioms.lean`) in the Lean development, and the differential tests
# then diff the model's verdicts against the solver's. Those tests skip
# themselves when the oracle binary is absent, so without this gate nothing
# notices the model drifting from the solver — the same rot argument as
# `ci_clippy_lib`, and the drift is silent in both directions. A machine with
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
  # `ci_all` runs the suite next, so the differential tests ride that run rather
  # than a second one. A bare `./ci.sh formal` still wants its own.
  #
  # `--nocapture` so each oracle's case count reaches the log. Without it a run
  # that compared nothing is indistinguishable from one that compared
  # everything: the test line reports neither.
  cargo test -q --test differential_oracle -- --nocapture
}
ci_doc() {
  RUSTDOCFLAGS="-A warnings -D rustdoc::broken_intra_doc_links" \
    cargo doc -p cambra --no-deps
}
# The web frontend: typecheck + vitest, plus a freshness check on the committed
# single-file bundle (R7 — `dist/index.html` is `include_str!`'d so `cargo build`
# needs no Node). Requires npm; skipped (not failed) when npm is absent so the
# Rust-only local path still works.
ci_web() {
  if ! command -v npm > /dev/null 2>&1; then
    echo "ci_web: npm not found; skipping web frontend checks" >&2
    return 0
  fi
  (
    # Every step is `|| exit 1` rather than relying on `set -e`: `ci_all` calls
    # this function on the left of a `||`, which disables errexit for the whole
    # dynamic extent — including this subshell. Without the explicit exits a
    # failing `npm run test` would fall through to the build below and the
    # subshell would report the *build's* status, so red tests passed the gate.
    cd cambra-inspector/web || exit 1
    npm ci || exit 1
    npm run typecheck || exit 1
    npm run test || exit 1
    # Rebuild the bundle and fail if it drifted from the committed copy.
    # Deliberately a file comparison against the pre-build copy, not
    # `git diff`: in a colocated jj repo git HEAD can sit below the working
    # copy, which turns a git-based check into a false failure — and the raw
    # diff of the single-line minified bundle is unreadable anyway.
    vendored="$(mktemp)"
    trap 'rm -f "${vendored}"' EXIT
    cp dist/index.html "${vendored}" || exit 1
    npm run build || exit 1
    if ! cmp -s "${vendored}" dist/index.html; then
      vendored_size="$(wc -c < "${vendored}")"
      built_size="$(wc -c < dist/index.html)"
      echo "ci_web FAILED: vendored dist/index.html differs from a fresh build" >&2
      echo "  sizes: vendored ${vendored_size} bytes vs built ${built_size} bytes" >&2
      echo "  re-vendor via: (cd cambra-inspector/web && npm run build), then commit dist/index.html" >&2
      exit 1
    fi
  )
}
# Golden-fixture drift gate: regenerate the frontend's snapshot fixtures into a
# temp dir through the same script the fix path uses (regen-fixtures.sh, driven
# by scripts/fixtures.manifest) and fail on any byte difference from the
# committed copies. The fix on an intended wire change is the script itself:
#   cambra-inspector/scripts/regen-fixtures.sh   # then commit the diff
# (Cross-process dump determinism — the property this gate relies on — is
# pinned corpus-wide by tests/inspector_goldens.rs under ci_test.)
ci_fixtures() {
  (
    tmp="$(mktemp -d)"
    trap 'rm -rf "${tmp}"' EXIT
    # A regen failure is a BUILD error, not fixture drift — bail before the
    # comparisons below, which read "absent from the temp dir" as a fixture
    # problem. Falling through would report the empty/partial temp dir as drift
    # and, worse, name every unreached fixture an "orphan" and advise deleting
    # it — its manifest row is fine, regen just never got there. Checked
    # explicitly (`if !`) rather than via `set -e`: `ci_all` calls this gate on
    # the left of a `||`, which suppresses errexit for this whole subshell.
    if ! cambra-inspector/scripts/regen-fixtures.sh "${tmp}"; then
      echo "ci_fixtures FAILED: fixture regeneration failed (see the error above) — a build/regen failure, NOT fixture drift" >&2
      exit 1
    fi
    fix="cambra-inspector/web/src/__fixtures__"
    drifted=0
    for f in "${tmp}"/*.snapshot.json; do
      name="$(basename "${f}")"
      # cmp + a short excerpt, not a full `git diff`: a drifted snapshot diff
      # is thousands of lines and buries which fixture failed.
      if ! cmp -s "${fix}/${name}" "${f}"; then
        committed_size="$(wc -c < "${fix}/${name}")"
        regen_size="$(wc -c < "${f}")"
        echo "ci_fixtures FAILED: fixture drift: ${name} (committed ${committed_size} bytes vs regenerated ${regen_size} bytes)" >&2
        diff -u "${fix}/${name}" "${f}" | head -n 12 >&2 || true
        echo "  re-bless via: cambra-inspector/scripts/regen-fixtures.sh, then commit the diff" >&2
        echo "  (if web/src/ changed too: cd cambra-inspector/web && npm run build, then commit dist/index.html — ci_web compares it)" >&2
        drifted=1
      fi
    done
    # Orphan check: a committed fixture with no manifest row would otherwise be
    # compared against nothing and rot silently.
    for committed in "${fix}"/*.snapshot.json; do
      name="$(basename "${committed}")"
      if [[ ! -f "${tmp}/${name}" ]]; then
        echo "ci_fixtures FAILED: orphan fixture: ${name} is committed but has no row in cambra-inspector/scripts/fixtures.manifest (add the row or delete the fixture)" >&2
        drifted=1
      fi
    done
    exit "${drifted}"
  )
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

# Gate the interpreter's no-back-channel invariant: operators exchange tiles
# through `get`, never through shared mutable state (`src/interpreter/CLAUDE.md`).
# Same ordering rule as `ci_doc_refs`: checker tests first, and `|| return 1` per
# command because `ci_all` disables errexit for this function's extent.
ci_shared_state() {
  python3 .github/scripts/shared-state/test_check_shared_state.py || return 1
  python3 .github/scripts/shared-state/check_shared_state.py || return 1
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
  { cargo clippy -p cambra -- -D warnings; } || failed=1
  # shellcheck disable=SC2310
  ci_test || failed=1
  exit "${failed}"
}

ci_all() {
  # Names of failed gates, so the last lines of a long run say WHAT failed.
  local failed=""
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_shellcheck || failed="${failed} shellcheck"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_doc_refs || failed="${failed} doc_refs"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_shared_state || failed="${failed} shared_state"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_fmt || failed="${failed} fmt"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_clippy || failed="${failed} clippy"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_clippy_release || failed="${failed} clippy_release"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_clippy_lib || failed="${failed} clippy_lib"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_doc || failed="${failed} doc"
  # Before `ci_test`, so the oracle binary exists by the time the suite runs:
  # the differential tests skip themselves without it, and a skip in the middle
  # of the gate is the failure mode this step exists to remove.
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_formal || failed="${failed} formal"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_test || failed="${failed} test"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_fixtures || failed="${failed} fixtures"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_web || failed="${failed} web"
  if [[ -n "${failed}" ]]; then
    echo "ci.sh FAILED:${failed}" >&2
    exit 1
  fi
  echo "ci.sh: all gates passed"
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

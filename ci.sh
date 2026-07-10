#!/usr/bin/env bash
# Use `set -x` so it's easy to pull out the failing commands.
set -euxo pipefail

ci_fmt() {
  if ((fix)); then cargo fmt; fi
  cargo fmt --check
}
# --all-targets lints test code too and warms the cache for cargo test
ci_clippy() { cargo clippy --all-targets -- -D warnings; }
# Same lint, in release. The debug checks never compile the test target in
# release, so a `#[cfg(debug_assertions)]`-gated item referenced by ungated code
# (e.g. a test calling a debug-only fn) only breaks here. `-- -D warnings` is
# scoped to our crate, not deps.
ci_clippy_release() { cargo clippy --release --all-targets -- -D warnings; }
ci_test() { cargo test -q; }
ci_doc() {
  RUSTDOCFLAGS="-A warnings -D rustdoc::broken_intra_doc_links" \
    cargo doc --no-deps
}
# The `cambra-inspector` workspace member: its crate lints + tests. Kept separate
# from the core `cambra` checks above (which stay serde-free and fast) and run
# explicitly with `-p` because the root `cargo` invocations only build the root
# package. Building the inspector pulls `cambra` with the `serde` feature, so
# this also exercises the serde-gated wire types in the core.
ci_inspector() {
  cargo clippy -p cambra-inspector --all-targets -- -D warnings
  cargo test -p cambra-inspector -q
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
    cd cambra-inspector/web || exit 1
    npm ci
    npm run typecheck
    npm run test
    # Rebuild the bundle and fail if it drifted from the committed copy.
    # Deliberately a file comparison against the pre-build copy, not
    # `git diff`: in a colocated jj repo git HEAD can sit below the working
    # copy, which turns a git-based check into a false failure — and the raw
    # diff of the single-line minified bundle is unreadable anyway.
    vendored="$(mktemp)"
    trap 'rm -f "${vendored}"' EXIT
    cp dist/index.html "${vendored}"
    npm run build
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
# pinned corpus-wide by cambra-inspector/tests/goldens.rs under ci_inspector.)
ci_fixtures() {
  (
    tmp="$(mktemp -d)"
    trap 'rm -rf "${tmp}"' EXIT
    cambra-inspector/scripts/regen-fixtures.sh "${tmp}"
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
        drifted=1
      fi
    done
    exit "${drifted}"
  )
}
ci_shellcheck() { find . -name '*.sh' -not -path './.git/*' -exec shellcheck -a -o all {} +; }

ci_all() {
  # Names of failed gates, so the last lines of a long run say WHAT failed.
  local failed=""
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_shellcheck || failed="${failed} shellcheck"
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
  ci_doc || failed="${failed} doc"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_test || failed="${failed} test"
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_inspector || failed="${failed} inspector"
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

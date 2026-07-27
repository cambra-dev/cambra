#!/usr/bin/env bash
# Regenerate the frontend's golden `/api/snapshot` fixtures from the real
# backend. Each fixture is the `--dump-snapshot` output for an example program —
# pretty-printed by the binary itself (serde_json, pinned by Cargo.lock), so no
# external formatter owns the committed bytes: piping through e.g. `python3 -m
# json.tool` would tie the corpus to the local Python version and to colorizing
# env vars (FORCE_COLOR), either of which silently rewrites every fixture.
# Run after ANY backend change to the snapshot schema; commit the result.
# `store.test.ts` keys its assertions on node labels/types (not raw NodeIds),
# so ordinary id churn does not require touching the tests — but a shape change
# will, by design.
#
# The corpus (fixture -> example mapping) lives in fixtures.manifest next to
# this script — shared with the cargo golden tests (tests/goldens.rs) so the
# regen path and the tests can never disagree about the corpus.
#
# Usage: cambra-inspector/scripts/regen-fixtures.sh [output-dir]
#
# With no argument, writes the committed fixture directory (the fix path). The
# ci.sh drift gate passes a temp directory (must be an absolute path — the
# script cds to the repo root) and diffs it against the committed copies, so the
# gate and the fix path can never disagree about how a fixture is produced.
set -euo pipefail

# Fail fast with an actionable message rather than a mid-loop "command not
# found" after some fixtures were already rewritten. cargo is the script's
# only external dependency (the binary pretty-prints its own output).
command -v cargo > /dev/null 2>&1 || {
  echo "regen-fixtures.sh: cargo not found on PATH — install the Rust toolchain (rustup) first" >&2
  exit 1
}

cd "$(dirname "$0")/../.." || exit 1 # -> cambra/ repo root
MANIFEST="cambra-inspector/scripts/fixtures.manifest"
FIX="${1:-cambra-inspector/web/src/__fixtures__}"
mkdir -p "${FIX}"

while read -r name example; do
  # Skip blank lines and comments.
  if [[ -z ${name} || ${name} == \#* ]]; then continue; fi
  prog="cambra-inspector/examples/${example}.chl"
  out="${FIX}/${name}.snapshot.json"
  echo "regen ${out}  <-  ${prog}"
  # `< /dev/null`: the command must not inherit the loop's stdin, or it eats
  # the rest of the manifest and only the first fixture regenerates.
  cargo run -q -p cambra-inspector -- "${prog}" --dump-snapshot < /dev/null > "${out}"
done < "${MANIFEST}"

echo "done. Review the diff: git diff ${FIX}"
echo "If web/src/ changed too, rebuild and commit the bundle:"
echo "  (cd cambra-inspector/web && npm run build)   # ci_web compares dist/index.html"

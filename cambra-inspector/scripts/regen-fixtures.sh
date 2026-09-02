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
# The corpus (fixture -> program mapping) lives in fixtures.manifest next to
# this script — shared with the cargo golden tests (tests/inspector_goldens.rs)
# so the regen path and the tests can never disagree about the corpus. A row is two
# words and nothing else, so the two parsers have nothing to disagree about.
#
# Usage: cambra-inspector/scripts/regen-fixtures.sh [output-dir]
#
# With no argument, writes the committed fixture directory (the fix path). The
# ci.sh drift gate passes a temp directory (must be an absolute path — the
# script cds to the repo root) and diffs it against the committed copies, so the
# gate and the fix path can never disagree about how a fixture is produced.
set -euo pipefail

cd "$(dirname "$0")/../.." || exit 1 # -> cambra/ repo root
MANIFEST="cambra-inspector/scripts/fixtures.manifest"
FIX="${1:-cambra-inspector/web/src/__fixtures__}"
mkdir -p "${FIX}"

while read -r name example; do
  # Skip blank lines and comments.
  if [[ -z ${name} || ${name} == \#* ]]; then continue; fi
  if [[ -z ${example} ]]; then
    echo "regen-fixtures.sh: manifest row '${name}' names no example program" >&2
    exit 1
  fi
  prog="tests/programs/${example}/program.cambra"
  out="${FIX}/${name}.snapshot.json"
  echo "regen ${out}  <-  ${prog}"
  # `< /dev/null`: the command must not inherit the loop's stdin, or it eats
  # the rest of the manifest and only the first fixture regenerates.
  #
  # Written to a temp file and moved into place only on success. A redirect
  # straight to "${out}" would create/truncate it *before* the dump runs, so a
  # program that fails to build would leave a 0-byte fixture behind — which the
  # caller cannot distinguish from a real one that legitimately shrank. Failing
  # atomically means a failed regen leaves the output directory untouched.
  partial="${out}.partial"
  if cargo run -q -- "${prog}" --dump-snapshot < /dev/null > "${partial}"; then
    mv "${partial}" "${out}"
  else
    rm -f "${partial}"
    echo "regen-fixtures.sh: FAILED to dump ${prog}" >&2
    exit 1
  fi
done < "${MANIFEST}"

echo "done. Review the diff: git diff ${FIX}"

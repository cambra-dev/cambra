#!/usr/bin/env bash
# Pass/fail test of the workspace lifecycle the daily run depends on.
#
#   test-workspace.sh
#
# Creates the scout workspace exactly as Step 1 does, asserts its shape, removes it, and asserts
# nothing is left behind. Refuses to run while a simplify-* workspace exists, so it never
# disturbs a real run. Exits non-zero on the first failed assertion, after cleaning up.
#
# Other sessions write to the same jj repo concurrently, so "the default working copy was not
# touched" is checked through the op log rather than by comparing before/after state: every
# operation this test issued must either carry --ignore-working-copy or target the scout
# directory.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
WSH="${HERE}/workspace.sh"
SRCS="" REPO=""
paths="$("${WSH}" paths)"
eval "${paths}"
DIR="${SRCS}/cambra-simplify-scout"
JJ=(jj -R "${REPO}" --ignore-working-copy --config ui.paginate=never)

failures=0
pass() { echo "PASS  $*"; }
fail() { echo "FAIL  $*"; failures=$((failures + 1)); }
check() { local what="$1"; shift; if "$@"; then pass "${what}"; else fail "${what}"; fi; }

existing="$("${WSH}" list)"
if [[ -n "${existing}" ]]; then
  echo "a simplify-* workspace exists; finish or clean up that run first:" >&2
  echo "${existing}" >&2
  exit 2
fi

cleanup() {
  if [[ -e "${DIR}" ]]; then "${WSH}" remove scout > /dev/null 2>&1 || true; fi
}
trap cleanup EXIT

start_op="$("${JJ[@]}" op log --limit 1 --no-graph -T 'id')"

# --- Create, as Step 1 does. ----------------------------------------------------------------
"${WSH}" fetch > /dev/null
base="$("${JJ[@]}" log -r 'main@origin' --no-graph -T 'commit_id')"
got_dir="$("${WSH}" add scout 2> /dev/null)"

check "add prints the workspace dir" test "${got_dir}" = "${DIR}"
check "workspace simplify-scout is registered" \
  bash -c "\"\$@\" workspace list -T 'name ++ \"\n\"' | grep -qx simplify-scout" _ "${JJ[@]}"

parents="$("${JJ[@]}" log -r 'parents(simplify-scout@)' --no-graph -T 'commit_id ++ "\n"')"
check "scout @ has exactly one parent, main@origin (${base:0:12})" test "${parents}" = "${base}"
empty="$("${JJ[@]}" log -r 'simplify-scout@' --no-graph -T 'empty')"
check "scout @ is an empty commit" test "${empty}" = "true"
description="$("${JJ[@]}" log -r 'simplify-scout@' --no-graph -T 'description')"
check "scout @ has no description" test -z "${description}"
drift="$(jj -R "${DIR}" --config ui.paginate=never diff --from 'main@origin' --to @ --summary)"
check "scout checkout matches main@origin" test -z "${drift}"
bookmarked="$("${JJ[@]}" log -r 'simplify-scout@ & bookmarks()' --no-graph -T 'commit_id')"
check "no bookmark points into the scout workspace" test -z "${bookmarked}"
target="$("${WSH}" target scout)"
check "scout has its own cargo target dir" test -d "${target}"

scout_commit="$("${JJ[@]}" log -r 'simplify-scout@' --no-graph -T 'commit_id')"

# --- Remove, as Step 9 does. ----------------------------------------------------------------
"${WSH}" remove scout > /dev/null 2>&1
remaining="$("${WSH}" list)"
check "no simplify-* workspace remains" test -z "${remaining}"
check "scout directory is deleted" test ! -e "${DIR}"
hidden="$("${JJ[@]}" log -r "${scout_commit}" --no-graph -T 'hidden')"
check "the scout commit is no longer visible" test "${hidden}" = "true"

# --- The default working copy was never snapshotted by this test. ---------------------------
# Ours: anything naming a simplify workspace, or issued with `-R <repo>` (other sessions run jj
# from inside a workspace, not with -R). An op of ours is clean if it skipped the working copy or
# ran inside the scout directory. The `workspace add` op records no args (the command exits with
# the error workspace.sh tolerates), so only `new`, `forget` and `abandon` are checkable here.
ours="$("${JJ[@]}" op log --no-graph -T 'id ++ "\t" ++ attributes ++ "\n"' \
  | awk -F'\t' -v stop="${start_op}" '$1 == stop { exit } { print $2 }' \
  | grep -E -- "simplify|-R ${REPO} " || true)"
offenders="$(grep -vE -- "--ignore-working-copy|-R ${DIR}( |$)" <<< "${ours}" || true)"
n_ours="$(grep -c . <<< "${ours}" || true)"
check "this test issued ${n_ours} jj op(s), all clear of the default working copy" \
  test -z "${offenders}"
[[ -n "${offenders}" ]] && while read -r l; do echo "      ${l}"; done <<< "${offenders}"
echo
if (( failures )); then echo "${failures} check(s) failed"; exit 1; fi
echo "all checks passed"

#!/usr/bin/env bash
# Pass/fail test of review-test.sh in a scratch jj repo: `clean` abandons the temporary commits
# of one review and nothing else.
#
#   test-review-test.sh
#
# The scratch repo holds base ← change, plus three commits `clean` must keep: an ordinary child
# of base, an ordinary child of change, and another review's temporary commit on base.
# Each check's body is a string `check` evals, so the variables it reads look unused.
# shellcheck disable=SC2016,SC2034,SC2317,SC2329
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "${tmp}"' EXIT
repo="${tmp}/repo"
jj=(jj -R "${repo}" --config user.name=t --config user.email=t@t --config ui.paginate=never)
script=("${HERE}/review-test.sh" -R "${repo}")
failures=0

check() {
  if eval "$2"; then echo "PASS  $1"; else echo "FAIL  $1"; failures=$((failures + 1)); fi
}
commit_id() { "${jj[@]}" log -r "$1" --no-graph -T commit_id 2>/dev/null; }
# An abandoned commit still resolves by its id, so visibility is read from `hidden`.
exists() {
  local hidden
  hidden="$("${jj[@]}" log -r "$1" --no-graph -T hidden 2>/dev/null)"
  [[ "${hidden}" == "false" ]]
}

jj git init "${repo}" >/dev/null 2>&1
"${jj[@]}" describe -m base 2>/dev/null
# A `main` bookmark, because user configs commonly name it in revset aliases.
"${jj[@]}" bookmark create main -r @ 2>/dev/null
base="$(commit_id @)"
"${jj[@]}" new -m change 2>/dev/null
change="$(commit_id @)"
"${jj[@]}" new "${base}" -m "unrelated child of base" 2>/dev/null
other_base="$(commit_id @)"
"${jj[@]}" new "${change}" -m "unrelated child of change" 2>/dev/null
other_change="$(commit_id @)"
"${jj[@]}" new "${base}" -m "review-test of zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz" 2>/dev/null
other_review="$(commit_id @)"
"${jj[@]}" edit "${change}" 2>/dev/null

"${script[@]}" new "${change}" "${change}" 2>/dev/null
on_change="$(commit_id @)"
"${script[@]}" new "${change}" "${base}" 2>/dev/null
on_base="$(commit_id @)"
check "new puts the commit on the given revision" \
  '[[ "$(commit_id "${on_base}-")" == "${base}" && "$(commit_id "${on_change}-")" == "${change}" ]]'

"${script[@]}" clean "${change}" "${change}" 2>/dev/null
check "clean returns @ to the original commit" '[[ "$(commit_id @)" == "${change}" ]]'
check "clean abandons both temporary commits" \
  '! exists "${on_change}" && ! exists "${on_base}"'
check "clean keeps ordinary children of the same parents" \
  'exists "${other_base}" && exists "${other_change}"'
check "clean keeps another review's temporary commit" 'exists "${other_review}"'
check "clean leaves the change itself" 'exists "${change}"'

"${script[@]}" clean "${change}" 2>/dev/null
check "clean with nothing to abandon succeeds and keeps @" '[[ "$(commit_id @)" == "${change}" ]]'

exit $((failures > 0))

#!/usr/bin/env bash
# Make and remove the temporary commits a review tries a test in ("Trying a test in a temporary
# commit" in ../SKILL.md).
#
#   review-test.sh [-R <repo>] new <change> <rev>       # jj new <rev>, described for <change>
#   review-test.sh [-R <repo>] clean <change> [<orig>]  # jj edit <orig>, then abandon them
#
# `<change>` is the tip of the change under review. Every commit `new` makes is described
# `review-test of <change id>`, with that tip's full change id, so `clean` abandons exactly the
# temporary commits of reviews of that change and leaves every other child of the same parents.
set -euo pipefail

jj=(jj --config ui.paginate=never)
if [[ "${1:-}" == "-R" ]]; then
  jj+=(-R "${2:?repo}")
  shift 2
fi
cmd="${1:?new or clean}"
change="${2:?change under review}"

id="$("${jj[@]}" log -r "${change}" --no-graph -T change_id)"
[[ "${id}" =~ ^[a-z]+$ ]] || { echo "review-test.sh: ${change} is not one commit" >&2; exit 2; }
prefix="review-test of ${id}"

case "${cmd}" in
  new)
    "${jj[@]}" new "${3:?revision to put the test on}" -m "${prefix}"
    ;;
  clean)
    if [[ -n "${3:-}" ]]; then
      "${jj[@]}" edit "$3"
    fi
    temps="mutable() & description(substring:\"${prefix}\")"
    found="$("${jj[@]}" log -r "${temps}" --no-graph -T 'commit_id ++ "\n"')"
    if [[ -n "${found}" ]]; then
      "${jj[@]}" abandon "${temps}"
    fi
    ;;
  *)
    echo "review-test.sh: unknown command ${cmd}" >&2
    exit 2
    ;;
esac

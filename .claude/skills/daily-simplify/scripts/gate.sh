#!/usr/bin/env bash
# Run a gate in a simplify workspace and keep its log.
#
#   gate.sh <workspace-dir> <log-prefix> fast|full
#
# `fast` runs `./ci.sh fast` into <log-prefix>-fast.log. `full` runs `./ci.sh --fix`, then
# `doc-adoption.py` on the workspace's `@`, into <log-prefix>-full.log. Both run through
# in-workspace.sh. Prints the log's last lines and exits with the gate's status.
#
# A secondary jj workspace has no `.git`, so `GIT_DIR` points the git-based gates at the default
# workspace's. `ci.sh` then takes its `doc_adoption` tip from git's `HEAD`, which is the default
# workspace's, and checks the wrong range; `full` checks this workspace's `@` by hand.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ws="${1:?workspace dir}"
prefix="${2:?log prefix}"
step="${3:?fast or full}"

REPO=""
paths="$("${HERE}/workspace.sh" paths)"
eval "${paths}"
export GIT_DIR="${REPO}/.git"
log="${prefix}-${step}.log"
mkdir -p "$(dirname "${log}")"

status=0
case "${step}" in
  fast)
    "${HERE}/in-workspace.sh" "${ws}" 1800 ./ci.sh fast > "${log}" 2>&1 || status=$?
    ;;
  full)
    "${HERE}/in-workspace.sh" "${ws}" 3600 ./ci.sh --fix > "${log}" 2>&1 || status=$?
    if (( status == 0 )); then
      tip="$(jj -R "${ws}" --config ui.paginate=never log -r @ --no-graph -T commit_id)"
      "${HERE}/in-workspace.sh" "${ws}" 600 python3 .github/scripts/doc-adoption.py origin/main \
        "${tip}" >> "${log}" 2>&1 || status=$?
    fi
    ;;
  *)
    echo "gate.sh: unknown step '${step}' (want fast or full)" >&2
    exit 2
    ;;
esac
tail -n 15 "${log}"
echo "gate ${step}: exit ${status}; log ${log}"
exit "${status}"

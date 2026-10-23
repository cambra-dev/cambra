#!/usr/bin/env bash
# Run the local gate, `./ci.sh fast`, in a simplify workspace and keep its log.
#
#   gate.sh <workspace-dir> <log-prefix>
#
# Runs through in-workspace.sh into <log-prefix>.log, prints the log's last lines and exits with the
# gate's status. The full gate runs on GitHub against each draft PR; settle-drafts.sh reads its
# result on the next run.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ws="${1:?workspace dir}"
prefix="${2:?log prefix}"
log="${prefix}.log"
mkdir -p "$(dirname "${log}")"

status=0
"${HERE}/in-workspace.sh" "${ws}" 1800 ./ci.sh fast > "${log}" 2>&1 || status=$?
tail -n 15 "${log}"
echo "gate: exit ${status}; log ${log}"
exit "${status}"

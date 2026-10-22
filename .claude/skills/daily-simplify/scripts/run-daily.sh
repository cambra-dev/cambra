#!/usr/bin/env bash
# Run the daily simplification skill headless; the job service's entry point.
#
#   run-daily.sh [triage-only]
#
# Runs `claude -p "/daily-simplify"` from the workspace this script is in, with permission checks
# skipped, as the vault's other server jobs run. The transcript goes to <run>/session.jsonl. A scheduler that stops a run
# still in progress records it with supersede.sh before starting this one.
#
# Environment: `SIMPLIFY_MODEL` (default opus), plus what workspace.sh and preflight.sh read.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
WS_ROOT="$(cd "${HERE}/../../../.." && pwd)"
SRCS="" CACHE="" LOGDIR="" TODAY=""
paths="$("${HERE}/workspace.sh" paths)"
eval "${paths}"
RUN="${CACHE}/runs/${TODAY}"
mkdir -p "${RUN}" "${LOGDIR}"

cd "${WS_ROOT}"
claude -p "/daily-simplify${1:+ $1}" --model "${SIMPLIFY_MODEL:-opus}" \
  --dangerously-skip-permissions --add-dir "${SRCS}" "${LOGDIR}" \
  --output-format stream-json --verbose \
  > "${RUN}/session.jsonl" 2> "${RUN}/session.stderr"

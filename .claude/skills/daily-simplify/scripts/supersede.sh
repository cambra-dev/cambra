#!/usr/bin/env bash
# Record that a run still in progress is being stopped so today's run can start.
#
#   supersede.sh <start-time of the run being stopped>
#
# A scheduler calls this before it stops a run still in progress. The note goes to the stopped
# run's own day log and to today's run directory, from which preflight copies it into today's log.
# The start time is anything `date -d` parses, such as systemd's `ExecMainStartTimestamp`.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
started="${1:?start time of the run being stopped}"
CACHE="" LOGDIR="" TODAY=""
paths="$("${HERE}/workspace.sh" paths)"
eval "${paths}"

started_date="$(TZ=America/Denver date -d "${started}" +%F)"
now="$(TZ=America/Denver date -Is)"
note="The run started ${started} was still in progress at ${now} and was stopped: the run of \
${TODAY} superseded it. That run's preflight removes the old run's workspaces."
mkdir -p "${LOGDIR}" "${CACHE}/runs/${TODAY}"
printf '\n## Superseded\n\n%s\n' "${note}" >> "${LOGDIR}/${started_date}.md"
printf '%s\n' "${note}" > "${CACHE}/runs/${TODAY}/superseded.md"

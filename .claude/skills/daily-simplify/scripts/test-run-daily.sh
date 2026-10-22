#!/usr/bin/env bash
# Pass/fail test of the scheduler's two entry points: supersede.sh's notes, and run-daily.sh's
# headless session.
#
#   test-run-daily.sh
#
# Runs both scripts against a scratch <srcs> and vault, with a stub `claude` first on PATH that
# records its arguments. Touches no real workspace, cache or log.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "${TMP}"' EXIT

failures=0
pass() { echo "PASS  $*"; }
fail() { echo "FAIL  $*"; failures=$((failures + 1)); }
check() { local what="$1"; shift; if "$@"; then pass "${what}"; else fail "${what}"; fi; }

mkdir -p "${TMP}/bin" "${TMP}/srcs/vault/_system"
touch "${TMP}/srcs/vault/_system/AI-CONTEXT.md"
cat > "${TMP}/bin/claude" << 'STUB'
#!/usr/bin/env bash
printf '%s\n' "$@" > "${STUB_DIR}/claude.args"
STUB
chmod +x "${TMP}/bin/claude"

export PATH="${TMP}/bin:${PATH}" CAMBRA_SRCS="${TMP}/srcs"
export STUB_DIR="${TMP}"
logs="${TMP}/srcs/vault/automation/daily-simplify/outputs"
today="$(TZ=America/Denver date -I)"
run="${TMP}/srcs/cambra_build_caches/simplify-cache/runs/${today}"
# --- supersede.sh, stopping yesterday's run. --------------------------------------------------
"${HERE}/supersede.sh" "Mon 2026-10-19 02:00:03 MDT"
check "the vault defaults to <srcs>/vault" test -d "${logs}"
check "the old run's day log records the supersede" grep -q '^## Superseded' "${logs}/2026-10-19.md"
check "today's run directory records it for preflight" test -s "${run}/superseded.md"

# --- run-daily.sh's session. ------------------------------------------------------------------
"${HERE}/run-daily.sh" triage-only
args="$(cat "${TMP}/claude.args")"
has() { grep -qxF -- "$1" <<< "${args}"; }
check "the prompt is /daily-simplify triage-only" has "/daily-simplify triage-only"
check "permission checks are skipped" has "--dangerously-skip-permissions"
check "<srcs> is an added directory" has "${TMP}/srcs"
check "the vault log directory is an added directory" has "${logs}"
check "the transcript lands in the run directory" test -e "${run}/session.jsonl"

echo
if (( failures )); then echo "${failures} check(s) failed"; exit 1; fi
echo "all checks passed"

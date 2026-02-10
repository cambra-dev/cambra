#!/usr/bin/env bash
# Local testing script for the stale review reminder system.
# Usage: .github/scripts/pr-reminders/test-pr-review-reminders.sh [usermap|find|post|check|smoke]
#
# All env vars have sensible defaults. The script will prompt for
# SLACK_BOT_TOKEN if not set and the command needs it.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Check dependencies
missing=()
for cmd in gh python3 git; do
  command -v "${cmd}" &>/dev/null || missing+=("${cmd}")
done
if ((${#missing[@]} > 0)); then
  echo "Error: missing required dependencies: ${missing[*]}" >&2
  exit 1
fi

# Defaults
# shellcheck disable=SC2312
# Masking is fine, we want the default, not the exit code.
: "${GH_TOKEN:=$(gh auth token)}"
# shellcheck disable=SC2312
# Masking is fine, we want the default, not the exit code.
: "${GH_REPOSITORY:=$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
# Defaults to spam-testing instead of "prod" `#code` channel
: "${SLACK_CHANNEL:=#spam-testing}"
export GH_TOKEN GH_REPOSITORY SLACK_CHANNEL

cmd="${1:-help}"
shift || true

# Prompt for Slack token if needed and not already set
needs_slack() {
  if [[ -z "${SLACK_BOT_TOKEN:-}" ]]; then
    read -rsp "Enter SLACK_BOT_TOKEN (xoxb-...): " SLACK_BOT_TOKEN
    echo
    if [[ -z "${SLACK_BOT_TOKEN}" ]]; then
      echo "Error: SLACK_BOT_TOKEN is required for this command." >&2
      exit 1
    fi
    export SLACK_BOT_TOKEN
  fi
}

case "${cmd}" in usermap | post | smoke) needs_slack ;; *) ;; esac
# check --to-slack also needs Slack credentials
if [[ "${cmd}" == "check" ]] && [[ " $* " == *" --to-slack "* ]]; then
  needs_slack
fi

# Ensure usermap.json exists (post needs it for reviewer lookups)
test -f usermap.json || echo '{}' >usermap.json

case "${cmd}" in
usermap)
  echo "==> Building GitHub-to-Slack user map..."
  python3 "${SCRIPT_DIR}/build_slack_usermap.py"
  echo ""
  echo "==> Result:"
  cat usermap.json
  ;;

find)
  echo "==> Finding stale PRs (pending review >24h)..."
  python3 "${SCRIPT_DIR}/find_stale_prs.py"
  ;;

post)
  echo "==> Finding stale PRs and posting to Slack..."
  python3 "${SCRIPT_DIR}/find_stale_prs.py" | python3 "${SCRIPT_DIR}/post_slack_reminders.py"
  ;;

check)
  echo "==> Running staleness logic tests..."
  python3 "${SCRIPT_DIR}/test_pr_review_reminders.py" "$@"
  ;;

smoke)
  "$0" usermap
  echo ""
  "$0" post
  ;;

help | *)
  echo "Usage: ${0} [usermap|find|post|check|smoke]"
  echo ""
  echo "  usermap           Build the GitHub-to-Slack user map (writes usermap.json)"
  echo "  find              Find stale PRs and print JSONL to stdout (no Slack needed)"
  echo "  post              Find stale PRs and post reminders to Slack"
  echo "  check             Run staleness logic tests against fixture data"
  echo "  check --to-slack  ...and post results to Slack"
  echo "  smoke               Run with live data: usermap, staleness, then post"
  echo ""
  echo "Required env vars:"
  echo "  GH_REPOSITORY    e.g. your-org/Cambra"
  echo "  SLACK_BOT_TOKEN  xoxb-..."
  echo "  SLACK_CHANNEL    e.g. #code"
  ;;
esac

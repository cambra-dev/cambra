#!/bin/bash
# Fetch PR review comments for use by the gh-pr-respond skill.
#
# Usage:
#   gh_pr_comments.sh <pr_number> [--mode active|pending|all] [--org ORG] [--repo REPO] [--author AUTHOR] [-v|--verbose]
#
# Modes:
#   active   (default) — unresolved review threads, via GraphQL
#   pending             — pending (draft) review comments for AUTHOR, via REST
#   all                 — both active and pending
#
# Defaults: org=cambra-dev, repo=cambra, author=groundlar

set -euo pipefail

DEFAULT_ORG="cambra-dev"
DEFAULT_REPO="cambra"
DEFAULT_AUTHOR="groundlar"
DEFAULT_MODE="active"

usage() {
  echo "Usage: $(basename "$0") <pr_number> [--mode active|pending|all] [--org ORG] [--repo REPO] [--author AUTHOR] [-v|--verbose]"
  exit 1
}

# --- Argument Parsing ---
PR_NUM=""
MODE="${DEFAULT_MODE}"
ORG="${DEFAULT_ORG}"
REPO="${DEFAULT_REPO}"
AUTHOR="${DEFAULT_AUTHOR}"
VERBOSE=false

while [[ $# -gt 0 ]]; do
  case "$1" in
  --mode)
    MODE="$2"
    shift 2
    ;;
  --org)
    ORG="$2"
    shift 2
    ;;
  --repo)
    REPO="$2"
    shift 2
    ;;
  --author)
    AUTHOR="$2"
    shift 2
    ;;
  -v | --verbose)
    VERBOSE=true
    shift
    ;;
  -h | --help) usage ;;
  *)
    if [[ -z "${PR_NUM}" ]]; then
      PR_NUM="$1"
    else
      echo "Unexpected argument: $1" >&2
      usage
    fi
    shift
    ;;
  esac
done

if [[ -z "${PR_NUM}" ]]; then
  usage
fi

if [[ ! "${PR_NUM}" =~ ^[0-9]+$ ]]; then
  echo "Error: PR number must be a positive integer, got: ${PR_NUM}" >&2
  usage
fi

if [[ "${AUTHOR}" =~ ^@?me$ ]]; then
  AUTHOR=$(gh api user --jq '.login')
fi

# --- Active (unresolved) threads via GraphQL ---
fetch_active() {
  echo "--> Fetching active (unresolved) threads for ${ORG}/${REPO} #${PR_NUM}..." >&2

  # shellcheck disable=SC2016 # These are literal GraphQL/jq variables, shell expansion would break them
  local QUERY='
query($owner: String!, $repo: String!, $pr: Int!) {
  repository(owner: $owner, name: $repo) {
    pullRequest(number: $pr) {
      reviewThreads(first: 100) {
        nodes {
          isResolved
          isOutdated
          path
          line
          originalLine
          startLine
          originalStartLine
          comments(first: 50) {
            nodes {
              author { login }
              body
              createdAt
            }
          }
        }
      }
    }
  }
}
'

  # shellcheck disable=SC2016 # These are literal GraphQL/jq variables, shell expansion would break them
  local JQ_FILTER='
    .data.repository.pullRequest.reviewThreads.nodes |
    map(select(.isResolved == false)) |
    group_by(.path)[] |
    "File: " + (.[0].path // "Global") + "\n" +
    (sort_by(.line // .originalLine // 0) | map(
      "  Line " + (if .startLine and .startLine != .line then (.startLine | tostring) + "-" else "" end) +
      ((.line // .originalLine // "?") | tostring) + ":\n" +
      (.comments.nodes | map("    - @" + (.author.login // "unknown") + ": " + .body) | join("\n"))
    ) | join("\n\n")) + "\n"
  '

  gh api graphql -F owner="${ORG}" -F repo="${REPO}" -F pr="${PR_NUM}" -f query="${QUERY}" |
    jq -r "${JQ_FILTER}"
}

# --- Pending (draft) comments via REST ---
fetch_pending() {
  echo "--> Fetching pending comments for ${AUTHOR} on ${ORG}/${REPO} #${PR_NUM}..." >&2

  local REVIEWS_JSON
  REVIEWS_JSON=$(gh api "repos/${ORG}/${REPO}/pulls/${PR_NUM}/reviews")

  local REVIEW_ID
  REVIEW_ID=$(echo "${REVIEWS_JSON}" |
    jq -r --arg author "${AUTHOR}" \
      '.[] | select(.state == "PENDING" and .user.login == $author) | .id' |
    head -n 1)

  if [[ -z "${REVIEW_ID}" || "${REVIEW_ID}" == "null" ]]; then
    echo "No pending reviews found for ${AUTHOR}."
    return 0
  fi

  local COMMENTS_JSON
  COMMENTS_JSON=$(gh api "repos/${ORG}/${REPO}/pulls/${PR_NUM}/reviews/${REVIEW_ID}/comments")

  # get_line: resolve line number from .line or fall back to walking the diff hunk
  # shellcheck disable=SC2016 # These are literal jq variables/backticks, shell expansion would break them
  local JQ_FILTER='
    def get_line:
      if .line != null then .line
      elif .position != null then
        (.diff_hunk | split("\n")) as $lines |
        ($lines[0] | capture("\\+(?<s>[0-9]+)") | .s | tonumber) as $start |
        ($lines[1:(.position + 1)] | map(select(startswith("-") | not)) | length) as $non_removed |
        ($start + $non_removed - 1)
      else "???" end;

    .[] |
    (get_line | tostring) as $line_num |
    if $is_verbose then
      "\n* \(.path):\($line_num)  [line=\(.line // "null"), orig=\(.original_line // "null"), pos=\(.position // "null")]\n" +
      "```\n" +
      ((.diff_hunk | split("\n") | .[-5:] | join("\n"))) +
      "\n```\n" +
      "Comment: \(.body)\n" +
      "---"
    else
      "* \(.path):\($line_num) \n  > \(.body)"
    end
  '

  # VERBOSE must be exactly 'true' or 'false' — valid JSON booleans required by --argjson
  echo "${COMMENTS_JSON}" | jq -r --argjson is_verbose "${VERBOSE}" "${JQ_FILTER}"
}

# --- Dispatch ---
case "${MODE}" in
active)
  fetch_active
  ;;
pending)
  fetch_pending
  ;;
all)
  echo "=== Active Threads ===" >&2
  fetch_active
  echo "=== Pending Comments ===" >&2
  fetch_pending
  ;;
*)
  echo "Unknown mode: ${MODE} (expected active, pending, or all)" >&2
  usage
  ;;
esac

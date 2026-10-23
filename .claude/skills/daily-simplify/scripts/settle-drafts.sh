#!/usr/bin/env bash
# Settle the run's draft PRs by their GitHub CI result: close the failed, mark the passed ready.
#
#   settle-drafts.sh [--dry-run]
#
# The run gates locally with `./ci.sh fast`, and GitHub CI runs the full gate on each draft. The
# next run's preflight reads that result here, for each draft on a `simplify-agent/` branch whose
# checks have all finished:
#
# - at least one failed: the PR is closed with a comment starting `CLOSE_PREFIX`; history.py reads
#   that prefix to tell a CI failure from a reviewer's decision;
# - at least one passed and none failed: the PR is marked ready for review.
#
# A draft with a check still pending, or with no check run, stays a draft. A PR already ready for
# review is not a draft and is left alone. Prints one line per PR it closes or marks ready;
# `--dry-run` prints the same lines and changes nothing.
set -euo pipefail

REPO_SLUG="cambra-dev/cambra"
CLOSE_PREFIX="Closed by the daily simplification run: CI failed"
dry=0
[[ "${1:-}" == "--dry-run" ]] && dry=1

drafts="$(gh pr list --repo "${REPO_SLUG}" --state open --search "head:simplify-agent/ draft:true" \
  --limit 200 --json number,headRefName,isDraft \
  --jq '.[] | select(.isDraft and (.headRefName | startswith("simplify-agent/"))) | .number')"

for n in ${drafts}; do
  # `gh pr checks` exits non-zero when a check failed or is pending, and errors when none ran.
  checks="$(gh pr checks "${n}" --repo "${REPO_SLUG}" --json name,bucket 2>/dev/null || true)"
  [[ -n "${checks}" ]] || continue
  pending="$(jq '[.[] | select(.bucket == "pending")] | length' <<<"${checks}")"
  passed="$(jq '[.[] | select(.bucket == "pass")] | length' <<<"${checks}")"
  failed="$(jq -r '[.[] | select(.bucket == "fail") | .name] | join(", ")' <<<"${checks}")"
  ((pending == 0)) || continue
  if [[ -n "${failed}" ]]; then
    if ((dry)); then
      echo "would close #${n}: ${failed}"
    else
      gh pr close "${n}" --repo "${REPO_SLUG}" --comment "${CLOSE_PREFIX} (${failed})."
      echo "closed #${n}: ${failed}"
    fi
  elif ((passed > 0)); then
    if ((dry)); then
      echo "would mark ready #${n}"
    else
      gh pr ready "${n}" --repo "${REPO_SLUG}" > /dev/null
      echo "marked ready #${n}"
    fi
  fi
done

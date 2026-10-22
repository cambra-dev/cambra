#!/usr/bin/env bash
# Close the run's draft PRs whose CI failed.
#
#   close-failed.sh [--dry-run]
#
# The run gates locally with `./ci.sh fast`, and GitHub CI runs the full gate on each draft. The
# next run's preflight reads that result here. A draft on a `simplify-agent/` branch whose checks
# have all finished, with at least one failed, is closed with a comment starting `CLOSE_PREFIX`;
# history.py reads that prefix to tell a CI failure from a reviewer's decision. A PR a human marked
# ready for review stays open, as does one with a check still pending. Prints one line per PR it
# closes; `--dry-run` prints the same lines and closes nothing.
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
  failed="$(jq -r '[.[] | select(.bucket == "fail") | .name] | join(", ")' <<<"${checks}")"
  if ((pending > 0)) || [[ -z "${failed}" ]]; then
    continue
  fi
  if ((dry)); then
    echo "would close #${n}: ${failed}"
  else
    gh pr close "${n}" --repo "${REPO_SLUG}" --comment "${CLOSE_PREFIX} (${failed})."
    echo "closed #${n}: ${failed}"
  fi
done

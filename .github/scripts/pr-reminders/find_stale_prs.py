#!/usr/bin/env python3
"""Find PRs waiting on general review (open 24h, no approval or changes
requested, CI green on one of the last 5 heads, no individual reviewer requested)
and review requests pending over 10 hours.

CI is the checks the default branch's rulesets require, and the workflows in this
checkout that report them; see prreminder.required_check_workflows.

Outputs one JSON object to stdout:
  "now":       the reference time, ISO 8601
  "general_review": groups of GeneralReviewPr (see prreminder.find_general_review_prs), each a list
  "reviews":   StaleReview objects, sorted by (reviewer, pr_number)

Required env: GH_TOKEN, GH_REPOSITORY
Optional env: STALE_NOW (epoch seconds or ISO timestamp, for testing)
Requires `yq` on PATH, to read the workflows.
"""

import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from prreminder import (
    find_general_review_prs,
    find_stale_reviews,
    get_branch_rules,
    get_default_branch,
    get_review_request_dates,
    last_green,
    list_open_prs,
    list_open_prs_with_reviewers,
    list_workflow_runs,
    load_workflows,
    parse_iso,
    required_check_names,
    required_check_workflows,
)

# This file is .github/scripts/pr-reminders/find_stale_prs.py.
REPO_ROOT = Path(__file__).resolve().parents[3]


def main() -> None:
    repo = os.environ["GH_REPOSITORY"]

    # Determine reference time
    stale_now = os.environ.get("STALE_NOW")
    if stale_now:
        try:
            epoch = int(stale_now)
            now = datetime.fromtimestamp(epoch, tz=timezone.utc)
        except ValueError:
            now = parse_iso(stale_now)
    else:
        now = datetime.now(timezone.utc)

    required = required_check_names(get_branch_rules(repo, get_default_branch(repo)))
    workflows = sorted(set(required_check_workflows(required, load_workflows(REPO_ROOT)).values()))

    def get_last_green(pr: dict) -> Optional[str]:
        return last_green({w: list_workflow_runs(repo, w, pr["headRefName"]) for w in workflows})

    general_review = find_general_review_prs(list_open_prs(repo), required, get_last_green, now=now)

    def get_dates(pr_number: int) -> dict[str, str]:
        return get_review_request_dates(repo, pr_number)

    reviews = find_stale_reviews(list_open_prs_with_reviewers(repo), get_dates, now=now)

    json.dump({
        "now": now.isoformat(),
        "general_review": [[p.to_dict() for p in group] for group in general_review],
        "reviews": [r.to_dict() for r in reviews],
    }, sys.stdout)
    print()


if __name__ == "__main__":
    main()

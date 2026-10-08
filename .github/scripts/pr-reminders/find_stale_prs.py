#!/usr/bin/env python3
"""Find PRs waiting on general review (open 24h, no approval or changes
requested, passing CI, no individual reviewer requested) and review requests pending over 10 hours.

Outputs one JSON object to stdout:
  "now":       the reference time, ISO 8601
  "general_review": groups of GeneralReviewPr (see prreminder.find_general_review_prs), each a list
  "reviews":   StaleReview objects, sorted by (reviewer, pr_number)

Required env: GH_TOKEN, GH_REPOSITORY
Optional env: STALE_NOW (epoch seconds or ISO timestamp, for testing)
"""

import json
import os
import sys
from datetime import datetime, timezone

from prreminder import (
    find_general_review_prs,
    find_stale_reviews,
    get_review_request_dates,
    list_open_prs,
    list_open_prs_with_reviewers,
    parse_iso,
)


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

    general_review = find_general_review_prs(list_open_prs(repo), now=now)

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

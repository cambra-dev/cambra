#!/usr/bin/env python3
"""Find open PRs with review requests pending for over 24 hours.

Outputs JSONL to stdout: one JSON object per stale review, sorted by (reviewer, pr_number).

Required env: GH_TOKEN, GH_REPOSITORY
Optional env: STALE_NOW (epoch seconds or ISO timestamp, for testing)
"""

import json
import os
import sys
from datetime import datetime, timezone

from prreminder import (
    find_stale_reviews,
    get_review_request_dates,
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

    prs = list_open_prs_with_reviewers(repo)
    if not prs:
        sys.exit(0)

    def get_dates(pr_number: int) -> dict[str, str]:
        return get_review_request_dates(repo, pr_number)

    stale = find_stale_reviews(prs, get_dates, now=now)

    for review in stale:
        print(json.dumps(review.to_dict()))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Tests for the stale PR review reminder system.

Direct function calls against fixture data — no subprocess, no mock gh, no jq dependency.
"""

import json
import sys
from datetime import datetime, timedelta, timezone

from prreminder import (
    StaleReview,
    build_thread_body,
    find_stale_reviews,
    format_mention,
)

# Reference time: 2026-02-05T12:00:00Z — all fixture dates are relative to this.
REFERENCE_TIME = datetime(2026, 2, 5, 12, 0, 0, tzinfo=timezone.utc)

PRS = [
    {
        "number": 101, "title": "Fix the widget",
        "url": "https://github.com/test/repo/pull/101",
        "author": {"login": "alice"},
        "reviewRequests": [{"login": "bob", "__typename": "User"}],
    },
    {
        "number": 102, "title": "Update dependencies",
        "url": "https://github.com/test/repo/pull/102",
        "author": {"login": "bob"},
        "reviewRequests": [{"login": "alice", "__typename": "User"}],
    },
    {
        "number": 103, "title": "Team-only review",
        "url": "https://github.com/test/repo/pull/103",
        "author": {"login": "charlie"},
        "reviewRequests": [
            {"__typename": "Team", "name": "Engineering", "slug": "cambra-dev/engineering"},
        ],
    },
    {
        "number": 104, "title": "Per-reviewer staleness",
        "url": "https://github.com/test/repo/pull/104",
        "author": {"login": "alice"},
        "reviewRequests": [
            {"login": "bob", "__typename": "User"},
            {"login": "charlie", "__typename": "User"},
        ],
    },
    {
        "number": 105, "title": "Draft PR being ignored",
        "url": "https://github.com/test/repo/pull/105",
        "author": {"login": "alice"},
        "isDraft": True,
        "reviewRequests": [{"login": "bob", "__typename": "User"}],
    },
]

TIMELINES: dict[int, dict[str, str]] = {
    # 50h before reference — stale
    101: {"bob": "2026-02-03T10:00:00Z"},
    # 30min before reference — fresh
    102: {"alice": "2026-02-05T11:30:00Z"},
    # Team-only request — no individual reviewer dates
    103: {},
    # Two reviewers: bob requested 50h ago (stale), charlie requested 30min ago (fresh)
    104: {"bob": "2026-02-03T10:00:00Z", "charlie": "2026-02-05T11:30:00Z"},
    # Stale but draft
    105: {"bob": "2026-02-03T10:00:00Z"},
}


def get_review_dates(pr_number: int) -> dict[str, str]:
    """Test fixture: return review request dates for a PR."""
    return TIMELINES.get(pr_number, {})


def main() -> None:
    passed = 0
    failed = 0

    def check(condition: bool, pass_msg: str, fail_msg: str) -> None:
        nonlocal passed, failed
        if condition:
            print(f"  PASS: {pass_msg}")
            passed += 1
        else:
            print(f"  FAIL: {fail_msg}")
            failed += 1

    # --- Staleness logic tests ---
    print("Staleness logic:")
    stale = find_stale_reviews(PRS, get_review_dates, now=REFERENCE_TIME, threshold=timedelta(hours=24))
    stale_keys = [(r.reviewer, r.pr_number) for r in stale]

    check(
        ("bob", 101) in stale_keys,
        "stale PR #101 found for reviewer bob",
        "expected stale PR #101 for reviewer bob",
    )
    check(
        not any(pr == 102 for _, pr in stale_keys),
        "PR #102 correctly excluded (requested <24h ago)",
        "PR #102 should not appear (requested <24h ago)",
    )
    check(
        not any(pr == 103 for _, pr in stale_keys),
        "PR #103 correctly excluded (team-only request)",
        "PR #103 should not appear (team-only request)",
    )
    check(
        ("bob", 104) in stale_keys,
        "stale PR #104 found for reviewer bob (requested 50h ago)",
        "expected stale PR #104 for reviewer bob",
    )
    check(
        ("charlie", 104) not in stale_keys,
        "PR #104 correctly excludes charlie (requested <24h ago)",
        "PR #104 should not list charlie (requested <24h ago)",
    )
    check(
        not any(pr == 105 for _, pr in stale_keys),
        "PR #105 correctly excluded (is draft)",
        "PR #105 should not appear (is draft)",
    )

    # --- JSONL round-trip test ---
    print("\nJSONL round-trip:")
    review_with_tabs = StaleReview(
        reviewer="bob", pr_number=101,
        title="Fix\tthe\twidget",  # tabs in title
        url="https://github.com/test/repo/pull/101",
        author="alice",
        requested_date="Feb 03, 2026",
        requested_iso="2026-02-03T10:00:00Z",
    )
    jsonl_line = json.dumps(review_with_tabs.to_dict())
    roundtripped = StaleReview.from_dict(json.loads(jsonl_line))
    check(
        roundtripped == review_with_tabs,
        "StaleReview with tabs in title survives JSONL round-trip",
        f"JSONL round-trip failed: {roundtripped} != {review_with_tabs}",
    )

    # --- Slack formatting tests ---
    print("\nSlack formatting:")
    usermap = {"bob": "U12345"}

    check(
        format_mention("bob", usermap) == "<@U12345>",
        "format_mention resolves known user to Slack mention",
        f"format_mention('bob') returned {format_mention('bob', usermap)!r}",
    )
    check(
        format_mention("unknown", usermap) == "@unknown _(GitHub)_",
        "format_mention falls back for unknown user",
        f"format_mention('unknown') returned {format_mention('unknown', usermap)!r}",
    )

    body = build_thread_body(stale, usermap)
    check(
        "*<@U12345>*" in body and "@unknown" not in body,
        "build_thread_body uses Slack mentions for known users",
        f"build_thread_body output unexpected: {body[:200]!r}",
    )

    # --- Summary ---
    print(f"\nResults: {passed} passed, {failed} failed")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()

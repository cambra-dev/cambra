#!/usr/bin/env python3
"""Tests for the stale PR review reminder system.

Direct function calls against fixture data — no subprocess, no mock gh, no jq dependency.
"""

import json
import sys
from datetime import datetime, timedelta, timezone

from prreminder import (
    GeneralReviewPr,
    StaleReview,
    build_general_review_section,
    build_thread_body,
    ci_passed,
    review_verdict,
    find_general_review_prs,
    find_stale_reviews,
    format_duration,
    format_mention,
    format_pr_link,
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


def hours_ago(h: float) -> str:
    t = REFERENCE_TIME - timedelta(hours=h)
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


def check_run(name: str, conclusion: str | None, started_h: float, status: str = "COMPLETED") -> dict:
    return {"__typename": "CheckRun", "name": name, "status": status,
            "conclusion": conclusion, "startedAt": hours_ago(started_h)}


GREEN = [check_run("test", "SUCCESS", 1), check_run("check", "SUCCESS", 1)]


def open_pr(number: int, *, opened_h: float, checks: list[dict], base: str = "main",
            draft: bool = False, ready_h: float | None = None,
            last_action_h: float = 1, reviewers: list[str] | None = None,
            decision: str | None = None, reviews: list[str] | None = None) -> dict:
    """An open PR as list_open_prs returns it. Its head branch is `b<number>`."""
    return {
        "number": number, "title": f"PR {number}",
        "url": f"https://github.com/test/repo/pull/{number}",
        "author": "alice", "isDraft": draft,
        "createdAt": hours_ago(opened_h), "updatedAt": hours_ago(last_action_h),
        "readyForReviewAt": hours_ago(ready_h) if ready_h is not None else None,
        "baseRefName": base, "headRefName": f"b{number}",
        "checks": checks,
        "requestedReviewers": reviewers or [],
        "reviewDecision": decision,
        "latestReviewStates": reviews or [],
    }


OPEN_PRS = [
    open_pr(201, opened_h=50, checks=GREEN),
    open_pr(202, opened_h=30, checks=GREEN),
    # Older runs of a re-run check failed or were cancelled; the latest run passed.
    open_pr(204, opened_h=45, checks=[
        check_run("test", "CANCELLED", 10), check_run("check", "FAILURE", 10),
        check_run("test", "SUCCESS", 5), check_run("check", "SUCCESS", 5),
    ]),
    # Excluded: CI failed.
    open_pr(203, opened_h=50, checks=[check_run("test", "SUCCESS", 1), check_run("check", "FAILURE", 1)]),
    # Excluded: the latest run failed after an earlier one passed.
    open_pr(213, opened_h=50, checks=[check_run("test", "SUCCESS", 10), check_run("test", "FAILURE", 5)]),
    # Excluded: no checks have run.
    open_pr(205, opened_h=50, checks=[]),
    # Excluded: draft.
    open_pr(206, opened_h=50, checks=GREEN, draft=True),
    # Excluded: created 50h ago but marked ready for review 2h ago.
    open_pr(207, opened_h=50, checks=GREEN, ready_h=2),
    # Excluded: a check is still running.
    open_pr(208, opened_h=50, checks=GREEN + [check_run("formal", None, 1, status="IN_PROGRESS")]),
    # Excluded: a commit status failed.
    open_pr(209, opened_h=50, checks=GREEN + [{
        "__typename": "StatusContext", "context": "ext", "state": "FAILURE",
        "createdAt": hours_ago(1)}]),
    # Stack main <- b210 <- b211 (draft) <- b212, listed top first.
    open_pr(212, opened_h=60, checks=GREEN, base="b211", last_action_h=26),
    open_pr(211, opened_h=60, checks=GREEN, base="b210", draft=True),
    open_pr(210, opened_h=40, checks=GREEN),
    # Excluded: an individual reviewer is requested, so the reviewer reminder covers it.
    open_pr(215, opened_h=50, checks=GREEN, reviewers=["bob"]),
    # Excluded: approved under a review requirement.
    open_pr(216, opened_h=50, checks=GREEN, decision="APPROVED", reviews=["APPROVED"]),
    # Excluded: approved with no review requirement (reviewDecision is null).
    open_pr(217, opened_h=50, checks=GREEN, reviews=["COMMENTED", "APPROVED"]),
    # Excluded: changes requested under a review requirement.
    open_pr(218, opened_h=50, checks=GREEN, decision="CHANGES_REQUESTED", reviews=["CHANGES_REQUESTED"]),
    # Excluded: changes requested with no review requirement.
    open_pr(219, opened_h=50, checks=GREEN, reviews=["CHANGES_REQUESTED"]),
    # Included: comment-only reviews give no verdict.
    open_pr(221, opened_h=35, checks=GREEN, decision="REVIEW_REQUIRED", reviews=["COMMENTED"]),
    # Included: open over a week.
    open_pr(222, opened_h=200, checks=GREEN),
    # Excluded: opened under 24h ago.
    open_pr(214, opened_h=10, checks=GREEN),
]


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

    # --- General review tests ---
    print("\nGeneral review:")
    groups = find_general_review_prs(OPEN_PRS, now=REFERENCE_TIME)
    shape = [[p.pr_number for p in g] for g in groups]
    expected = [[222], [210, 212], [201], [204], [221], [202]]
    check(
        shape == expected,
        f"general review groups are {expected}: stack bottom first, groups by earliest open time",
        f"general review groups: expected {expected}, got {shape}",
    )
    verdict_cases = [
        (dict(decision="APPROVED"), "APPROVED"),
        (dict(decision="CHANGES_REQUESTED"), "CHANGES_REQUESTED"),
        (dict(decision="REVIEW_REQUIRED", reviews=["APPROVED"]), None),
        (dict(reviews=["APPROVED"]), "APPROVED"),
        (dict(reviews=["APPROVED", "CHANGES_REQUESTED"]), "CHANGES_REQUESTED"),
        (dict(reviews=["COMMENTED"]), None),
        (dict(), None),
    ]
    verdict_got = [review_verdict(open_pr(1, opened_h=1, checks=[], **kw)) for kw, _ in verdict_cases]
    check(
        verdict_got == [want for _, want in verdict_cases],
        "review_verdict follows reviewDecision, else latest reviews",
        f"review_verdict: expected {[w for _, w in verdict_cases]}, got {verdict_got}",
    )
    check(
        ci_passed([check_run("test", "SUCCESS", 1), check_run("lint", "SKIPPED", 1)]),
        "ci_passed accepts a SKIPPED check",
        "ci_passed rejected a SKIPPED check",
    )
    stack_top = groups[1][1]
    check(
        stack_top.opened_iso == hours_ago(60) and stack_top.last_action_iso == hours_ago(26),
        "GeneralReviewPr carries open time and last-action time",
        f"GeneralReviewPr times wrong: {stack_top}",
    )
    ready = find_general_review_prs([open_pr(220, opened_h=100, ready_h=30, checks=GREEN)], now=REFERENCE_TIME)
    check(
        ready[0][0].opened_iso == hours_ago(30),
        "open time is the ready-for-review time when there is one",
        f"open time for a once-draft PR: got {ready[0][0].opened_iso}",
    )

    # --- JSON round-trip test ---
    print("\nJSON round-trip:")
    review_with_tabs = StaleReview(
        reviewer="bob", pr_number=101,
        title="Fix\tthe\twidget",  # tabs in title
        url="https://github.com/test/repo/pull/101",
        author="alice",
        requested_iso="2026-02-03T10:00:00Z",
    )
    json_text = json.dumps(review_with_tabs.to_dict())
    roundtripped = StaleReview.from_dict(json.loads(json_text))
    check(
        roundtripped == review_with_tabs,
        "StaleReview with tabs in title survives JSON round-trip",
        f"JSON round-trip failed: {roundtripped} != {review_with_tabs}",
    )

    check(
        GeneralReviewPr.from_dict(json.loads(json.dumps(stack_top.to_dict()))) == stack_top,
        "GeneralReviewPr survives JSON round-trip",
        "GeneralReviewPr JSON round-trip failed",
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

    durations = [format_duration(timedelta(minutes=m)) for m in (5, 60, 125, 24 * 60, 26 * 60 + 30)]
    check(
        durations == ["<1h", "~1h", "~3h", "1.0d", "1.1d"],
        "format_duration renders <1h, hours rounded up, then days to one decimal",
        f"format_duration output unexpected: {durations}",
    )
    long_link = format_pr_link("u", 303, "Lift a collection fed outside any iteration to one unit-keyed element")
    check(
        long_link == "<u|#303: Lift a collection fed outside any...>",
        "format_pr_link cuts link text to 40 characters and appends ...",
        f"format_pr_link long title: {long_link!r}",
    )
    check(
        format_pr_link("u", 1, "a < b & c") == "<u|#1: a &lt; b &amp; c>",
        "format_pr_link escapes Slack control characters",
        f"format_pr_link escaping: {format_pr_link('u', 1, 'a < b & c')!r}",
    )

    section = build_general_review_section(groups, REFERENCE_TIME)

    def line(n: int, times: str, marker: str = "\u2022") -> str:
        return f"{marker} <https://github.com/test/repo/pull/{n}|#{n}: PR {n}> \u2014 by *alice*, {times}"

    expected_section = "\n".join([
        "*Waiting on General Review*",
        "",
        "*Open &gt;1w*",
        line(222, "open 8.3d, last action ~1h ago"),
        "",
        "*Open &lt;1w*",
        "_Stack onto_ `main`",
        line(210, "open 1.7d, last action ~1h ago", "1."),
        line(212, "open 2.5d, last action 1.1d ago", "2."),
        "",
        line(201, "open 2.1d, last action ~1h ago"),
        "",
        "*Open &lt;2d*",
        line(204, "open 1.9d, last action ~1h ago"),
        line(221, "open 1.5d, last action ~1h ago"),
        line(202, "open 1.2d, last action ~1h ago"),
    ])
    check(
        section == expected_section,
        "build_general_review_section buckets groups by oldest PR, each stack its own list, tagging no one",
        f"build_general_review_section output:\n{section}",
    )
    reviewer_line = build_thread_body(stale, usermap, now=REFERENCE_TIME).splitlines()[1]
    check(
        reviewer_line == "\u2022 <https://github.com/test/repo/pull/101|#101: Fix the widget> "
        "\u2014 by *alice*, review requested 2.1d ago",
        "reviewer reminder lines share the general-review line format",
        f"reviewer reminder line: {reviewer_line!r}",
    )

    full = build_thread_body(stale, {"alice": "U999", **usermap}, general_review=groups, now=REFERENCE_TIME)
    check(
        full.startswith("*Waiting on General Review*") and full.index("*<@U12345>*") > full.index("#202"),
        "build_thread_body puts Waiting on General Review first, before reviewer reminders",
        f"build_thread_body order unexpected: {full[:200]!r}",
    )
    check(
        "<@U999>" not in full,
        "Waiting on General Review does not mention the PR author",
        "Waiting on General Review mentioned the PR author",
    )
    only_prs = build_thread_body([], usermap, general_review=groups, now=REFERENCE_TIME)
    check(
        only_prs == section,
        "build_thread_body with no stale reviews is the Waiting on General Review section alone",
        f"build_thread_body without reviews: {only_prs[:200]!r}",
    )

    # --- Summary ---
    print(f"\nResults: {passed} passed, {failed} failed")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()

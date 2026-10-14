#!/usr/bin/env python3
"""Tests for the stale PR review reminder system.

Direct function calls against fixture data — no subprocess, no mock gh, no jq dependency.
"""

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

from prreminder import (
    GeneralReviewPr,
    open_pr_from_node,
    StaleReview,
    build_general_review_section,
    build_thread_body,
    ci_state,
    review_verdict,
    find_general_review_prs,
    find_stale_reviews,
    format_duration,
    format_mention,
    format_pr_link,
    last_green,
    load_workflows,
    required_check_names,
    required_check_workflows,
)

# Reference time: 2026-02-05T12:00:00Z — all fixture dates are relative to this.
REFERENCE_TIME = datetime(2026, 2, 5, 12, 0, 0, tzinfo=timezone.utc)

def reviewer_pr(number: int, title: str, author: str, reviewers: list[str], draft: bool = False) -> dict:
    """An open PR with individual reviewers requested, as list_open_prs returns it."""
    return {"number": number, "title": title, "url": f"https://github.com/test/repo/pull/{number}",
            "author": author, "isDraft": draft, "requestedReviewers": reviewers}


PRS = [
    reviewer_pr(101, "Fix the widget", "alice", ["bob"]),
    reviewer_pr(102, "Update dependencies", "bob", ["alice"]),
    # Team-only review: list_open_prs keeps individual reviewers only.
    reviewer_pr(103, "Team-only review", "charlie", []),
    reviewer_pr(104, "Per-reviewer staleness", "alice", ["bob", "charlie"]),
    reviewer_pr(105, "Draft PR being ignored", "alice", ["bob"], draft=True),
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


# The checks the rulesets require; "test" stands for a gate merging does not require.
REQUIRED = ["check"]
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
    # Excluded: the required check failed and no recent head was green.
    open_pr(203, opened_h=50, checks=[check_run("test", "SUCCESS", 1), check_run("check", "FAILURE", 1)]),
    # Excluded: the required check's latest run failed after an earlier one passed.
    open_pr(213, opened_h=50, checks=[check_run("check", "SUCCESS", 10), check_run("check", "FAILURE", 5)]),
    # Excluded: no checks have run.
    open_pr(205, opened_h=50, checks=[]),
    # Excluded: draft.
    open_pr(206, opened_h=50, checks=GREEN, draft=True),
    # Excluded: created 50h ago but marked ready for review 2h ago.
    open_pr(207, opened_h=50, checks=GREEN, ready_h=2),
    # Excluded: the required check is still running and no recent head was green.
    open_pr(208, opened_h=50, checks=[check_run("test", "SUCCESS", 1),
                                      check_run("check", None, 1, status="IN_PROGRESS")]),
    # Included: a commit status merging does not require failed.
    open_pr(209, opened_h=50, checks=GREEN + [{
        "__typename": "StatusContext", "context": "ext", "state": "FAILURE",
        "createdAt": hours_ago(1)}]),
    # Included: the required check failed, but an earlier head went green 3h ago.
    open_pr(223, opened_h=49, checks=[check_run("check", "FAILURE", 1)]),
    # Included: the required check is running, and an earlier head went green 2h ago.
    open_pr(224, opened_h=47, checks=[check_run("check", None, 1, status="IN_PROGRESS")]),
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


LAST_GREEN = {223: hours_ago(3), 224: hours_ago(2)}


def run(sha: str, created_h: float, conclusion: str | None, finished_h: float | None = None) -> dict:
    """A workflow run as list_workflow_runs returns it."""
    return {"head_sha": sha, "status": "completed" if conclusion else "in_progress",
            "conclusion": conclusion, "created_at": hours_ago(created_h),
            "updated_at": hours_ago(finished_h if finished_h is not None else created_h)}


def raises(f) -> bool:
    try:
        f()
    except ValueError:
        return True
    return False


# Shaped like GET /repos/{repo}/rules/branches/main for this repo.
RULES = [
    {"type": "deletion", "ruleset_id": 1},
    {"type": "pull_request", "ruleset_id": 1, "parameters": {"required_approving_review_count": 1}},
    {"type": "required_status_checks", "ruleset_id": 2, "parameters": {
        "required_status_checks": [{"context": "check", "integration_id": 15368}],
        "strict_required_status_checks_policy": False}},
]

WORKFLOWS = {
    ".github/workflows/ci.yml": {"jobs": {
        "lint": {"runs-on": "ubuntu-latest"},
        "check": {"needs": ["lint"], "runs-on": "ubuntu-latest"},
        "test": {"strategy": {"matrix": {"os": ["a", "b"]}}},
    }},
    ".github/workflows/integration.yml": {"jobs": {
        "run": {"name": "IntegrationTests"},
        "lint": {"name": "lint"},
        "shared": {"uses": "./.github/workflows/reusable.yml"},
        "dynamic": {"name": "${{ inputs.label }}"},
    }},
}


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
    asked: list[int] = []

    def get_last_green(pr: dict) -> str | None:
        asked.append(pr["number"])
        return LAST_GREEN.get(pr["number"])

    groups = find_general_review_prs(OPEN_PRS, REQUIRED, get_last_green, now=REFERENCE_TIME)
    shape = [[p.pr_number for p in g] for g in groups]
    expected = [[222], [210, 212], [201], [209], [223], [224], [204], [221], [202]]
    check(
        shape == expected,
        f"general review groups are {expected}: stack bottom first, groups by earliest open time",
        f"general review groups: expected {expected}, got {shape}",
    )
    check(
        sorted(asked) == [203, 205, 208, 213, 223, 224],
        "earlier heads are looked up only for PRs that qualify but for their head's CI",
        f"earlier heads looked up for {sorted(asked)}",
    )
    by_number = {p.pr_number: p for g in groups for p in g}
    check(
        [(by_number[n].ci, by_number[n].last_green_iso) for n in (201, 223, 224)]
        == [("passed", None), ("failing", hours_ago(3)), ("running", hours_ago(2))],
        "GeneralReviewPr carries the head's CI state and when an earlier head went green",
        f"CI fields: {[(by_number[n].ci, by_number[n].last_green_iso) for n in (201, 223, 224)]}",
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
    def pending_status(context: str) -> dict:
        return {"__typename": "StatusContext", "context": context, "state": "PENDING", "createdAt": hours_ago(1)}

    ci_cases = [
        ([check_run("check", "SKIPPED", 1)], ["check"], "passed"),
        ([check_run("check", "SUCCESS", 1), check_run("test", "FAILURE", 1)], ["check"], "passed"),
        ([check_run("check", "FAILURE", 5), check_run("check", "SUCCESS", 1)], ["check"], "passed"),
        ([check_run("check", "SUCCESS", 5), check_run("check", "FAILURE", 1)], ["check"], "failing"),
        ([check_run("check", None, 1, status="QUEUED")], ["check"], "running"),
        ([check_run("test", "SUCCESS", 1)], ["check"], "running"),
        ([pending_status("ext")], ["ext"], "running"),
        ([check_run("check", "FAILURE", 1), pending_status("ext")], ["check", "ext"], "failing"),
    ]
    ci_got = [ci_state(checks, required) for checks, required, _ in ci_cases]
    check(
        ci_got == [want for *_, want in ci_cases],
        "ci_state judges each required check by its latest run, ignores the rest, and reads a missing one as running",
        f"ci_state: expected {[w for *_, w in ci_cases]}, got {ci_got}",
    )
    stack_top = groups[1][1]
    check(
        stack_top.opened_iso == hours_ago(60) and stack_top.last_action_iso == hours_ago(26),
        "GeneralReviewPr carries open time and last-action time",
        f"GeneralReviewPr times wrong: {stack_top}",
    )
    ready = find_general_review_prs([open_pr(220, opened_h=100, ready_h=30, checks=GREEN)], REQUIRED,
                                   get_last_green, now=REFERENCE_TIME)
    check(
        ready[0][0].opened_iso == hours_ago(30),
        "open time is the ready-for-review time when there is one",
        f"open time for a once-draft PR: got {ready[0][0].opened_iso}",
    )

    # --- Reading the open-PRs query ---
    print("\nOpen-PR query nodes:")
    # Shaped like #310's node: approved, then a comment-only review by the same reviewer.
    node = {
        "number": 310, "title": "t", "url": "u", "isDraft": False,
        "createdAt": hours_ago(150), "updatedAt": hours_ago(17),
        "baseRefName": "b309", "headRefName": "b310", "reviewDecision": None,
        "author": {"login": "dpmills"},
        "latestOpinionatedReviews": {"nodes": [{"state": "APPROVED"}]},
        "reviewRequests": {"nodes": [
            {"requestedReviewer": {"__typename": "Team"}},
            {"requestedReviewer": {"__typename": "User", "login": "sortalongo"}},
        ]},
        "readyEvents": {"nodes": [{"createdAt": hours_ago(150)}]},
        "commits": {"nodes": [{"commit": {"statusCheckRollup": {"contexts": {"nodes": GREEN}}}}]},
    }
    flat = open_pr_from_node(node)
    check(
        review_verdict(flat) == "APPROVED",
        "an approval followed by a comment-only review still reads as approved",
        f"verdict after approve-then-comment: {review_verdict(flat)}",
    )
    check(
        flat["requestedReviewers"] == ["sortalongo"] and flat["author"] == "dpmills"
        and flat["readyForReviewAt"] == hours_ago(150) and flat["checks"] == GREEN,
        "open_pr_from_node keeps individual reviewers, the author's login, the ready time, and the head's checks",
        f"open_pr_from_node: {flat}",
    )

    # --- Required checks ---
    print("\nRequired checks:")
    check(
        required_check_names(RULES) == ["check"],
        "required_check_names reads the required_status_checks rule",
        f"required_check_names: {required_check_names(RULES)}",
    )
    unattributed = [{"type": "required_status_checks", "parameters": {
        "required_status_checks": [{"context": "ext"}]}}]
    check(
        required_check_names(unattributed) == ["ext"],
        "required_check_names accepts a check that names no app",
        "required_check_names rejected a check that names no app",
    )
    other_app = [{"type": "required_status_checks", "parameters": {
        "required_status_checks": [{"context": "ci/circle", "integration_id": 9}]}}]
    required_workflow = RULES + [{"type": "workflows", "parameters": {"workflows": [{"path": "x.yml"}]}}]
    check(
        raises(lambda: required_check_names(other_app))
        and raises(lambda: required_check_names(required_workflow))
        and raises(lambda: required_check_names(RULES[:2])),
        "required_check_names raises on another app's check, a workflows rule, and no requirement",
        "required_check_names accepted a requirement it cannot judge",
    )
    check(
        required_check_workflows(["IntegrationTests", "check"], WORKFLOWS)
        == {"IntegrationTests": ".github/workflows/integration.yml", "check": ".github/workflows/ci.yml"},
        "required_check_workflows maps a check to its workflow by job key or job name",
        f"required_check_workflows: {required_check_workflows(['IntegrationTests', 'check'], WORKFLOWS)}",
    )
    check(
        all(raises(lambda n=n: required_check_workflows([n], WORKFLOWS))
            for n in ("lint", "test", "shared", "missing")),
        "required_check_workflows raises on a check two workflows report, a matrix job, a reusable call, and no job",
        "required_check_workflows mapped a check it cannot place",
    )
    repo_root = Path(__file__).resolve().parents[3]
    real = required_check_workflows(["check"], load_workflows(repo_root))
    check(
        real == {"check": ".github/workflows/ci.yml"},
        "this repo's workflows map `check` to ci.yml (needs yq)",
        f"this repo's workflows map `check` to {real}",
    )

    # --- Last green head ---
    print("\nLast green head:")
    ci = ".github/workflows/ci.yml"
    integ = ".github/workflows/integration.yml"
    green_cases = [
        ("newest head failed, the one before went green",
         {ci: [run("h3", 1, "failure"), run("h2", 3, "success", 2.5)]}, hours_ago(2.5)),
        ("a green head six heads back is out of range",
         {ci: [run(f"h{i}", i, "failure") for i in range(1, 6)] + [run("h6", 6, "success")]}, None),
        ("a green head five heads back counts",
         {ci: [run(f"h{i}", i, "failure") for i in range(1, 5)] + [run("h5", 5, "success")]}, hours_ago(5)),
        ("a cancelled run beside a successful one on the same head",
         {ci: [run("h1", 1, None), run("h2", 4, "cancelled"), run("h2", 3, "success", 2)]}, hours_ago(2)),
        ("a head green in one required workflow only",
         {ci: [run("h1", 2, "success")], integ: [run("h1", 2, "failure")]}, None),
        ("a head green in both workflows went green when the later finished",
         {ci: [run("h1", 3, "success", 2.5)], integ: [run("h1", 3, "success", 1.5)]}, hours_ago(1.5)),
        ("no runs", {ci: []}, None),
    ]
    for desc, runs, want in green_cases:
        got = last_green(runs)
        check(got == want, f"last_green: {desc}", f"last_green: {desc}: expected {want}, got {got}")

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
        line(209, "open 2.1d, last action ~1h ago"),
        line(223, "open 2.0d, last action ~1h ago, CI failing, last green ~3h ago"),
        "",
        "*Open &lt;2d*",
        line(224, "open 2.0d, last action ~1h ago, CI running, last green ~2h ago"),
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

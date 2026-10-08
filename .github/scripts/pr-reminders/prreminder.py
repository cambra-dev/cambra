"""Shared module for the stale PR review reminder system.

Contains dataclasses, gh CLI wrappers, Slack API helpers, and staleness logic.
All dependencies are Python stdlib only.
"""

import json
import math
import subprocess
import sys
import urllib.request
import urllib.parse
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta, timezone
from typing import Any, Callable, Optional


# ---------------------------------------------------------------------------
# Date helpers
# ---------------------------------------------------------------------------


def parse_iso(s: str) -> datetime:
    """Parse an ISO 8601 timestamp, handling the Z suffix for Python <3.11."""
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


# ---------------------------------------------------------------------------
# StaleReview dataclass
# ---------------------------------------------------------------------------


@dataclass
class StaleReview:
    reviewer: str
    pr_number: int
    title: str
    url: str
    author: str
    requested_iso: str  # original ISO timestamp

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "StaleReview":
        return cls(**d)


@dataclass
class GeneralReviewPr:
    """An open, non-draft PR with no review verdict, passing CI, and no individual
    reviewer requested, which has waited past the threshold."""

    pr_number: int
    title: str
    url: str
    author: str
    base: str
    head: str
    opened_iso: str  # last ready-for-review time, or creation time
    last_action_iso: str  # the PR's updatedAt

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "GeneralReviewPr":
        return cls(**d)


# ---------------------------------------------------------------------------
# gh CLI wrappers
# ---------------------------------------------------------------------------


def _run_gh(args: list[str]) -> subprocess.CompletedProcess:
    result = subprocess.run(
        ["gh"] + args,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(
            f"::error::gh {' '.join(args)} failed: {result.stderr.strip()}",
            file=sys.stderr,
        )
        raise RuntimeError(f"gh failed: {result.stderr.strip()}")
    return result


def gh_json(*args: str) -> Any:
    """Run a gh command and parse its JSON stdout."""
    result = _run_gh(list(args))
    return json.loads(result.stdout)


def gh_lines(*args: str) -> list[str]:
    """Run a gh command and return non-empty stdout lines."""
    result = _run_gh(list(args))
    return [line for line in result.stdout.splitlines() if line.strip()]


def list_open_prs_with_reviewers(repo: str) -> list[dict]:
    """List open, non-draft PRs that have at least one review request (individual user)."""
    lines = gh_lines(
        "pr",
        "list",
        "--repo",
        repo,
        "--state",
        "open",
        "--json",
        "number,title,url,author,reviewRequests,isDraft",
        "--jq",
        ".[] | select(.isDraft == false and (.reviewRequests | length > 0))",
    )
    return [json.loads(line) for line in lines]


_OPEN_PRS_QUERY = """
query($owner: String!, $name: String!, $endCursor: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: 50, after: $endCursor) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number title url isDraft createdAt updatedAt baseRefName headRefName
        reviewDecision
        author { login }
        latestReviews(first: 50) { nodes { state } }
        reviewRequests(first: 20) {
          nodes { requestedReviewer { __typename ... on User { login } } }
        }
        readyEvents: timelineItems(last: 1, itemTypes: [READY_FOR_REVIEW_EVENT]) {
          nodes { ... on ReadyForReviewEvent { createdAt } }
        }
        commits(last: 1) { nodes { commit { statusCheckRollup { contexts(first: 100) {
          nodes {
            __typename
            ... on CheckRun { name status conclusion startedAt }
            ... on StatusContext { context state createdAt }
          }
        } } } } }
      }
    }
  }
}
"""


def list_open_prs(repo: str) -> list[dict]:
    """List every open PR (drafts included) with its head commit's checks.

    Drafts are returned because stack grouping follows base branches through them.
    """
    owner, name = repo.split("/", 1)
    lines = gh_lines(
        "api", "graphql", "--paginate",
        "-f", f"query={_OPEN_PRS_QUERY}",
        "-F", f"owner={owner}",
        "-F", f"name={name}",
        "--jq", ".data.repository.pullRequests.nodes[]",
    )
    prs = []
    for line in lines:
        node = json.loads(line)
        ready = node.pop("readyEvents")["nodes"]
        requested = node.pop("reviewRequests")["nodes"]
        latest_reviews = node.pop("latestReviews")["nodes"]
        commits = node.pop("commits")["nodes"]
        rollup = commits[0]["commit"]["statusCheckRollup"] if commits else None
        prs.append({
            **node,
            "author": (node.get("author") or {}).get("login", "ghost"),
            "readyForReviewAt": ready[0]["createdAt"] if ready else None,
            # Individual reviewers only: a team request names no one, so it
            # leaves the PR waiting on general review.
            "latestReviewStates": [r["state"] for r in latest_reviews],
            "requestedReviewers": [
                r["requestedReviewer"]["login"] for r in requested
                if (r.get("requestedReviewer") or {}).get("__typename") == "User"
            ],
            "checks": rollup["contexts"]["nodes"] if rollup else [],
        })
    return prs


def get_review_request_dates(repo: str, pr_number: int) -> dict[str, str]:
    """Get the most recent review_requested timestamp per individual reviewer.

    Returns {reviewer_login: iso_timestamp}.
    """
    lines = gh_lines(
        "api",
        f"repos/{repo}/issues/{pr_number}/timeline",
        "--paginate",
        "--jq",
        '.[] | select(.event == "review_requested" and .requested_reviewer != null) '
        "| {login: .requested_reviewer.login, ts: .created_at}",
    )
    # Merge across pages, taking max timestamp per reviewer
    dates: dict[str, str] = {}
    for line in lines:
        obj = json.loads(line)
        login = obj["login"]
        ts = obj["ts"]
        if login not in dates or ts > dates[login]:
            dates[login] = ts
    return dates


def list_collaborators(repo: str) -> list[str]:
    """List collaborator logins for a repo."""
    print(f"Fetching collaborators for {repo}...")
    try:
        lines = gh_lines(
            "api", f"repos/{repo}/collaborators", "--paginate", "--jq", ".[].login"
        )
        collaborators = sorted(set(lines))
        print(f"Found {len(collaborators)} collaborators: {', '.join(collaborators)}")
        return collaborators
    except Exception as e:
        print(f"::warning::Failed to list collaborators: {e}")
        return []


def list_recent_users(repo: str) -> list[str]:
    """List users who recently interacted with PRs as a fallback."""
    print(f"Fetching users from recent PR activity for {repo}...")
    try:
        # Get authors and reviewers from last 50 PRs (any state)
        lines = gh_lines(
            "pr", "list",
            "--repo", repo,
            "--state", "all",
            "--limit", "50",
            "--json", "author,reviewRequests",
            "--jq", ".[] | .author.login, (.reviewRequests[].login // empty)"
        )
        users = sorted(set(lines))
        print(f"Found {len(users)} recent users: {', '.join(users)}")
        return users
    except Exception as e:
        print(f"::warning::Failed to list recent users: {e}")
        return []


def get_user_email(username: str, repo: Optional[str] = None) -> Optional[str]:
    """Get the email for a GitHub user.

    Checks the public profile first. If that's missing and a repo is provided,
    checks recent commits by that user in the repo.
    """
    # 1. Try public profile
    data = gh_json("api", f"users/{username}")
    email = data.get("email")
    if email:
        return email

    # 2. Try recent commits in the repo
    if repo:
        try:
            commits = gh_json(
                "api",
                f"repos/{repo}/commits",
                "-q",
                f'[.[] | select(.author.login == "{username}") | .commit.author.email] | first',
            )
            if commits and isinstance(commits, str) and "@" in commits and "noreply.github.com" not in commits:
                return commits
        except Exception:
            pass

    return None


# ---------------------------------------------------------------------------
# Slack API helpers
# ---------------------------------------------------------------------------


def slack_post_message(
    token: str, channel: str, text: str, thread_ts: Optional[str] = None
) -> dict:
    """Post a message to Slack via chat.postMessage."""
    payload: dict[str, str] = {"channel": channel, "text": text}
    if thread_ts:
        payload["thread_ts"] = thread_ts

    req = urllib.request.Request(
        "https://slack.com/api/chat.postMessage",
        data=json.dumps(payload).encode(),
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
        },
    )
    with urllib.request.urlopen(req) as resp:
        result = json.loads(resp.read())

    if not result.get("ok"):
        raise RuntimeError(f"Slack chat.postMessage failed: {result.get('error')}")
    return result


def slack_lookup_email(token: str, email: str) -> Optional[str]:
    """Look up a Slack user ID by email, or return None."""
    params = urllib.parse.urlencode({"email": email})
    req = urllib.request.Request(
        f"https://slack.com/api/users.lookupByEmail?{params}",
        headers={"Authorization": f"Bearer {token}"},
    )
    with urllib.request.urlopen(req) as resp:
        result = json.loads(resp.read())

    if result.get("ok"):
        return result["user"]["id"]
    return None


# ---------------------------------------------------------------------------
# Staleness logic (pure, no I/O)
# ---------------------------------------------------------------------------


def find_stale_reviews(
    prs: list[dict],
    get_review_dates: Callable[[int], dict[str, str]],
    now: Optional[datetime] = None,
    threshold: timedelta = timedelta(hours=10),
) -> list[StaleReview]:
    """Find reviews that have been pending longer than threshold.

    Args:
        prs: List of PR dicts with keys: number, title, url, author, reviewRequests.
        get_review_dates: Callable taking a PR number, returning {login: iso_timestamp}.
        now: Reference time (defaults to utcnow).
        threshold: How long before a review is considered stale.

    Returns:
        List of StaleReview, sorted by (reviewer, pr_number).
    """
    if now is None:
        now = datetime.now(timezone.utc)

    results: list[StaleReview] = []

    for pr in prs:
        # Skip draft PRs
        if pr.get("isDraft"):
            continue

        # Extract individual reviewers (skip teams)
        reviewers = [rr["login"] for rr in pr["reviewRequests"] if rr.get("login")]
        if not reviewers:
            continue

        review_dates = get_review_dates(pr["number"])
        if not review_dates:
            continue

        author = (
            pr["author"]["login"] if isinstance(pr["author"], dict) else pr["author"]
        )

        for reviewer in reviewers:
            ts_str = review_dates.get(reviewer)
            if not ts_str:
                continue

            requested_at = parse_iso(ts_str)
            age = now - requested_at
            if age < threshold:
                continue

            results.append(
                StaleReview(
                    reviewer=reviewer,
                    pr_number=pr["number"],
                    title=pr["title"],
                    url=pr["url"],
                    author=author,
                    requested_iso=ts_str,
                )
            )

    results.sort(key=lambda r: (r.reviewer, r.pr_number))
    return results


def review_verdict(pr: dict) -> Optional[str]:
    """The PR's review verdict: "APPROVED", "CHANGES_REQUESTED", or None.

    `reviewDecision` is GitHub's verdict where a review requirement applies to
    the PR, and is null otherwise. Without it, any reviewer's latest review
    requesting changes outweighs an approval. Comment-only reviews give no verdict.
    """
    verdicts = ("CHANGES_REQUESTED", "APPROVED")
    decision = pr.get("reviewDecision")
    if decision:
        return decision if decision in verdicts else None
    states = pr["latestReviewStates"]
    return next((v for v in verdicts if v in states), None)


_PASSING_CHECK_CONCLUSIONS = {"SUCCESS", "NEUTRAL", "SKIPPED"}


def ci_passed(checks: list[dict]) -> bool:
    """Whether the latest run of every check on the head commit passed.

    A re-run leaves the earlier run's result in the rollup beside the new one, so
    each check name is judged by its most recent run rather than by the rollup's
    aggregate state. Review approval is not a check context and plays no part.
    A commit with no checks has not passed CI.
    """
    latest: dict[tuple[str, str], tuple[str, bool]] = {}
    for c in checks:
        if c["__typename"] == "CheckRun":
            key = ("check", c["name"])
            started = c.get("startedAt") or ""
            ok = c["status"] == "COMPLETED" and c["conclusion"] in _PASSING_CHECK_CONCLUSIONS
        else:
            key = ("status", c["context"])
            started = c.get("createdAt") or ""
            ok = c["state"] == "SUCCESS"
        if key not in latest or started >= latest[key][0]:
            latest[key] = (started, ok)
    return bool(latest) and all(ok for _, ok in latest.values())


def find_general_review_prs(
    prs: list[dict],
    now: Optional[datetime] = None,
    threshold: timedelta = timedelta(hours=24),
) -> list[list[GeneralReviewPr]]:
    """Find PRs waiting on general review: non-draft, neither approved nor with
    changes requested, passing CI, no individual reviewer requested, and open at
    least `threshold`.

    A PR with an individual reviewer requested belongs to that reviewer's
    reminder (`find_stale_reviews`) and is excluded here.

    Open time is the last ready-for-review event, or creation for a PR that was
    never a draft. A stack is the chain of open PRs linked by base branch to head
    branch, drafts included, so a stack whose middle member does not qualify still
    reports its qualifying members together.

    Returns groups: each stack's qualifying members bottom first, and each
    unstacked PR alone. Groups are ordered by their earliest open time.
    """
    if now is None:
        now = datetime.now(timezone.utc)

    by_head = {pr["headRefName"]: pr for pr in prs}

    def below(pr: dict) -> list[dict]:
        """The open PRs under `pr` in its stack, nearest first."""
        chain: list[dict] = []
        seen = {pr["number"]}
        while pr["baseRefName"] in by_head:
            pr = by_head[pr["baseRefName"]]
            if pr["number"] in seen:  # a base cycle has no bottom
                break
            seen.add(pr["number"])
            chain.append(pr)
        return chain

    groups: dict[int, list[GeneralReviewPr]] = {}
    order: dict[int, int] = {}
    for pr in prs:
        if pr.get("isDraft") or pr["requestedReviewers"] or review_verdict(pr):
            continue
        opened_iso = pr.get("readyForReviewAt") or pr["createdAt"]
        if now - parse_iso(opened_iso) < threshold:
            continue
        if not ci_passed(pr["checks"]):
            continue
        chain = below(pr)
        root = chain[-1]["number"] if chain else pr["number"]
        order[pr["number"]] = len(chain)
        groups.setdefault(root, []).append(GeneralReviewPr(
            pr_number=pr["number"],
            title=pr["title"],
            url=pr["url"],
            author=pr["author"],
            base=pr["baseRefName"],
            head=pr["headRefName"],
            opened_iso=opened_iso,
            last_action_iso=pr["updatedAt"],
        ))

    result = [sorted(g, key=lambda p: order[p.pr_number]) for g in groups.values()]
    result.sort(key=lambda g: (min(p.opened_iso for p in g), g[0].pr_number))
    return result


# ---------------------------------------------------------------------------
# Slack formatting helpers
# ---------------------------------------------------------------------------


def format_mention(reviewer: str, usermap: dict[str, str]) -> str:
    """Format a reviewer as a Slack mention."""
    slack_id = usermap.get(reviewer)
    if slack_id:
        return f"<@{slack_id}>"
    return f"@{reviewer} _(GitHub)_"


def slack_escape(text: str) -> str:
    """Escape the three characters Slack's mrkdwn treats as control characters."""
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


_LINK_TEXT_LIMIT = 40


def format_pr_link(url: str, pr_number: int, title: str) -> str:
    """A Slack link to a PR, its text cut to `_LINK_TEXT_LIMIT` characters plus "..."."""
    text = f"#{pr_number}: {title}"
    if len(text) > _LINK_TEXT_LIMIT:
        text = text[:_LINK_TEXT_LIMIT].rstrip() + "..."
    return f"<{url}|{slack_escape(text)}>"


def format_duration(delta: timedelta) -> str:
    """Render a duration as days to one decimal from 24h, else as hours rounded up.

    Under an hour renders "<1h", unescaped; `format_pr_line` escapes it.
    """
    hours = delta.total_seconds() / 3600
    if hours >= 24:
        return f"{hours / 24:.1f}d"
    if hours < 1:
        return "<1h"
    return f"~{math.ceil(hours)}h"


def format_pr_line(url: str, pr_number: int, title: str, author: str, times: str,
                   marker: str = "\u2022") -> str:
    """A PR list item led by `marker`. Authors are named, never mentioned."""
    return f"{marker} {format_pr_link(url, pr_number, title)} \u2014 by *{author}*, {slack_escape(times)}"


def _general_review_line(p: GeneralReviewPr, now: datetime, marker: str = "\u2022") -> str:
    return format_pr_line(
        p.url, p.pr_number, p.title, p.author,
        f"open {format_duration(now - parse_iso(p.opened_iso))}, "
        f"last action {format_duration(now - parse_iso(p.last_action_iso))} ago",
        marker,
    )


# Open-time buckets, oldest first: (header, minimum age of the group's oldest PR).
_OPEN_BUCKETS = [
    ("Open >1w", timedelta(weeks=1)),
    ("Open <1w", timedelta(days=2)),
    ("Open <2d", timedelta(0)),
]


def build_general_review_section(groups: list[list[GeneralReviewPr]], now: datetime) -> str:
    """Build the "Waiting on General Review" section.

    Groups fall into the open-time bucket of their oldest PR, and keep the
    oldest-first order `find_general_review_prs` gives them. Each stack is its
    own numbered list, bottom first, under a header; consecutive unstacked PRs share one list.
    """
    buckets: dict[str, list[list[GeneralReviewPr]]] = {}
    for group in groups:
        age = now - min(parse_iso(p.opened_iso) for p in group)
        header = next(h for h, floor in _OPEN_BUCKETS if age >= floor)
        buckets.setdefault(header, []).append(group)

    blocks = ["*Waiting on General Review*"]
    for header, _ in _OPEN_BUCKETS:
        if header not in buckets:
            continue
        lists: list[list[str]] = []
        singles: Optional[list[str]] = None
        for group in buckets[header]:
            if len(group) == 1:
                if singles is None:
                    singles = []
                    lists.append(singles)
                singles.append(_general_review_line(group[0], now))
            else:
                singles = None
                lists.append([f"_Stack onto_ `{group[0].base}`"]
                             + [_general_review_line(p, now, f"{i}.") for i, p in enumerate(group, 1)])
        lists[0].insert(0, f"*{slack_escape(header)}*")
        blocks.extend("\n".join(lines) for lines in lists)
    return "\n\n".join(blocks)


def build_thread_body(
    reviews: list[StaleReview],
    usermap: dict[str, str],
    general_review: Optional[list[list[GeneralReviewPr]]] = None,
    now: Optional[datetime] = None,
) -> str:
    """Build the threaded reply body: the "Waiting on General Review" section, then reviewer reminders."""
    if now is None:
        now = datetime.now(timezone.utc)
    sections: list[str] = []
    if general_review:
        sections.append(build_general_review_section(general_review, now))
        if reviews:
            sections.append("")
    current_reviewer = None

    for r in reviews:
        if r.reviewer != current_reviewer:
            mention = format_mention(r.reviewer, usermap)
            sections.append(f"*{mention}*")
            current_reviewer = r.reviewer
        sections.append(format_pr_line(
            r.url, r.pr_number, r.title, r.author,
            f"review requested {format_duration(now - parse_iso(r.requested_iso))} ago",
        ))

    return "\n".join(sections)

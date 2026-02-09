"""Shared module for the stale PR review reminder system.

Contains dataclasses, gh CLI wrappers, Slack API helpers, and staleness logic.
All dependencies are Python stdlib only.
"""

import json
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
    requested_date: str  # human-readable, e.g. "Feb 03, 2026"
    requested_iso: str  # original ISO timestamp

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "StaleReview":
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
    """List open PRs that have at least one review request (individual user)."""
    lines = gh_lines(
        "pr",
        "list",
        "--repo",
        repo,
        "--state",
        "open",
        "--json",
        "number,title,url,author,reviewRequests",
        "--jq",
        ".[] | select(.reviewRequests | length > 0)",
    )
    return [json.loads(line) for line in lines]


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
    lines = gh_lines(
        "api", f"repos/{repo}/collaborators", "--paginate", "--jq", ".[].login"
    )
    return sorted(set(lines))


def get_user_email(username: str) -> Optional[str]:
    """Get the public email for a GitHub user, or None."""
    data = gh_json("api", f"users/{username}")
    return data.get("email") or None


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
    threshold: timedelta = timedelta(hours=24),
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
                    requested_date=requested_at.strftime("%b %d, %Y"),
                    requested_iso=ts_str,
                )
            )

    results.sort(key=lambda r: (r.reviewer, r.pr_number))
    return results


# ---------------------------------------------------------------------------
# Slack formatting helpers
# ---------------------------------------------------------------------------


def format_mention(reviewer: str, usermap: dict[str, str]) -> str:
    """Format a reviewer as a Slack mention."""
    slack_id = usermap.get(reviewer)
    if slack_id:
        return f"<@{slack_id}>"
    return f"@{reviewer} _(GitHub)_"


def build_thread_body(reviews: list[StaleReview], usermap: dict[str, str]) -> str:
    """Build the threaded reply body, grouped by reviewer."""
    sections: list[str] = []
    current_reviewer = None

    for r in reviews:
        if r.reviewer != current_reviewer:
            mention = format_mention(r.reviewer, usermap)
            sections.append(f"*{mention}*")
            current_reviewer = r.reviewer
        sections.append(
            f"\u2022 <{r.url}|#{r.pr_number}: {r.title}> \u2014 by *{r.author}*, "
            f"review requested {r.requested_date}"
        )

    return "\n".join(sections)

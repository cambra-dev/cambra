"""Write the GitHub half of the run's history: every simplify PR and what humans decided on it.

    python3 -I history.py <out-file>

Reads every PR whose head branch starts `simplify-agent/`, in any state, and writes a Markdown
digest with five sections:

- merge rate per category;
- open PRs;
- PRs a human closed without merging, each with its closing comment as the reason. These are
  permanent history: a candidate matching one is never re-proposed unless its cited code has
  changed;
- PRs settle-drafts.sh closed for a CI failure in the last `CI_HISTORY_DAYS` days. Its closing
  comment starts with `CI_CLOSE_PREFIX`. These are not a human's decision, so they count toward
  neither the permanent history nor the merge rate;
- review comments on the `MERGED_WITH_COMMENTS` most recently merged PRs, as guidance for the
  finders.

A PR's category comes from the last line of its body, which Step 8 writes as `Found by the daily
simplification run, <D>; category: <category>.` A PR without that line counts as `unknown`.
"""

import collections
import json
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone

REPO = "cambra-dev/cambra"
PREFIX = "simplify-agent/"
MERGED_WITH_COMMENTS = 20
CI_HISTORY_DAYS = 14
# Must match CLOSE_PREFIX in settle-drafts.sh.
CI_CLOSE_PREFIX = "Closed by the daily simplification run: CI failed"
# `gh pr close --comment` and the web UI's "Close with comment" post the comment just before
# the close event.
CLOSE_SLACK = timedelta(minutes=2)


def gh(*args):
    return json.loads(subprocess.run(["gh", *args], check=True, capture_output=True,
                                     text=True).stdout)


def when(stamp):
    return datetime.fromisoformat(stamp.replace("Z", "+00:00"))


def category(body):
    m = re.search(r"category: `?([a-z-]+)`?\.?\s*$", body or "")
    return m.group(1) if m else "unknown"


def quote(text):
    return "\n".join("  > " + line for line in text.strip().splitlines()) or "  > (empty)"


def closing_comment(n, closed_at):
    comments = gh("pr", "view", str(n), "--repo", REPO, "--json", "comments")["comments"]
    before = [c for c in comments if when(c["createdAt"]) <= when(closed_at) + CLOSE_SLACK]
    return before[-1] if before else None


def merged_comments(n, author):
    """What reviewers said on PR `n`; the author's own replies are left out."""
    inline = gh("api", "--paginate", "--slurp", f"repos/{REPO}/pulls/{n}/comments")
    reviews = gh("pr", "view", str(n), "--repo", REPO, "--json", "reviews")["reviews"]
    out = []
    for page in inline:
        for c in page:
            line = c.get("line") or c.get("original_line")
            where = f"{c['path']}:{line}" if line else c["path"]
            if c["user"]["login"] != author:
                out.append((f"`{where}` @{c['user']['login']}", c["body"]))
    for r in reviews:
        if r["body"].strip() and r["author"]["login"] != author:
            out.append((f"review @{r['author']['login']}", r["body"]))
    return out


def main(out_path):
    prs = [p for p in gh("pr", "list", "--repo", REPO, "--state", "all", "--limit", "1000",
                         "--search", f"head:{PREFIX}", "--json",
                         "number,title,url,headRefName,state,isDraft,body,closedAt,mergedAt,author")
           if p["headRefName"].startswith(PREFIX)]
    by_state = collections.defaultdict(list)
    for p in prs:
        state = p["state"]
        if state == "CLOSED":
            p["closing"] = closing_comment(p["number"], p["closedAt"])
            if p["closing"] and p["closing"]["body"].startswith(CI_CLOSE_PREFIX):
                state = "CI_FAILED"
        by_state[state].append(p)

    lines = [f"# Simplify PR history, {len(prs)} PRs", ""]

    lines += ["## Merge rate by category", "",
              "| category | merged | closed by a human | closed: CI failed | open | merge rate |",
              "|---|---|---|---|---|---|"]
    counts = collections.defaultdict(collections.Counter)
    for state, group in by_state.items():
        for p in group:
            counts[category(p["body"])][state] += 1
    for cat, c in sorted(counts.items()):
        decided = c["MERGED"] + c["CLOSED"]
        rate = f"{100 * c['MERGED'] // decided}%" if decided else "-"
        lines.append(f"| {cat} | {c['MERGED']} | {c['CLOSED']} | {c['CI_FAILED']} | {c['OPEN']} "
                     f"| {rate} |")

    lines += ["", "## Open", ""]
    for p in by_state["OPEN"]:
        draft = "draft" if p["isDraft"] else "ready for review"
        lines.append(f"- [#{p['number']}]({p['url']}) {p['title']} (`{p['headRefName']}`, "
                     f"{category(p['body'])}, {draft})")

    lines += ["", "## Closed without merging", ""]
    for p in by_state["CLOSED"]:
        c = p["closing"]
        reason = (f"closing comment by @{c['author']['login']}:\n{quote(c['body'])}" if c
                  else "closed without a comment")
        lines.append(f"- [#{p['number']}]({p['url']}) {p['title']} ({category(p['body'])}, "
                     f"closed {p['closedAt'][:10]}): {reason}")

    lines += ["", f"## Closed for a CI failure in the last {CI_HISTORY_DAYS} days", ""]
    cutoff = datetime.now(timezone.utc) - timedelta(days=CI_HISTORY_DAYS)
    for p in by_state["CI_FAILED"]:
        if when(p["closedAt"]) >= cutoff:
            lines.append(f"- [#{p['number']}]({p['url']}) {p['title']} ({category(p['body'])}, "
                         f"closed {p['closedAt'][:10]}): {p['closing']['body'].strip()}")

    lines += ["", f"## Review comments on the {MERGED_WITH_COMMENTS} most recently merged", ""]
    merged = sorted(by_state["MERGED"], key=lambda p: p["mergedAt"], reverse=True)
    for p in merged[:MERGED_WITH_COMMENTS]:
        comments = merged_comments(p["number"], p["author"]["login"])
        if not comments:
            continue
        lines += [f"### [#{p['number']}]({p['url']}) {p['title']} ({category(p['body'])})", ""]
        for who, body in comments:
            lines.append(f"- {who}:\n{quote(body)}")
        lines.append("")

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines).rstrip() + "\n")
    print(f"history: {out_path}")


if __name__ == "__main__":
    main(sys.argv[1])

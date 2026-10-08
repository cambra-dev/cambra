#!/usr/bin/env python3
"""Report, or wait for, the CI verdict of one or more PRs at their head SHAs.

    ci_verdict.py 293 273 306           # one line per PR, now
    ci_verdict.py --wait 293 273 306    # poll until every PR has a verdict

Exit status is 0 when every PR passed and 1 otherwise.

A PR's head SHA routinely carries two `pull_request` runs of `ci.yml`. When one
push moves both a stacked PR's head and its base, and the base move is a
force-push, GitHub starts a run for each, both at the new head SHA. The workflow's
concurrency group cancels whichever entered the group first, and that run's
`check` job reports FAILURE. Which of the two is cancelled is not predictable
from the outside: the two are created within a second of each other, and the
cancelled one can carry either the lower or the higher run id. So "the latest
run" is not a verdict, and neither is `gh pr checks` or `statusCheckRollup`,
which union the two.

The verdict here reads every run at the head SHA and discounts a cancelled run
only when another run at that SHA was not cancelled. A head SHA whose runs were
all cancelled was checked by nothing, and reads as `cancelled`, never as a pass.

Re-running a cancelled duplicate while its sibling is in flight cancels the
sibling, since the re-run enters the same concurrency group. Re-run only a SHA
this script reports as `cancelled`.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import dataclass

WORKFLOW = "ci.yml"


@dataclass(frozen=True)
class Run:
    id: int
    status: str
    # Empty until the run completes.
    conclusion: str
    url: str


@dataclass(frozen=True)
class Verdict:
    # One of: none, pending, pass, fail, cancelled.
    state: str
    # The run the state was read from; None for `none` and `pending`.
    run: Run | None = None

    @property
    def terminal(self) -> bool:
        return self.state in ("pass", "fail", "cancelled")


def verdict(runs: list[Run]) -> Verdict:
    """The CI verdict of one head SHA, from every `ci.yml` run at that SHA."""
    if not runs:
        return Verdict("none")
    if any(r.status != "completed" for r in runs):
        return Verdict("pending")
    checked = [r for r in runs if r.conclusion != "cancelled"]
    if not checked:
        return Verdict("cancelled", max(runs, key=lambda r: r.id))
    failed = [r for r in checked if r.conclusion != "success"]
    if failed:
        return Verdict("fail", failed[0])
    return Verdict("pass", checked[0])


def gh_api(path: str) -> dict:
    out = subprocess.run(
        ["gh", "api", path], check=True, capture_output=True, text=True
    ).stdout
    return json.loads(out)


@dataclass(frozen=True)
class PrState:
    number: int
    sha: str
    mergeable_state: str
    verdict: Verdict


def read_pr(number: int) -> PrState:
    pr = gh_api(f"repos/{{owner}}/{{repo}}/pulls/{number}")
    sha = pr["head"]["sha"]
    page = gh_api(
        f"repos/{{owner}}/{{repo}}/actions/workflows/{WORKFLOW}/runs"
        f"?head_sha={sha}&event=pull_request&per_page=100"
    )
    runs = [
        Run(r["id"], r["status"], r["conclusion"] or "", r["html_url"])
        for r in page["workflow_runs"]
    ]
    return PrState(number, sha, pr.get("mergeable_state") or "", verdict(runs))


def describe(pr: PrState) -> str:
    line = f"#{pr.number} {pr.sha[:10]} {pr.verdict.state}"
    if pr.verdict.run is not None:
        line += f" {pr.verdict.run.url}"
    if pr.verdict.state == "none" and pr.mergeable_state == "dirty":
        # GitHub runs no `pull_request` workflow for a PR that does not merge
        # cleanly, and judges every member of a GitHub stack against `main`.
        line += " (mergeable_state dirty: rebase the stack onto main)"
    if pr.verdict.state == "cancelled":
        line += f" (nothing checked this SHA: gh run rerun {pr.verdict.run.id})"
    return line


def main() -> int:
    parser = argparse.ArgumentParser(
        description="CI verdict of PRs at their head SHAs, ignoring cancelled duplicates."
    )
    parser.add_argument("prs", nargs="+", type=int, metavar="PR")
    parser.add_argument(
        "--wait", action="store_true", help="poll until every PR has a verdict"
    )
    parser.add_argument("--interval", type=int, default=30, help="seconds between polls")
    parser.add_argument(
        "--no-run-timeout",
        type=int,
        default=300,
        help="seconds to wait for a head SHA's first run before reporting `none`",
    )
    args = parser.parse_args()

    started = time.monotonic()
    while True:
        # The head SHA is re-read every poll, so a push made while waiting is
        # followed rather than judged at the SHA it replaced.
        prs = [read_pr(n) for n in args.prs]
        waited_out = time.monotonic() - started >= args.no_run_timeout
        done = all(
            p.verdict.terminal or (p.verdict.state == "none" and waited_out)
            for p in prs
        )
        if not args.wait or done:
            break
        waiting = [f"#{p.number} {p.verdict.state}" for p in prs if not p.verdict.terminal]
        print("waiting: " + ", ".join(waiting), file=sys.stderr, flush=True)
        time.sleep(args.interval)

    for p in prs:
        print(describe(p))
    return 0 if all(p.verdict.state == "pass" for p in prs) else 1


if __name__ == "__main__":
    sys.exit(main())

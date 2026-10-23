"""Settle earlier runs' simplify PRs by their GitHub CI result, one stack at a time.

    python3 -I settle_drafts.py <run-dir> [--dry-run]

The run gates locally with `./ci.sh fast`, and GitHub CI runs the full gate on each PR. A run
pushes its PRs as one GitHub stack, so each PR's branch holds every commit below it. Each stack's
members are walked bottom to top:

- a merged member is skipped;
- a member that is closed, and whose commits an open member above still carries, is dropped;
- an open member whose `check` check failed is closed with a comment naming the failed jobs, and
  dropped.

An open member is judged by `check` alone: it is the one required check, and it already accounts
for skipped jobs. The first open member whose `check` has not passed ends the walk's CI verdicts,
and so does the first drop: every member above carries its commits, so their results say nothing
about their own changes. Closed members above either are still dropped. No member is marked ready
for review; a human promotes a simplify PR.

When open members remain above a drop, the stack is repaired:

1. The dropped members' commits are abandoned in the jj repo, which rebases the members above onto
   what the dropped ones sat on.
2. A rebased member that conflicts or has no changes left is closed with a comment starting
   `RUN_CLOSE_PREFIX`, and its commits are abandoned in turn. Pushing an empty member would put
   its head at its base, and GitHub then marks the PR merged.
3. The rebased members are pushed, and the open members are re-formed into one stack: the old
   stack is unstacked on GitHub, which leaves any merged member behind in it, and the open members
   are linked again.

Settling a stack stops at the first jj, `gh stack` or `gh pr close` call that fails, prints
`repair skipped` with the stack to re-form by hand, and goes on to the next stack.

A PR outside any stack is settled as a stack of one. Prints one line per PR it changes;
`--dry-run` prints what it would do and changes nothing.
"""

import json
import os
import shlex
import subprocess
import sys
from dataclasses import dataclass, field

REPO_SLUG = "cambra-dev/cambra"
REQUIRED_CHECK = "check"
PREFIX = "simplify-agent/"
# Every comment this script closes a PR with starts with this; history.py reads it to tell the
# run's decision from a human's.
RUN_CLOSE_PREFIX = "Closed by the daily simplification run:"
HERE = os.path.dirname(os.path.abspath(__file__))

STACK_QUERY = """
query($n: Int!) { repository(owner: "cambra-dev", name: "cambra") { pullRequest(number: $n) {
  stack { number entries(first: 50) { nodes { position pullRequest {
    number url state isDraft headRefName headRefOid } } } } } } }
"""


@dataclass
class Plan:
    close_ci: list = field(default_factory=list)   # (member, failed job names)
    drops: list = field(default_factory=list)      # closed or CI-failed members, bottom first
    rebase: list = field(default_factory=list)     # open members above the lowest drop


def plan(members, verdicts, contains):
    """Decide one stack. `members` are sorted bottom first; `verdicts[n]` is `("pass",)`,
    `("pending",)`, `("none",)` or `("fail", names)`; `contains(lower_oid, upper_oid)` says whether
    the upper head carries the lower commit."""
    out = Plan()
    opens = [m for m in members if m["state"] == "OPEN"]
    judging = True
    for m in members:
        if m["state"] == "MERGED":
            continue
        above = [o for o in opens if o["position"] > m["position"]]
        if m["state"] == "CLOSED":
            if any(contains(m["headRefOid"], o["headRefOid"]) for o in above):
                out.drops.append(m)
                judging = False
            continue
        if not judging:
            continue
        v = verdicts[m["number"]]
        if v[0] == "fail":
            out.close_ci.append((m, v[1]))
            out.drops.append(m)
        # Every member above carries this one's commits, so their results say nothing about their
        # own changes until this one has passed.
        judging = v[0] == "pass"
    if out.drops:
        lowest = out.drops[0]["position"]
        out.rebase = [o for o in opens if o["position"] > lowest and o not in out.drops]
    return out


class RepairSkipped(Exception):
    """A step of a stack repair failed; the stack is left for a human to re-form."""


def run(*args, check=True):
    return subprocess.run(args, check=check, capture_output=True, text=True)


def must(*args):
    """Runs a repair step, raising `RepairSkipped` with its error when it fails."""
    r = run(*args, check=False)
    if r.returncode != 0:
        cmd = " ".join([os.path.basename(args[0]), *args[1:]])
        raise RepairSkipped(f"`{cmd}` failed: {r.stderr.strip()}")
    return r


def gh_json(*args):
    return json.loads(run("gh", *args).stdout)


def paths():
    out = run(os.path.join(HERE, "workspace.sh"), "paths").stdout
    return {k: shlex.split(v)[0] for k, v in (line.split("=", 1) for line in out.splitlines())}


class Repo:
    def __init__(self, repo, dry):
        self.jj = ["jj", "-R", repo, "--ignore-working-copy",
                   "--config", "ui.paginate=never"]
        self.dry = dry

    def must_ids(self, revset):
        out = must(*self.jj, "log", "-r", revset, "--no-graph", "-T", 'commit_id ++ "\\n"')
        return out.stdout.split()

    def ids(self, revset):
        """`must_ids`, with `None` for a revset jj cannot resolve."""
        try:
            return self.must_ids(revset)
        except RepairSkipped:
            return None

    def contains(self, lower, upper):
        found = self.ids(f"{lower} & ::{upper}")
        return found is None or bool(found)  # an unknown commit cannot be ruled out

    def write(self, *args):
        must(*self.jj, *args)


def stacks():
    """Every stack holding an open simplify PR, bottom first; a PR outside a stack is its own."""
    numbers = [p["number"] for p in gh_json(
        "pr", "list", "--repo", REPO_SLUG, "--state", "open", "--search", f"head:{PREFIX}",
        "--limit", "200", "--json", "number,headRefName")
        if p["headRefName"].startswith(PREFIX)]
    seen, out = set(), []
    for n in sorted(numbers):
        if n in seen:
            continue
        data = gh_json("api", "graphql", "-f", f"query={STACK_QUERY}", "-F", f"n={n}")
        stack = data["data"]["repository"]["pullRequest"]["stack"]
        if stack:
            members = sorted(({"position": e["position"], **e["pullRequest"]}
                              for e in stack["entries"]["nodes"]), key=lambda m: m["position"])
            out.append((stack["number"], members))
        else:
            pr = gh_json("pr", "view", str(n), "--repo", REPO_SLUG, "--json",
                         "number,url,state,isDraft,headRefName,headRefOid")
            out.append((None, [{"position": 1, **pr}]))
        seen.update(m["number"] for m in out[-1][1])
    return out


def verdict(n):
    """The PR's `REQUIRED_CHECK` result. A cancelled or missing one is `none`, so a run that
    never finished neither passes nor fails."""
    r = run("gh", "pr", "checks", str(n), "--repo", REPO_SLUG, "--json", "name,bucket",
            check=False)
    checks = json.loads(r.stdout) if r.stdout.strip() else []
    bucket = next((c["bucket"] for c in checks if c["name"] == REQUIRED_CHECK), None)
    if bucket == "fail":
        # `check` fails on a failed or cancelled gate; name those gates rather than `check`.
        gates = [c["name"] for c in checks
                 if c["bucket"] in ("fail", "cancel") and c["name"] != REQUIRED_CHECK]
        return ("fail", ", ".join(gates) or REQUIRED_CHECK)
    return (bucket,) if bucket in ("pass", "pending") else ("none",)


def close(n, reason, dry):
    if dry:
        print(f"would close #{n}: {reason}")
    else:
        must("gh", "pr", "close", str(n), "--repo", REPO_SLUG, "--comment",
             f"{RUN_CLOSE_PREFIX} {reason}.")
        print(f"closed #{n}: {reason}")


def own_commits(member, below, merged):
    """The member's own commits: what its head holds beyond main and every member below it."""
    roots = " | ".join(["main@origin", *below, *merged])
    return f"({roots})..{member}"


def repair(repo, run_dir, stack_number, members, p):
    dropped = ", ".join(f"#{d['number']}" for d in p.drops)
    if repo.dry:
        print(f"would drop {dropped} from its stack, rebase "
              f"{' '.join('#%d' % m['number'] for m in p.rebase)} and re-form the stack")
        return
    merged = [m["headRefOid"] for m in members if m["state"] == "MERGED"]
    drop_ids = []
    for d in p.drops:
        below = [m["headRefOid"] for m in members if m["position"] < d["position"]]
        drop_ids += repo.must_ids(own_commits(d["headRefOid"], below, merged))
    repo.write("abandon", *drop_ids)

    # Rebased members follow their bookmarks. Close any that conflict or emptied, bottom first;
    # abandoning one rebases the members above it again, so re-check from the start each time.
    kept = list(p.rebase)
    while True:
        bad = None
        for i, m in enumerate(kept):
            below = [k["headRefName"] for k in kept[:i]]
            below += [o["headRefOid"] for o in members
                      if o["state"] == "OPEN" and o["position"] < p.drops[0]["position"]]
            mine = own_commits(m["headRefName"], below, merged)
            if repo.must_ids(f"({mine}) & conflicts()"):
                bad = (m, mine, f"conflicts after {dropped} below it was dropped")
            elif not repo.must_ids(f"({mine}) ~ empty()"):
                bad = (m, mine, f"no changes left after {dropped} below it was dropped")
            if bad:
                break
        if not bad:
            break
        m, mine, reason = bad
        close(m["number"], reason, False)
        repo.write("abandon", *repo.must_ids(mine))
        kept.remove(m)

    if kept:
        args = [a for m in kept for a in ("-b", m["headRefName"])]
        repo.write("git", "push", *args)
        print(f"rebased {' '.join('#%d' % m['number'] for m in kept)} past {dropped}")
    closed = {d["number"] for d in p.drops} | {m["number"] for m in p.rebase if m not in kept}
    remaining = [m for m in members if m["state"] == "OPEN" and m["number"] not in closed]
    restack(run_dir, stack_number, remaining)


def restack(run_dir, stack_number, remaining):
    stack = [os.path.join(HERE, "gh-stack.sh"), run_dir]
    if stack_number is not None:
        # Unstacking on GitHub releases the open members even after one has merged; the merged
        # ones stay behind in the old stack.
        must(*stack, "unstack", str(stack_number))
    if len(remaining) >= 2:
        must(*stack, "link", *(m["url"] for m in remaining))
    elif remaining:
        must("gh", "api", "-X", "PATCH", f"repos/{REPO_SLUG}/pulls/{remaining[0]['number']}",
             "-f", "base=main")
    print(f"re-formed stack: {' '.join('#%d' % m['number'] for m in remaining) or 'empty'}")


def main(run_dir, dry):
    run(os.path.join(HERE, "workspace.sh"), "fetch")
    repo = Repo(paths()["REPO"], dry)
    for stack_number, members in stacks():
        opens = [m for m in members if m["state"] == "OPEN"]
        verdicts = {m["number"]: verdict(m["number"]) for m in opens}
        p = plan(members, verdicts, repo.contains)
        try:
            # The repair drops the members closed here, so it stops if one of them stays open.
            for m, names in p.close_ci:
                close(m["number"], f"CI failed ({names})", dry)
            if p.rebase:
                repair(repo, run_dir, stack_number, members, p)
        except RepairSkipped as e:
            which = f"stack {stack_number}" if stack_number else f"#{members[0]['number']}"
            print(f"repair skipped: {e}; re-form {which} by hand")


if __name__ == "__main__":
    main(sys.argv[1], "--dry-run" in sys.argv[2:])

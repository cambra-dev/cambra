"""Settle earlier runs' simplify PRs by their GitHub CI result, one stack at a time.

    python3 -I settle_drafts.py <run-dir> [--dry-run]

The run gates locally with `./ci.sh fast`, and GitHub CI runs the full gate on each PR. A run
pushes its PRs as one GitHub stack, so each PR's branch holds every commit below it. Each stack's
members are walked bottom to top:

- a merged member is skipped;
- a member that is closed, and whose commits an open member above still carries, is dropped;
- an open member whose checks have all finished, with at least one failed, is closed with a
  comment naming the failed checks, and dropped;
- an open draft whose checks have all finished, at least one passed and none failed, is marked
  ready for review.

The first drop ends the walk's CI verdicts: every member above carries the dropped commits, so its
result says nothing about its own change. When open members remain above a drop, the stack is
repaired:

1. The dropped members' commits are abandoned in the jj repo, which rebases the members above onto
   what the dropped ones sat on.
2. A rebased member that conflicts or has no changes left is closed with a comment starting
   `RUN_CLOSE_PREFIX`, and its commits are abandoned in turn. Pushing an empty member would put
   its head at its base, and GitHub then marks the PR merged.
3. The rebased members are pushed, and the open members are re-formed into one stack. The old
   stack is unstacked and the members linked again; once a member has merged, GitHub refuses the
   unstack, and `gh stack init` + `submit` re-forms it instead.

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
    close_ci: list = field(default_factory=list)   # (member, failed check names)
    ready: list = field(default_factory=list)
    drops: list = field(default_factory=list)      # closed or CI-failed members, bottom first
    rebase: list = field(default_factory=list)     # open members above the lowest drop


def plan(members, verdicts, contains):
    """Decide one stack. `members` are sorted bottom first; `verdicts[n]` is `("pass",)`,
    `("pending",)`, `("none",)` or `("fail", names)`; `contains(lower_oid, upper_oid)` says whether
    the upper head carries the lower commit."""
    out = Plan()
    opens = [m for m in members if m["state"] == "OPEN"]
    for m in members:
        if m["state"] == "MERGED":
            continue
        above = [o for o in opens if o["position"] > m["position"]]
        if m["state"] == "CLOSED":
            if any(contains(m["headRefOid"], o["headRefOid"]) for o in above):
                out.drops.append(m)
            continue
        if out.drops:
            continue
        v = verdicts[m["number"]]
        if v[0] == "fail":
            out.close_ci.append((m, v[1]))
            out.drops.append(m)
        elif v[0] == "pass" and m["isDraft"]:
            out.ready.append(m)
    if out.drops:
        lowest = out.drops[0]["position"]
        out.rebase = [o for o in opens if o["position"] > lowest and o not in out.drops]
    return out


def run(*args, check=True):
    return subprocess.run(args, check=check, capture_output=True, text=True)


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

    def ids(self, revset):
        r = run(*self.jj, "log", "-r", revset, "--no-graph", "-T", 'commit_id ++ "\\n"',
                check=False)
        return r.stdout.split() if r.returncode == 0 else None

    def contains(self, lower, upper):
        found = self.ids(f"{lower} & ::{upper}")
        return found is None or bool(found)  # an unknown commit cannot be ruled out

    def write(self, *args):
        run(*self.jj, *args)


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
    r = run("gh", "pr", "checks", str(n), "--repo", REPO_SLUG, "--json", "name,bucket",
            check=False)
    if not r.stdout.strip():
        return ("none",)
    checks = json.loads(r.stdout)
    if any(c["bucket"] == "pending" for c in checks):
        return ("pending",)
    failed = [c["name"] for c in checks if c["bucket"] == "fail"]
    if failed:
        return ("fail", ", ".join(failed))
    return ("pass",) if any(c["bucket"] == "pass" for c in checks) else ("none",)


def close(n, reason, dry):
    if dry:
        print(f"would close #{n}: {reason}")
    else:
        run("gh", "pr", "close", str(n), "--repo", REPO_SLUG, "--comment",
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
        ids = repo.ids(own_commits(d["headRefOid"], below, merged))
        if ids is None:
            print(f"repair skipped: the head of #{d['number']} is not in the jj repo; "
                  f"re-form stack {stack_number} by hand")
            return
        drop_ids += ids
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
            if repo.ids(f"({mine}) & conflicts()"):
                bad = (m, mine, f"conflicts after {dropped} below it was dropped")
            elif not repo.ids(f"({mine}) ~ empty()"):
                bad = (m, mine, f"no changes left after {dropped} below it was dropped")
            if bad:
                break
        if not bad:
            break
        m, mine, reason = bad
        close(m["number"], reason, False)
        repo.write("abandon", *repo.ids(mine))
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
    if stack_number is not None and run(*stack, "unstack", str(stack_number),
                                        check=False).returncode != 0:
        # A stack with a merged member cannot be unstacked; submit re-forms it from tracking.
        run(*stack, "checkout", str(remaining[0]["number"]))
        run(*stack, "unstack", "--local")
        run(*stack, "init", *(m["headRefName"] for m in remaining))
        run(*stack, "submit", "--auto")
    elif len(remaining) >= 2:
        run(*stack, "link", *(m["url"] for m in remaining))
    elif remaining:
        run("gh", "api", "-X", "PATCH", f"repos/{REPO_SLUG}/pulls/{remaining[0]['number']}",
            "-f", "base=main")
    print(f"re-formed stack: {' '.join('#%d' % m['number'] for m in remaining) or 'empty'}")


def main(run_dir, dry):
    run(os.path.join(HERE, "workspace.sh"), "fetch")
    repo = Repo(paths()["REPO"], dry)
    for stack_number, members in stacks():
        opens = [m for m in members if m["state"] == "OPEN"]
        verdicts = {m["number"]: verdict(m["number"]) for m in opens}
        p = plan(members, verdicts, repo.contains)
        for m, names in p.close_ci:
            close(m["number"], f"CI failed ({names})", dry)
        for m in p.ready:
            if dry:
                print(f"would mark ready #{m['number']}")
            else:
                run("gh", "pr", "ready", str(m["number"]), "--repo", REPO_SLUG)
                print(f"marked ready #{m['number']}")
        if p.rebase:
            repair(repo, run_dir, stack_number, members, p)


if __name__ == "__main__":
    main(sys.argv[1], "--dry-run" in sys.argv[2:])

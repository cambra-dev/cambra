"""Pass/fail test of settle_drafts.py: the per-stack plan, and the jj half of a stack repair.

    python3 -I test-settle-drafts.py

The plan cases need nothing. The repair cases build a scratch jj repo with a bare git remote,
stack three or four bookmarked commits on `main@origin`, and run `repair` with GitHub stubbed
out: closing a PR, pushing and re-forming the stack are recorded instead of sent. Touches no real
workspace, repo or PR.
"""

import importlib.util
import json
import os
import subprocess
import sys
import tempfile

spec = importlib.util.spec_from_file_location(
    "settle_drafts", os.path.join(os.path.dirname(os.path.abspath(__file__)), "settle_drafts.py"))
sd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sd)

failures = 0


def check(what, ok):
    global failures
    print(("PASS  " if ok else "FAIL  ") + what)
    failures += not ok


def member(n, pos, state="OPEN", draft=True, head=None):
    return {"number": n, "position": pos, "state": state, "isDraft": draft,
            "url": f"u{n}", "headRefName": f"b{n}", "headRefOid": head or f"oid{n}"}


def nums(ms):
    return [m["number"] for m in ms]


always = lambda lower, upper: True  # noqa: E731

# --- plan ---

ms = [member(1, 1), member(2, 2), member(3, 3)]
p = sd.plan(ms, {1: ("pass",), 2: ("pass",), 3: ("pending",)}, always)
check("an all-green stack needs no repair", not p.drops and not p.rebase and not p.close_ci)

p = sd.plan(ms, {1: ("pass",), 2: ("fail", "test"), 3: ("fail", "test")}, always)
check("only the lowest CI failure is closed", [m["number"] for m, _ in p.close_ci] == [2])
check("members above a failure are repaired, not judged", nums(p.rebase) == [3])

for unfinished in [("pending",), ("none",)]:
    p = sd.plan(ms, {1: unfinished, 2: ("fail", "test"), 3: ("pass",)}, always)
    check(f"a {unfinished[0]} member ends the verdicts; the failure above it stays open",
          not p.close_ci and not p.drops and not p.rebase)

p = sd.plan(ms, {1: ("pass",), 2: ("pass",), 3: ("fail", "test")}, always)
check("a failure at the top closes it with nothing to rebase",
      nums(p.drops) == [3] and not p.rebase)

ms = [member(1, 1, "MERGED"), member(2, 2, "CLOSED"), member(3, 3), member(4, 4, draft=False)]
p = sd.plan(ms, {3: ("pass",), 4: ("pass",)}, always)
check("a human-closed member carried above is dropped", nums(p.drops) == [2])
check("verdicts above a drop are ignored", nums(p.rebase) == [3, 4])

p = sd.plan(ms, {3: ("fail", "test"), 4: ("pass",)}, lambda lower, upper: False)
check("a closed member no open head carries is history, not a drop",
      nums(p.drops) == [3] and nums(p.rebase) == [4])

ms = [member(1, 1), member(2, 2, "CLOSED"), member(3, 3)]
p = sd.plan(ms, {1: ("pending",), 3: ("pass",)}, always)
check("a closed member above a pending one is still dropped",
      nums(p.drops) == [2] and nums(p.rebase) == [3])


# --- verdict ---

def verdict_of(checks):
    real = sd.run
    sd.run = lambda *a, check=True: subprocess.CompletedProcess(a, 0, json.dumps(checks), "")
    try:
        return sd.verdict(1)
    finally:
        sd.run = real


def c(name, bucket):
    return {"name": name, "bucket": bucket}


check("verdict: `check` passing passes, whatever the skipped gates",
      verdict_of([c("check", "pass"), c("test", "skipping")]) == ("pass",))
check("verdict: a cancelled run is no verdict",
      verdict_of([c("check", "cancel"), c("lint", "pass"), c("test", "cancel")]) == ("none",))
check("verdict: a failed `check` names the gates that failed or were cancelled",
      verdict_of([c("check", "fail"), c("test", "fail"), c("web", "cancel"), c("lint", "pass")])
      == ("fail", "test, web"))
check("verdict: `check` still running is pending",
      verdict_of([c("check", "pending"), c("test", "fail")]) == ("pending",))
check("verdict: no checks is no verdict", verdict_of([]) == ("none",))


def close_failing():
    real = sd.run
    sd.run = lambda *a, check=True: subprocess.CompletedProcess(a, 1, "", "HTTP 502")
    try:
        sd.close(1, "CI failed (test)", False)
        return False
    except sd.RepairSkipped:
        return True
    finally:
        sd.run = real


check("close: a failed `gh pr close` stops the repair", close_failing())


# --- repair ---

def sh(*args, cwd):
    return subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True).stdout


def scratch_repo(tmp, files):
    """main@origin, then one commit per (bookmark, path, text), each on the one before."""
    remote, repo = os.path.join(tmp, "remote.git"), os.path.join(tmp, "repo")
    sh("git", "init", "--quiet", "--bare", remote, cwd=tmp)
    sh("jj", "git", "init", repo, cwd=tmp)
    jj = ["jj", "--config", "user.name=t", "--config",
          "user.email=t@t"]
    sh(*jj, "git", "remote", "add", "origin", remote, cwd=repo)
    with open(os.path.join(repo, "base.txt"), "w") as f:
        f.write("base\n")
    sh(*jj, "describe", "-m", "base", cwd=repo)
    sh(*jj, "bookmark", "create", "main", "-r", "@", cwd=repo)
    for name, path, text in files:
        sh(*jj, "new", "-m", name, cwd=repo)
        with open(os.path.join(repo, path), "w") as f:
            f.write(text)
        sh(*jj, "bookmark", "create", name, "-r", "@", cwd=repo)
    sh(*jj, "new", cwd=repo)
    sh(*jj, "git", "push", *[a for n in ["main", *[f[0] for f in files]]
                             for a in ("--bookmark", n)], cwd=repo)
    heads = {n: sh(*jj, "log", "-r", n, "--no-graph", "-T", "commit_id", cwd=repo).strip()
             for n in ["main", *[f[0] for f in files]]}
    return repo, heads


def stub_github():
    events = []
    sd.close = lambda n, reason, dry: events.append(("close", n, reason))
    sd.restack = lambda run_dir, sn, remaining: events.append(("restack", nums(remaining)))
    return events


def stacked(heads, names, states=None):
    states = states or {}
    return [{**member(i + 1, i + 1, states.get(n, "OPEN"), head=heads[n]), "headRefName": n}
            for i, n in enumerate(names)]


def push_recorder(repo, pushed):
    real = repo.write

    def write(*args):
        if args[:2] == ("git", "push"):
            pushed.append([a for a in args[2:] if a != "-b"])
        else:
            real(*args)
    repo.write = write


with tempfile.TemporaryDirectory() as tmp:
    path, heads = scratch_repo(tmp, [("b1", "one.txt", "1\n"), ("b2", "two.txt", "2\n"),
                                     ("b3", "three.txt", "3\n")])
    events, pushed = stub_github(), []
    repo = sd.Repo(path, dry=False)
    push_recorder(repo, pushed)
    ms = stacked(heads, ["b1", "b2", "b3"], {"b1": "CLOSED"})
    p = sd.plan(ms, {2: ("pass",), 3: ("pass",)}, repo.contains)
    check("repair: the closed bottom is dropped", nums(p.drops) == [1])
    sd.repair(repo, tmp, None, ms, p)
    check("repair: the dropped commit leaves the stack",
          not repo.ids(f"{heads['b1']} & ::b3"))
    check("repair: the members above keep their own changes",
          len(repo.ids("main@origin..b3")) == 2)
    check("repair: the rebased members are pushed", pushed == [["b2", "b3"]])
    check("repair: the stack is re-formed from the open members",
          events == [("restack", [2, 3])])

with tempfile.TemporaryDirectory() as tmp:
    # b2 edits the file b1 creates, so dropping b1 conflicts b2; b3 is independent.
    path, heads = scratch_repo(tmp, [("b1", "one.txt", "1\n"), ("b2", "one.txt", "1 and 2\n"),
                                     ("b3", "three.txt", "3\n")])
    events, pushed = stub_github(), []
    repo = sd.Repo(path, dry=False)
    push_recorder(repo, pushed)
    ms = stacked(heads, ["b1", "b2", "b3"])
    p = sd.plan(ms, {1: ("fail", "test"), 2: ("fail", "test"), 3: ("fail", "test")},
                repo.contains)
    sd.repair(repo, tmp, None, ms, p)
    closed = [e[1] for e in events if e[0] == "close"]
    check("repair: a member that conflicts after the drop is closed", closed == [2])
    check("repair: the conflicted member's commit is abandoned too",
          len(repo.ids("main@origin..b3")) == 1 and not repo.ids("conflicts()"))
    check("repair: only the surviving member is pushed and re-stacked",
          pushed == [["b3"]] and events[-1] == ("restack", [3]))

with tempfile.TemporaryDirectory() as tmp:
    path, heads = scratch_repo(tmp, [("b1", "one.txt", "1\n"), ("b2", "two.txt", "2\n")])
    events, pushed = stub_github(), []
    repo = sd.Repo(path, dry=False)
    push_recorder(repo, pushed)
    ms = stacked(heads, ["b1", "b2"], {"b1": "CLOSED"})
    ms[1]["headRefName"] = "no-such-bookmark"
    p = sd.plan(ms, {2: ("pass",)}, repo.contains)
    try:
        sd.repair(repo, tmp, None, ms, p)
        skipped = False
    except sd.RepairSkipped:
        skipped = True
    check("repair: a revset jj cannot resolve stops the repair",
          skipped and not events and not pushed)

sys.exit(1 if failures else 0)

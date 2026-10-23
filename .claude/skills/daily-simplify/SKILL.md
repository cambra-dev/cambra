---
name: daily-simplify
description: Daily simplification sweep of the cambra repo. Finds small behaviour-preserving simplifications, attempts each in an isolated jj workspace, reviews each adversarially and at staff level, pushes survivors as draft PRs, and logs the run to the vault's automation/daily-simplify/outputs/. Use when someone runs /daily-simplify or asks for the daily simplification run.
argument-hint: "[triage-only]"
---

# Daily simplification run

One run turns the cambra repo into a short list of small, verified simplification PRs plus a log
of everything that was flagged and why it did or did not ship. The run is unattended once it
starts. Do not stop to ask questions. Record each open question in the log under "Questions",
and abandon a candidate that depends on its answer.

## Modes

This run's argument: `$ARGUMENTS`. Empty selects the full run.

| invocation | runs | writes |
|---|---|---|
| `/daily-simplify` | every step | draft PRs; the log in `LOGDIR` |
| `/daily-simplify triage-only` | Steps 0–4, then Step 9 cleanup and Step 10 log | no workspaces besides the scout, no bookmarks, no pushes; the log goes to `$RUN/triage-only.md`, never to `LOGDIR` |

`triage-only` answers "what would today's run attempt?" cheaply. Its log has the same shape as a
full run's. "Pushed" and "Attempted, not pushed" read `skipped (triage-only)`, and "Flagged, not
attempted" marks each selected candidate `selected` with its slug and budget. A `triage-only` log is
not history: a later run does not read it, because it lives outside `LOGDIR`.

Before a first run, or after editing the scripts, run `$SKILL/scripts/test-workspace.sh`. It is a
pass/fail check that the scout workspace lands on a fresh `main@origin`, that removal leaves nothing
behind, and that no jj operation touched the default working copy.

Unattended runs start from `$SKILL/scripts/run-daily.sh`, which starts this skill headless with
permission checks skipped, as the vault's other server jobs run. A scheduler that stops a run still
in progress records it first with `$SKILL/scripts/supersede.sh <start time>`. How the team schedules it lives in the vault, in `automation/daily-simplify/`.

Paths used throughout:

| name | path |
|---|---|
| `SKILL` | `${CLAUDE_SKILL_DIR}`, the directory holding this file, in whichever workspace the session loaded it from |
| `SRCS` | `$CAMBRA_SRCS` when set, otherwise the parent of the workspace `SKILL` is in: the directory holding the cambra workspaces |
| `REPO` | `$CAMBRA_REPO` when set, otherwise `$SRCS/cambra`: the default workspace, which holds the user's working copy |
| `CACHE` | `$CAMBRA_BUILD_CACHES/simplify-cache`, where `CAMBRA_BUILD_CACHES` defaults to `$SRCS/cambra_build_caches`: the two workspaces' persistent cargo targets and the run directories |
| `VAULT` | `$CAMBRA_VAULT`, by default `$SRCS/vault`; it must hold `_system/AI-CONTEXT.md` <!-- doc-refs-ignore: vault path --> |
| `LOGDIR` | `$VAULT/automation/daily-simplify/outputs`, which Obsidian Sync carries to every machine; the run writes files there and never runs git in the vault |
| `RUN` | `$CACHE/runs/<YYYY-MM-DD>`, holding this run's seeds and agent reports |
| `SCRATCH` | `$RUN/scratch-<slug>`, one per attempt: its agents' gate logs, backups and temp files |

`$SKILL/scripts/workspace.sh paths` prints `SRCS`, `REPO`, `CACHE`, `VAULT` and `LOGDIR` as this
machine resolves them, and `TODAY`, the run date `D` in America/Denver. Shell variables do not
persist between commands, so substitute the values wherever a command below writes `$NAME`.

`$SKILL/scripts/workspace.sh` owns every jj workspace operation. It runs jj against `REPO` only
with `--ignore-working-copy`, so it never snapshots or rewrites the user's working copy. A run uses
two workspaces: `scout`, which the finders read, and `attempt`, where one candidate at a time is
implemented, reviewed and pushed. Attempts run in series, so at most one build runs at a time.

Two scripts set what a build or gate needs:

- `$SKILL/scripts/in-workspace.sh <ws> <seconds> <command>` runs a build or test in a run workspace,
  under that workspace's cargo target and a timeout, so a test that never finishes ends.
- `$SKILL/scripts/gate.sh <ws> <log-prefix>` runs `./ci.sh fast` through `in-workspace.sh` and
  writes `<log-prefix>.log`.

`fast` is the only gate the run executes. GitHub CI runs the full gate on each draft PR. The next
run's Step 0 closes a draft whose CI failed and marks one whose CI passed ready for review, so a
draft stays a draft for at most a day after its CI finishes.

Each attempt's agents write their logs, backup copies and temp files under that attempt's
`SCRATCH`, never under the session scratchpad or `/tmp`. A scratch directory is named by slug
because every attempt reuses the `attempt` workspace. Gate logs are `$SCRATCH/gate-*.log`,
written by `gate.sh`, so a report cites the log and the orchestrator
reads it instead of trusting the agent's summary.

Commits are named by change id throughout. A rebase or a `jj describe` rewrites a
commit's id and keeps its change id. The one exception is a commit being abandoned: record its
commit id, which stays resolvable after the abandon.

## Why the pipeline has this shape

The design follows the evidence on LLM-driven refactoring. The research behind it is summarized in
`$SKILL/research.md`.

- **Narrow passes find more than open-ended ones.** A finder told which kind of simplification to
  look for, in a bounded scope, finds several times what "find simplifications" finds. Each finder
  therefore owns one category and one scope.
- **Most raw suggestions are wrong.** In published studies, 60–80% of raw LLM refactoring
  suggestions were invalid or useless before a mechanical filter removed them. Triage re-reads the
  cited code before any candidate is attempted.
- **Applied refactors silently change behaviour**, and passing tests do not prove otherwise. The
  common causes are collapsed case analysis, added functionality, inconsistent renames and misread
  context. A cold reviewer looks for exactly these.
- **Compound refactors fail about twice as often as atomic ones.** Each attempt is the smallest
  standalone change, with a budget fixed at dispatch time. Exceeding the budget means the attempt
  is abandoned, not stretched.
- **Over-abstraction is the characteristic LLM non-simplification.** A generic helper taking
  closures removes duplication and adds indirection. Fewer lines plus more indirection is rejected.

Repo-specific context the finders must hold
(`vault/projects/code-health-tooling/_index.md`): <!-- doc-refs-ignore: vault path -->
cambra has little complexity debt. At its default threshold `cognitive_complexity` fires at two
sites. Its real debt is duplication and cross-module coupling. Weight the finders' attention
accordingly.

## Step 0 — Preflight

```bash
$SKILL/scripts/workspace.sh paths          # SRCS, REPO, CACHE, VAULT, LOGDIR; TODAY is D
$SKILL/scripts/preflight.sh $LOGDIR/D.md   # in triage-only mode: $CACHE/runs/D/triage-only.md
$SKILL/scripts/workspace.sh list           # stale simplify-* workspaces
gh auth status 2>&1 | head -3
$SKILL/scripts/settle-drafts.sh            # in triage-only mode: --dry-run
mkdir -p $RUN
python3 -I $SKILL/scripts/history.py $RUN/history.md   # every simplify PR, in any state
ls -t $LOGDIR/                             # recent run logs
```

- `preflight.sh` removes run directories older than 14 days, which takes their scratch directories
  with them, and sweeps each cargo target down to a size limit. Record the free disk it prints under
  "Run notes". When less than 50 GB is free, it exits 3 after writing the reason to the day's log:
  stop the run there, with no further steps.
- `settle-drafts.sh` settles each earlier run's draft whose GitHub CI has finished, and prints one
  line per PR it changes. It runs before `history.py`, so today's history already shows each PR in
  its new state.
  - A draft whose CI failed is closed. Log each one under "Attempted, not pushed" as
    `discarded: CI failed`, with the failed checks and the PR link.
  - A draft whose CI passed is marked ready for review. List each one under "Run notes" as
    `marked ready`, with the PR link.
- If `$RUN/superseded.md` exists, the scheduler stopped a run still in progress to start this one.
  Copy its note into "Run notes".
- If stale `simplify-*` workspaces exist, a previous run crashed or was superseded. For each one,
  check `jj -R $REPO --ignore-working-copy log -r 'simplify-<name>@'` for unpushed work worth
  recording. Note it in today's log, then `workspace.sh remove <name>`.
- If `$LOGDIR/D.md` already exists, this is a second run today. Append a `## Run 2` section to the
  same file rather than overwriting it.
- Read the recent logs and `$RUN/history.md`. Together they are the **history**. A candidate
  matching a history entry is skipped, unless the code it cites has changed since or the recorded
  reason for dropping it no longer holds. A history entry is one of three things:
  - an open simplify PR;
  - a simplify PR a human closed without merging, with the closing comment as the reason. This
    entry is permanent: the run never re-proposes a candidate a human closed, unless its cited
    code has changed and the closing comment's reason no longer holds;
  - a simplify PR `settle-drafts.sh` closed for a CI failure in the last 14 days;
  - a candidate a log records as discarded, abandoned or rejected in the last 14 days.
- `$RUN/history.md` also holds the review comments on recently merged simplify PRs. They are
  guidance for the finders (Step 3), not history entries.
- Copy the merge-rate table from `$RUN/history.md` into the log's "Merge rate" section. It answers
  whether triage and the reviewers agree with the humans who merge.

## Step 1 — Fresh base and scout workspace

```bash
$SKILL/scripts/workspace.sh fetch          # jj git fetch; prints main@origin
$SKILL/scripts/workspace.sh add scout      # prints the workspace dir, SCOUT
```

`add` creates workspace `simplify-scout` at `$SRCS/cambra-simplify-scout`. Its working copy is a new
empty commit whose parent is the freshly fetched `main@origin`. Record the `main@origin` commit id
in the log. Every workspace this run creates uses that same base.

## Step 2 — Seed signals

```bash
$SKILL/scripts/seed.sh $SCOUT $RUN        # ~1 min warm; a cold clippy build takes longer
```

This writes `$RUN/seeds.md` with eight sections:

- 120-day hotspots (change count × code lines)
- exact clone regions
- renamed clone regions
- cross-module `use crate::` edges
- file pairs that change together in the same commits
- comments marking defensive handling of supposedly impossible cases
- comments that admit a workaround
- clippy candidates at lowered thresholds (`match_same_arms`, `cognitive_complexity` ≥ 15,
  `too_many_lines` ≥ 120, and others)

Read the digest yourself. Then choose today's **focus files**: six to ten files from the top of
the hotspot table that the history has not covered in the last 7 days. Add any file named in a
clone region of 15 or more normalized lines.

## Step 3 — Finders (read-only, parallel)

Dispatch **five** finders in one message, using `subagent_type: Explore` with "very thorough"
breadth. Explore agents cannot edit files, which keeps the scout workspace clean. Build each
prompt from `$SKILL/prompts/finder.md`, filling in:

- the category
- the scout path
- `SRCS`
- `$RUN/seeds.md`
- the focus files
- the history entries relevant to the category
- the review comments from `$RUN/history.md` on merged PRs of the category, as guidance

The five categories:


| category | what it hunts |
|---|---|
| `duplication` | One decision implemented more than once: graph and tree traversals, fixpoint loops, visitors over `Expr`/`Type`, the same case analysis repeated over one enum in several files, clone regions from the seeds |
| `encapsulation` | A fact one module owns that another module re-derives or re-asserts in a way its behaviour depends on: recomputed analyses, real logic for impossible cases, reaching into another module's representation, visibility that bypasses constructors, conventions with no owner, implicit concepts. Cheap verification at an input (boundary asserts, post-inference re-typechecking used as a tripwire) is not a candidate. Append `prompts/encapsulation.md` to this finder's prompt |
| `complexity` | Functions whose control flow can be flattened: early returns, `let … else`, merging `match` arms that share a body, splitting a function that does two things. Use the clippy `cognitive_complexity`/`too_many_lines`/`match_same_arms` seeds |
| `concision` | Lines that carry nothing: dead code and unused `pub` (seeds: `redundant_pub_crate`, `unused_self`, `dead_code`), needless clones or collects, hand-rolled std functionality, wrappers that only forward |
| `comments` | Comments that narrate history, restate the code, hedge, or run long, judged against the [prose style](../../../CLAUDE.md#prose-style-specifications-not-blog-posts) and [code comment](../../../CLAUDE.md#code-comments) rules in `CLAUDE.md` and against [the spec-prose skill](../spec-prose/SKILL.md). Also stale references a doc rename left behind |

Each finder returns at most **five** candidates in the schema in `prompts/finder.md`. Save each
finder's raw report to `$RUN/finder-<category>.md`.

Triage also takes each "Structural findings" entry from the logs of the last 14 days as a
candidate. One whose smallest standalone step passes the size rule in Step 4 is attempted as that
step. One that does not stays in the log it came from and is not logged again.

## Step 4 — Triage (you, not a subagent)

Triage is the filter. Most raw suggestions should die here. For every candidate:

1. **Re-read the cited code** in `$SCOUT` at the cited lines. If the code does not say what the
   candidate claims (wrong lines, the copies differ in a way the candidate ignores, the "dead" item
   has a caller), reject it as `hallucinated`.
2. **Usefulness.** Reject when:
   - it is a one-line extraction;
   - a helper would absorb nearly the whole function;
   - it adds a generic helper, trait or closure parameter where the copies differ in more than a
     value;
   - the net change is a rename;
   - the "duplicates" are parallel structure over different enums that will diverge, which is the
     right shape for a compiler.
3. **Design docs.** Read the design-doc sections the candidate cites (`docs/design.md`,
   `src/design.md`, `src/ccl/design/`, `src/interpreter/design-*.md`, `chl-parser/design-*.md`,
   `docs/operational-semantics/`). A candidate that contradicts a design doc is rejected, with two
   exceptions:
   - the doc is plainly wrong about the code it describes;
   - the doc, or a vault issue under `vault/issues/` whose status is not `done`, records the point
     as a known gap or inconsistency.

   Under either exception the attempt fixes the doc in the same commit, and the log says so.
4. **History.** Drop a candidate that matches a history entry (Step 0).
5. **Atomicity.** If the candidate is really two changes, keep the smaller standalone one, and log
   the other as flagged but not attempted.
6. **Encapsulation candidates.** Confirm the `producers` list yourself: grep for every
   constructor of the boundary's input. Reject the candidate if any re-derivation it deletes is
   verification rather than load-bearing, i.e. it only asserts and fails loudly.
7. **Size.** Anything whose honest estimate exceeds roughly 400 changed lines or 8 files is too big
   for a daily attempt. Log it under "Structural findings", with enough detail for a later run or a
   human to pick it up. Do not attempt it.

Select at most **four** candidates to attempt. Rank them by:

1. expected reduction in what a reader must hold in their head;
2. confidence;
3. hotspot score.

Assign each one:

- a slug (kebab-case, ≤ 5 words);
- a **budget**: the files the change may touch, the maximum changed lines (2× the finder's
  estimate, at least 40), and the expected sign of the net production line count. For an
  `encapsulation` candidate, files whose only change is deleting a load-bearing re-derivation do
  not count against the 8-file limit.

## Steps 5–8, once per candidate

In `triage-only` mode, skip Steps 5–8 and go to Step 9.

Take the selected candidates one at a time, in rank order. For each, run Steps 5 to 8 to the end,
then `workspace.sh remove attempt`, then start the next. A pushed commit survives the removal
because its bookmark keeps it; a discarded one is abandoned and its commit id goes in the log.

### Review guard

A reviewer reads the attempt's commits but must not change them. jj snapshots the working copy
into `@` at the start of every jj command, so a file a reviewer edits joins the commit under
review the next time anything runs jj in `WS`. The `--stat` budget check misses an edit inside a
budgeted file, and the gate only proves the result builds and passes. Every review dispatch, in
Steps 6 and 7, runs inside this guard:

1. Before dispatching the reviewer, record the attempt's commit ids:
   `jj -R $WS log -r 'main@origin..@' --no-graph -T 'commit_id ++ "\n"'`.
2. After the reviewer returns, run the same command and compare. It runs without
   `--ignore-working-copy`, so it snapshots any edit the reviewer left behind and the ids change.

Any difference voids the review: discard the attempt, whatever the verdict, and log it as
`discarded: reviewer edited the workspace`.

## Step 5 — Implementer

```bash
$SKILL/scripts/workspace.sh add attempt    # prints the workspace dir, WS
mkdir -p $RUN/scratch-<slug>               # SCRATCH
```

Dispatch one `general-purpose` implementer in the foreground and wait for its report. Build its
prompt from `$SKILL/prompts/implementer.md`, filled with:

- the candidate verbatim, after triage
- `WS`, `SCRATCH` and `SKILL`
- the budget
- the design-doc sections triage read

The implementer works only inside its own `WS` and returns one of two reports:

- `READY` with a change id and the path of its gate logs;
- `ABANDONED` with a reason in one of these classes: `scope-creep`, `invalid-assumption`,
  `behaviour-change`, `design-conflict`, `gate-failure`, `not-simpler`.

It never pushes. Save each report to `$RUN/impl-<slug>.md`.

## Step 6 — Adversarial review (cold)

For a `READY` result, dispatch a fresh `general-purpose` reviewer from
`$SKILL/prompts/reviewer.md`, inside the review guard. Give it:

- the candidate's stated intent;
- `WS`, `SKILL` and the change id;
- `$SCRATCH/review` as its `SCRATCH`;
- the design-doc sections triage read.

Do not give it the implementer's report or narrative. The reviewer must reach its own judgement
from the intent and the diff. It returns `ACCEPT`, `REJECT` or `REVISE`, with a reason.

- `REJECT` means the attempt is discarded.
- `REVISE` means one bounded fix round. Send the reviewer's points to the implementer with
  `SendMessage`, then re-review once, inside a fresh review guard. A second `REVISE` counts as
  `REJECT`.

Then check the result yourself. Read `jj -R $WS diff -r <change> --stat` and confirm the change
stayed inside the budget's files plus files under `tests/`, and that its changed lines outside
`tests/` are within the budget.

## Step 7 — Staff review and fixes

Each attempt the adversarial reviewer accepted gets a staff-level review before it is pushed. The
fixes land as a second commit on top of the reviewed one, in the same workspace. The PR carries
both commits under one bookmark.

The review follows the repo's `staff-rust-review` skill, read from
`$WS/.claude/skills/staff-rust-review/SKILL.md` so it is the version at the run's base.

1. **Review.** Dispatch a fresh `general-purpose` agent from `$SKILL/prompts/staff-reviewer.md`,
   inside the review guard. Give it:
   - the candidate's stated intent;
   - `WS`, `SKILL` and the change id;
   - `$SCRATCH/staff-review` as its `SCRATCH`;
   - the design-doc sections triage read.

   Do not give it the implementer's report or the adversarial reviewer's verdict. Save its report
   to `$RUN/staff-<slug>.md`.
2. **Read the report.** It has two lists. `## Findings` holds what should change in this commit,
   each a list item with the title line `<kind> : <location> <summary>` and details beneath it.
   The kind is `incorrect` when the finding says the change is wrong (it changes behaviour,
   breaks an invariant, or contradicts a design doc) and `improve` otherwise. `## Architectural`
   holds design-level problems whose fix reaches beyond this change.
   - Architectural findings are not fixed in this commit. Record each one under "Structural
     findings" in the log, with its details. The attempt still ships, and a later run's triage
     reads the finding as a candidate (Step 3).
   - When `## Findings` is `none`, go to Step 8 with the single commit.
3. **Address.** Build a message from `$SKILL/prompts/address-findings.md` with every finding from
   `## Findings`, each with its title line and details verbatim. Set `MAX_FIX_LINES` to half the
   attempt's line budget or 20, whichever is larger. Send it to the implementer with
   `SendMessage`. The implementer runs `jj new <change>`, so the fixes land in a new commit and
   the reviewed commit stays as the adversarial reviewer accepted it. Save the report to
   `$RUN/fix-<slug>.md`.
4. **Judge the result.**
   - `ENDED`: an `incorrect` finding was declined, or the gate failed. Discard the attempt, as for
     a `REJECT`.
   - `ADDRESSED` with `fix change: none`: every finding sent was declined with a reason, and none
     was `incorrect`. Go to Step 8 with the single commit.
   - `ADDRESSED` with a fix commit: read `jj -R $WS diff -r <fix-change> --stat` and confirm two
     limits:
     - it stays inside the budget's files plus files under `tests/`;
     - its changed lines outside `tests/` are at most `MAX_FIX_LINES`.

     A fix commit over either limit is dropped unreviewed, as below. Otherwise dispatch a fresh
     reviewer from `$SKILL/prompts/reviewer.md` on the fix commit alone, inside the review guard,
     with the addressed findings as its intent and `$SCRATCH/review-fix` as its `SCRATCH`.
     - `ACCEPT` keeps the fix commit.
     - `REVISE` gets one bounded round, as in Step 6. Send the reviewer's points to the implementer
       with `SendMessage`. The implementer edits the fix commit in place (`jj edit <fix-change>`)
       and re-runs the gate. Re-review once, with the same reviewer, the same limits and a fresh
       review guard. A second `REVISE` counts as `REJECT`.
     - `REJECT` drops the fix commit.

     Before dropping a fix commit, record its commit id
     (`jj -R $WS log -r <fix-change> --no-graph -T commit_id`). Then `jj -R $WS abandon
     <fix-change>` and `jj -R $WS edit <change>` put `@` back on the reviewed commit. The attempt
     goes to Step 8 without the fixes when no finding was `incorrect`, and is discarded when one
     was. The dropped commit stays recoverable with `jj new <commit-id>`.

Record each finding by its title line with its disposition for the log: addressed, declined with
the reason, or dropped with the fix commit.

In what follows, `<change>` is the reviewed commit's change id, and `<tip>` is the fix commit's
change id when one was kept, `<change>` otherwise.

## Step 8 — Push survivors as draft PRs

For an accepted attempt, running jj with `-R $WS`:

1. **Re-fetch** (`workspace.sh fetch`). If `main@origin` moved since Step 1, run
   `jj -R $WS rebase -b @ -d main@origin`, which moves both commits. CI runs on the branch tip,
   not on a merge with `main`, so a green check on a stale base says nothing about the code once
   it merges.
2. **Run the gate:** `$SKILL/scripts/gate.sh $WS $SCRATCH/gate-final`. It must pass.
3. **Write the title and body.** Use the repo's `pr-description` skill
   (`$REPO/.claude/skills/pr-description/SKILL.md`). Read it, then have a cold subagent draft the
   title and body from `jj diff --from main@origin --to <tip>` alone. The repo squash-merges, so
   the body describes both commits as one change. The skill sets an imperative title and a
   summary-first body. End the body with one line, `Found by the daily simplification run, <D>;
   category: <category>.`, naming the candidate's finder category. `history.py` reads the
   category from it for the merge rate. Never credit an AI tool or model, anywhere.
4. Publish:

   ```bash
   jj -R $WS describe -r <change> -m "<title>" -m "<body>"   # the fix commit keeps its own
   jj -R $WS git push --named simplify-agent/<D>-<slug>=<tip>   # fails if the bookmark exists
   gh pr create --repo cambra-dev/cambra --draft --base main \
     --head simplify-agent/<D>-<slug> --title "<title>" --body-file <file>
   ```

5. If the PR resolves or advances a vault issue, name the issue beside the PR in the log. The run
   does not edit the vault.

## Step 9 — Cleanup (always, including after a failure)

```bash
$SKILL/scripts/workspace.sh remove-all
$SKILL/scripts/workspace.sh list           # must print nothing
jj -R $REPO --ignore-working-copy log -r 'bookmarks(glob:"simplify-agent/*") & ~remote_bookmarks()'
```

- `remove-all` removes every `simplify-*` workspace jj knows about, including one a failure left.
  Each removal forgets the workspace and abandons its commits that no bookmark keeps alive, which
  covers discarded attempts and empty working-copy commits.
- Abandoned commits stay recoverable by the commit id the log records.
- Scratch directories stay, so a failed gate's log remains readable. The 14-day removal of run
  directories in Step 0 deletes them.
- The final `log` must be empty, meaning every simplify bookmark was pushed.
- Do not touch any bookmark that is not `simplify-agent/*`.

If the run dies partway, the next run's preflight finds the stale workspaces.

## Step 10 — Log

Write `$LOGDIR/<D>.md` from `$SKILL/prompts/log-template.md`. In `triage-only` mode the log goes to
`$RUN/triage-only.md` instead. Wrap prose at 100 columns. Every row names its subject in words.
Write "the duplicated free-variable walk in `subst.rs` and `inline.rs`", never "candidate 3" or
"finding B". The log records:

- the base commit;
- every flagged candidate and its disposition;
- every attempt and its status: `pushed` with the PR link, `discarded` with the reviewer's reason,
  or `abandoned` with its reason class and what the attempt learned;
- each staff-review finding, by its title line, and its disposition: addressed, declined with the
  reason, or dropped with the fix commit; each architectural finding under "Structural findings";
- the merge-rate table from `$RUN/history.md`;
- the commit id of each attempt that did not ship, which `workspace.sh remove` prints;
- structural findings too big for a daily attempt;
- open questions for the team;
- harness problems, such as a script failure or a flaky gate.

Then reply with the following. In an unattended run the reply lands in `$RUN/session.jsonl`, and
the log is the record anyone reads:

- the log path;
- the draft PR links;
- one line per attempt that did not ship.

## Rules that hold throughout

- Only the orchestrator pushes. Implementers and reviewers never push, never create bookmarks,
  and never run jj or cargo in `REPO`, the scout, or any workspace outside this run.
- Never re-bless the inspector golden fixtures, and never edit expected test output to make a
  refactor pass. Moved goldens or expectations mean behaviour changed, so the attempt is
  abandoned.
- Every jj command that could open an editor gets `-m` or `--config ui.editor=true`. A bare
  `jj squash` hangs forever.
- A simplification may delete or rewrite tests that the refactor makes redundant. It never
  weakens an assertion.

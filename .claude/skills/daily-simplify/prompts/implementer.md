# Implementer prompt template

Fill every `{{…}}` and send the text below the rule as a general-purpose agent's prompt.

---

You are implementing one simplification in cambra, a programming language and compiler in Rust.
Make the change below as the smallest standalone commit that preserves behaviour, or abandon it
and say why. Abandoning is a normal, useful outcome. A forced-through change that grew or changed
behaviour is the failure this process exists to prevent.

## Your sandbox

- Work only in `{{WS}}`. It is a jj workspace whose working-copy commit `@` sits on a fresh
  `main@origin`, or on the simplifications this run already pushed, which you leave as they are. Your edits land in `@` automatically, and there is no staging. Start with
  `cd {{WS}}`; the shell stays there between commands.
- Never `cd` into, build in, or run jj against any other directory. Other workspaces hold other
  people's work, and a write there rewrites their commits.
- Write every log, backup copy (`*.orig`) and temp file under `{{SCRATCH}}`. Never use the session
  scratchpad or `/tmp`.
- Never push, never create or move bookmarks, never run `jj git push` or `gh`.
- Pass `-m` to every jj command that takes a description. A bare `jj squash`/`describe`/`commit`
  opens an editor and hangs forever.
- Do not stop to ask questions. Anything you would ask is either a reason to abandon or a note in
  your report.
- Run every build and test as `{{SKILL}}/scripts/in-workspace.sh {{WS}} 1800 <command>`, for
  example `… in-workspace.sh {{WS}} 1800 cargo test <name>`. It uses the workspace's cargo target
  and a timeout. A test killed by the timeout under a temporary break counts as the test catching
  the break; on unmodified or refactored code it is a `behaviour-change`.
- Run the gate, `./ci.sh fast`, with `{{SKILL}}/scripts/gate.sh {{WS}} {{SCRATCH}}/gate`. It
  writes `{{SCRATCH}}/gate.log` and prints its tail.
- Run pin checks (step 2) as targeted `cargo test <name>` runs, never the whole suite, and run at
  most one cargo command at a time.

## The candidate

{{CANDIDATE}}

## Budget (fixed at dispatch)

- Files you may touch: {{FILES}}. Adding a test file or a design-doc fix the candidate names is
  allowed.
- Changed lines (`jj diff --stat` total, files under `tests/` excluded): at most {{MAX_LINES}}.
  Tests you add in step 2 do not count. A test added inside a production file's `#[cfg(test)]`
  module does count, so put a new test under `tests/`.
- Expected net production line delta: {{NET_SIGN}}.

## Governing design docs

{{DESIGN_DOCS}}

Your change must stay consistent with these. If the code shows a doc is plainly wrong, or the doc
records the point as a known gap, fix the doc in this same commit and say so. Follow
`{{WS}}/CLAUDE.md`, which covers prose style, comments, doc references (`./ci.sh doc_refs`) and
hard-wrapping Markdown at 100 columns.

## Procedure

1. **Re-verify the premise.** Read every cited location. If the claim does not hold (the copies
   differ materially, the "dead" item has a caller, the doc forbids it), abandon with
   `invalid-assumption`.
2. **Pin the behaviour.** For each behaviour the change touches, find the test that exercises it.
   Check that it really does by temporarily breaking the code, for example by flipping a branch or
   returning early. Run that test, confirm it fails, then revert the break exactly. Where no test
   covers the touched behaviour, add a focused one that passes on the unmodified code before you
   refactor. Use `indoc!` for multi-line CHL. A program that compares the compiler against the
   differential interpreter goes in the grid in `tests/it/generated_pairs.rs`, as a skeleton or a
   filler, never as a one-off case in `tests/it/differential_interp.rs`. A comment-only change
   skips this step.
3. **Make the change.** Make it the smallest edit that achieves the candidate, and no adjacent
   cleanups. Run `cargo fmt`, then loop on the gate (or a targeted `cargo test <name>` for a
   tight loop).
   **Encapsulation candidates** (category `encapsulation`) take two stages:
   1. Make the owner establish the fact at its boundary. Add a `debug_assert!` (or a restricted
      type) whose message names the invariant. Run the full suite with the new assertion **and**
      the old re-derivations both in place. Any assertion failure means a producer does not uphold
      the fact. Abandon with `invalid-assumption`, and name that producer.
   2. Delete only the re-derivations the candidate marks load-bearing. Never delete a check that
      only asserts and fails loudly: boundary asserts and post-inference re-typechecking are
      deliberate tripwires.
4. **Watch the abandonment triggers.** Abandon when any of these happens:
   - `scope-creep`: you need a file outside the budget, the diff outside `tests/` passes
     {{MAX_LINES}} lines, or you need a new abstraction the candidate did not describe.
   - `behaviour-change`: an existing test fails for a reason other than a typo in your edit; any
     inspector golden fixture or pinned expectation moves; or any diagnostic text, `Display`
     output or iteration order changes.
   - `gate-failure`: five fix rounds without `./ci.sh fast` going green.
   - `not-simpler`: the finished code does not read simpler. This includes the case where it has
     fewer lines but more indirection, such as a closure-taking helper or a trait with one impl.
   - `design-conflict`: the change needs a design decision the docs do not settle.

   When you abandon, leave the workspace as it is. Do not revert, and do not clean up.
5. **Describe.** `jj describe -m "<imperative subject>" -m "<two to four sentences: what was
   duplicated or convoluted, what replaces it, why behaviour is unchanged>"`. No AI attribution.

## Report

Return exactly this:

```
status: READY | ABANDONED
reason class: <for ABANDONED: scope-creep | invalid-assumption | behaviour-change | gate-failure | not-simpler | design-conflict>
change: <jj log -r @ --no-graph -T 'change_id.short(12)'>
diff: <jj diff --stat summary line>; net production lines: <±N>
what changed: <2–4 sentences>
behaviour evidence: <tests that pin the touched behaviour; the break you tried and the test that caught it; tests added>
gate: <the gate's last line; {{SCRATCH}}/gate.log>
learned: <for ABANDONED: what the candidate got wrong, in a form the next run can use to avoid re-proposing it>
```

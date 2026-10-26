---
name: staff-rust-review
description: Perform a staff-level Rust code review. Analyzes git commits, ranges, or branches against architectural design documents to ensure idiomatic code, performance, safety, and alignment with project vision. Use when a user asks for a code review or to verify changes against documentation.
---

# Staff Rust Review

## Overview

This skill provides a rigorous, high-level code review process. It combines the deep context of design documentation with the specific changes in a git commit range to provide actionable, senior-level feedback.

## Workflow

### 1. Identify Scope

Determine the review scope from the user's request:

- **Range**: Default to `HEAD` if not specified. Support commit hashes, branches (e.g., `main..feature`), or ranges (e.g., `HEAD~3..`).
- **Design Docs**: Default to `docs/design.md`. Check for additional docs mentioned by the user or relevant files in `docs/`.

### 2. Context Gathering

Execute the following to build context:

- **Repo Changes**: Use `jj` if available or referenced, otherwise `git`, to read commit messages and the full diff.
  - **Git**: `git show [range] -p`
  - **jj**: `jj show [range]`
- **Design Docs**: Read `docs/design.md` and any other specified documents to understand the intended semantics and architecture.

### 3. Analysis Criteria

Review the changes against these standards:

- **Architectural Alignment**: Does the implementation match the requirements and operational semantics described in the design docs?
- **Rust Idioms & Best Practices**:
  - Proper use of `Option`, `Result`, and error handling.
  - Efficient ownership, borrowing, and lifetime management.
  - Leveraging the type system (Newtype pattern, Enums) for safety.
- **Maintainability**: Code readability, naming clarity, and modularity.
  - Testing: ensure that the tests correctly assert the core logic of the new features, or prevent the errors claimed.
- **Performance**: Pipelining, parallelization, and dataflow efficiency (per Cambra's goals).
- **Prose**: New or edited comments and docs follow "Prose style" and "Code Comments" in the repo's
  `CLAUDE.md`.
- **Scope**: Every finding is about the diff, or about code the diff makes wrong. A problem in code
  the change did not touch goes under `## Out of scope`, not under `## Findings`.
- **Prioritize Impactful Feedback**
  - Ignore whitespace nits in markdown files (such as trailing whitespace).

### 4. Review Output

Open with an **Executive Summary**: the verdict on the change, in a few sentences. Three sections
follow it.

`## Findings` lists only what should change in this commit before it merges. A point the change
could take or leave is not a finding: leave it out. Each finding is a list item. The item's first
line is its title line, and the details sit indented beneath it:

```
## Findings

- incorrect : src/ccl/simplify.rs:212 Merged arm drops the `Infer` guard
  <what is wrong and why, the concrete fix, and the test case with the failure it produced>
- improve : src/ccl/simplify.rs:240 Comment narrates the old loop
  <what should change, and the replacement>

## Architectural

- src/ccl/lower.rs Zip helper belongs to the lowering module
  <the design problem, the files and concepts the separate change would touch, and the design
  question it must settle first, if any>

## Out of scope

- src/ccl/inline.rs:88 <adjacent problem the diff did not touch>
```

A finding's title line has three parts:

- **Kind**, one of two:
  - `incorrect`: the change is wrong. It changes behaviour, breaks an invariant, or contradicts a
    design doc.
  - `improve`: anything else that should change before merge.
- **Location**: `path:line` at the reviewed commit, or `path` when no single line holds the
  finding, or `-` when no file does. Do not invent a line number to fit the format.
- **Summary**: under 60 characters. It names the finding; the details beneath it carry the
  substance.

`## Architectural` lists design-level problems whose fix reaches beyond this change, such as a
missing concept or an abstraction in the wrong module. Each item is the brief for a separate
change, which an agent can pick up as readily as a human, so give it enough detail to act on. Its title line is the location and summary, without a
kind. A design problem whose fix fits this change is a finding: an `incorrect` one when it makes
the change wrong, an `improve` one otherwise.

`## Out of scope` lists problems in code the change did not touch.

No two title lines in one review are the same: the title line identifies the finding to whoever
addresses it. Write `none` under a section that has no items.

For each `incorrect` finding, write a concise test that exercises the bug and confirm it fails on
the change and passes on its parent (step 5), or say why such a test is impractical. A test that
fails on both shows a bug the change did not introduce: list it under `## Out of scope`. When the
code under test is new in the change, the test has no parent run.

### 5. Build and Test Scope

A review runs no builds and no existing tests: GitHub CI runs every gate on each push. The one
exception is a test the review writes for an `incorrect` finding (step 4), which the review runs
to confirm that it fails against the change and passes against its parent.

Run that test with `cargo test`, scoped to the one binary that holds it:

- `cargo test -p <crate> --lib <name>` for a unit test;
- `cargo test --test it <name>` for an integration test under `tests/it/`.

A bare `cargo test <name>` builds every test binary of every default member before it filters, and
`./ci.sh fast` also runs the full suite and the frontend's checks.

Build with the dev profile and its default flags. Each other profile or flag set adds its own build
tree to the target directory: about 9 GB for `no-assertions` and about 40 GB for a debug build.
Review target directories are seeded from one another, so every later review carries whatever one
review builds. Run these only when the user asks for them in the session:

- `./ci.sh` in any mode;
- `cargo clippy --release` or any other `--release` build;
- `CARGO_PROFILE_DEV_DEBUG=full` or any other change to the compile flags, which rebuilds the
  workspace under new artifact hashes.

A finding that depends on a gate the dev profile does not compile (a `cfg(debug_assertions)` item,
an editor grammar) names the gate in the review instead of running it.

#### Trying a test in a temporary commit

A review leaves the commit under review unchanged. A test it writes goes in a temporary commit on
the change, and again in one on the change's parent; both are removed before the review reports.
`scripts/review-test.sh` beside this file makes and removes them. It describes each one
`review-test of <change id>`, naming the tip of the change under review, so its `clean` abandons
those commits and no other child of the same parents. Pass it `-R <workspace>` when the review
runs outside the workspace. In the jj workspace that holds the change:

1. Record where `@` is: `jj log -r @ --no-graph -T commit_id`, the id `ORIG`. Record the tip of
   the change as `CHANGE`, and the parent of its first commit as `BASE`. `BASE` is `ORIG-` only
   when `@` is the change's one commit; when `@` is an empty commit on top of the change, it is
   not.
2. `review-test.sh new CHANGE CHANGE`, then write the test. Edit nothing but the test.
3. Run it, scoped as above. Keep its output for the report.
4. Unless the code under test is new in the change, `review-test.sh new CHANGE BASE`, write the
   same test, and run it the same way. Keep its output too.
5. Copy the test into the finding's details, with the file it belongs in and the results it
   produced on the change and on its parent.
6. `review-test.sh clean CHANGE ORIG`, which returns `@` to `ORIG` and abandons both commits.
   Confirm that `jj log -r @ --no-graph -T commit_id` prints `ORIG` again and `jj status` shows no
   changes.

`scripts/test-review-test.sh` is the script's pass/fail test.

## Example Triggers

- "Review the head commit against `docs/design.md`, the design doc."
- "Give me a staff review of HEAD~2.. using `docs/design.md` as the reference."
- "Review branch feature-x"

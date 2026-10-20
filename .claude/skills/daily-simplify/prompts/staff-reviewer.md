# Staff reviewer prompt template

Fill every `{{…}}` and send the text below the rule as a fresh general-purpose agent's prompt.
Send nothing about how the implementation or the adversarial review went: the staff reviewer reads
the diff cold.

---

You are giving a staff-level review of a proposed simplification in cambra, a programming language
and compiler in Rust. The change has already passed a behaviour-preservation review. Review it as
a change about to be merged: architecture, idiom, naming, tests, and the prose of its comments and
docs.

Follow the repo's `staff-rust-review` skill, read from
`{{WS}}/.claude/skills/staff-rust-review/SKILL.md`, with these bindings:

- **Range:** the single commit with change id `{{CHANGE}}`. Read it with
  `jj -R {{WS}} show {{CHANGE}}`.
- **Design docs:** `{{WS}}/docs/design.md` plus the governing sections: {{DESIGN_DOCS}}.
- **The stated intent:** {{INTENT}}

Read the surrounding code in `{{WS}}`, and judge comments and docs against "Prose style" and "Code
Comments" in `{{WS}}/CLAUDE.md`. You may run tests with `{{SKILL}}/scripts/in-workspace.sh {{WS}} 1800 cargo test <name>`, which uses the workspace's
cargo target and a timeout.

Do not edit any file in `{{WS}}`, do not run jj commands that write, and do not touch any directory
outside `{{WS}}` and `{{SCRATCH}}`. Write every log, backup copy (`*.orig`) and temp
file under `{{SCRATCH}}`. Never use the session scratchpad or `/tmp`.

Every finding is about this commit's diff or code the diff makes wrong. Do not propose adjacent
cleanups the change did not touch; list those under "Out of scope" instead.

## Report

Write the skill's Executive Summary. A `## Findings` section takes the place of the skill's
Architectural Notes, Detailed Feedback and Next Steps. The report ends with an `## Out of scope`
section.

Each finding is a list item. The item's first line is its title line, and the details sit
indented beneath it:

```
## Findings

- Critical : src/ccl/simplify.rs:212 Merged arm drops the `Infer` guard
  <what is wrong and why, the concrete fix, and the test case the skill asks for>
- Architectural : src/ccl/lower.rs Zip helper belongs to the lowering module
  <the design problem, and what resolving it would touch>

## Out of scope

- src/ccl/inline.rs:88 <adjacent problem the diff did not touch>
```

The title line has three parts:

- **Category**, one of four:
  - `Critical`: the change is wrong. It changes behaviour, breaks an invariant, or contradicts a
    design doc. The commit does not merge with it unfixed.
  - `Important`: a defect in the change that should be fixed before merge.
  - `Nit`: a local improvement the change can take or leave.
  - `Architectural`: a design-level problem whose fix reaches beyond this change, such as a
    missing concept or an abstraction in the wrong module. It is recorded for a human and not
    fixed here. A design problem that makes the change itself wrong is `Critical`, not
    `Architectural`.
- **Location**: `path:line` at commit `{{CHANGE}}`, or `path` when no single line holds the
  finding, or `-` when no file does. Do not invent a line number to fit the format.
- **Summary**: under 60 characters. It names the finding; the details beneath it carry the
  substance.

No two title lines in one review are the same: the title line identifies the finding to the agent
that addresses it and in the run log.

Write `## Findings` followed by `none` when there are no findings.

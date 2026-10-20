# Address-findings message template

Fill every `{{…}}` and send the text below the rule to the candidate's implementer with
`SendMessage`. The implementer keeps its sandbox rules from `prompts/implementer.md`, including
writing every log and temp file under its `{{SCRATCH}}`.

---

A staff reviewer read your commit `{{CHANGE}}`. Address its findings in a **new commit on top of
it**, in the same workspace `{{WS}}`. Do not amend `{{CHANGE}}`: the reviewed change and the
response to the review stay separate commits.

## Findings

Each finding is a list item: a title line `<category> : <location> <summary>`, with the details
beneath it. Locations refer to `{{CHANGE}}`.

{{FINDINGS}}

## Procedure

1. Start the new commit before editing: `jj new {{CHANGE}} -m "Address staff review findings"`.
   Every edit after this lands in it.
2. Decide each finding:
   - **Critical and Important:** address it, unless the fix breaks a rule below.
   - **Nit:** address it when the fix is local and stays inside the budget.
   - **Decline** a finding when the fix needs a file outside the budget, changes behaviour, or
     the finding is wrong about the code. A declined Critical finding ends the attempt: say so in
     the report.
3. The rules from your original procedure still hold:
   - no inspector golden fixture or pinned expectation moves;
   - no diagnostic text, `Display` output or iteration order changes;
   - no assertion is weakened;
   - a test you add for a finding passes on `{{CHANGE}}` unless the finding is a bug in it.
4. Make no claim the code does not support. Most fix commits that fail review fail on a new
   sentence, not on the fix itself:
   - When a finding suggests replacement wording, use it unless the code shows it is wrong. Do not
     strengthen it.
   - Before writing any claim with a universal ("every arm", "only", "always", "fails in `f`",
     "all callers"), grep for every site it covers and confirm it holds at each. If it does not
     hold everywhere, name the exceptions or narrow the claim.
   - Code you add for a finding must not rely on behaviour a reader has to work out, such as a
     zip that stops early or an iterator adaptor that drops elements. Write the case out, or say
     it in a comment.
5. Files this commit may touch: {{FILES}}, plus test files a finding needs. Changed lines, test
   files excluded, may not exceed {{MAX_FIX_LINES}}. A fix that needs more is a decline: say so in
   the report.
6. Gate: `cargo fmt`, then `{{SKILL}}/scripts/gate.sh {{WS}} {{SCRATCH}}/gate-fix fast` until
   green, then `… gate.sh {{WS}} {{SCRATCH}}/gate-fix full`.
   Five fix rounds without green ends the round: leave the workspace as it is.
7. Describe: `jj describe -m "Address staff review of <subject of {{CHANGE}}>" -m "<one line per
   addressed finding: its title line and what changed>"`. No AI attribution.

If you decline every finding, abandon the empty commit with `jj abandon @` and report `fix change:
none`.

## Report

Return exactly this:

```
status: ADDRESSED | ENDED
fix change: <jj log -r @ --no-graph -T 'change_id.short(12)'> | none
diff: <jj diff -r @ --stat summary line>
addressed: <title line → what changed, one per line>
declined: <title line → reason, one per line>
gate: <the full gate's last line; the gate-fix-*.log paths under {{SCRATCH}}>
```

`ENDED` means a Critical finding was declined or the gate did not go green.

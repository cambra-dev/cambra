---
type: log
date: {{D}}
base: {{MAIN_COMMIT}}
flagged: {{N_FLAGGED}}
attempted: {{N_ATTEMPTED}}
pushed: {{N_PUSHED}}
tags: [cambra, simplification, daily-run]
---

# Simplification run — {{D}}

{{One paragraph: base commit, focus files and why they were chosen, what shipped, what did not.}}

## Pushed

{{The stack's number and link, when the run pushed two or more PRs. Rows are bottom first.}}

| PR | change | diff | staff review |
|---|---|---|---|
| [#N](url) — title <!-- doc-refs-ignore: template placeholder --> | {{one sentence naming the code}} | +a −b, net production ±n | {{n addressed in `fix-commit-id` / none}} |

{{Per PR with staff-review findings: each finding's title line (`<kind> : <location> <summary>`)
and its disposition: addressed, declined with the reason, or dropped with the fix commit.
Architectural findings go under "Structural findings".}}

## Attempted, not pushed

### {{subject in words}} — abandoned: {{reason class}} | discarded: reviewer {{REJECT}} | discarded: staff review {{declined `incorrect` finding}} | discarded: reviewer edited the workspace | discarded: CI failed | discarded: stack repair

- **Locations:** `path:lines`
- **What happened:** {{two sentences}}
- **Learned:** {{what the candidate got wrong; how the next run should avoid re-proposing it}}
- **Commit:** `{{id}}`, abandoned and recoverable via `jj new {{id}}`

## Flagged, not attempted

| candidate | category | locations | disposition |
|---|---|---|---|
| {{claim in words}} | duplication | `path:lines` | rejected at triage: hallucinated / not useful / design conflict (doc + heading) / history / deferred (ranked below the cut) |

## Merge rate

{{The merge-rate table from `$RUN/history.md`: per category, PRs merged, closed and open.}}

## Structural findings

{{Changes too big or too design-dependent for a daily attempt: what, where, and the design question
each one needs answered. Name a vault issue if one exists.}}

## Questions

{{Open questions for the team that a candidate depended on.}}

## Run notes

{{Harness problems: script errors, flaky gates, cleanup anomalies, time per phase. "None" if none.}}

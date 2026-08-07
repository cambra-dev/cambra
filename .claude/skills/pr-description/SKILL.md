---
name: pr-description
description: Write or revise a pull-request description, or the commit description that becomes one (`gh pr create --fill` copies it verbatim). Use when creating a PR, writing a commit message that will become a PR body, or editing an existing PR body.
---

# PR descriptions

A PR body is a map for the reviewer.

## The rules

**Open with a summary that stands alone** — one paragraph, before the first heading: **why** (the problem in terms the reviewer can understand), **what** (a concise description of the change), **so what** (the impact of the change). A reader who stops there should be able to say what the PR does and why it exists. An opening that starts mid-mechanism fails that test; that sentence is the second paragraph's job.

**The description is a review guide.** Order sections the way the change should be read: the core mechanism of the change first, then its consequences, then test coverage and docs changes. One idea per section, and name a section for the idea rather than for the files it touches — a section per changed file is noise.

**Focus on the *changes*. Push long-lived information to the docs.** Some content belongs only in a PR description: what connects the old and new versions of the code — why the old shape was wrong, what a reviewer should be suspicious of, how to read the diff. Everything else belongs in the codebase itself, with the description carrying a short summary of it. Terms and concepts the PR introduces get a one-line gloss so the body still reads on its own.

**Where the body and a doc would say the same thing, cite and summarize in a sentence.** One sentence handing off to a doc or a code pointer beats a restatement: the restatement drifts from the doc by the next change, and then two places disagree. Use repo-relative Markdown links, which GitHub resolves in a PR body, and point at a heading rather than a section number — `§3.9` rots at the next reordering, which is why the repo's reference conventions require a heading. `./ci.sh doc_refs` does **not** check descriptions (nor anything under `.claude/`), so confirm by hand that the heading exists and the anchor spells it correctly.

This applies hardest to the diff's *own* comments and docs. A change that explains itself in a new code comment, doc comment, or design-doc section has already published its reasoning; the body states the change and points at where the reasoning lives, in a clause rather than a paragraph. Restating a comment the same diff adds is the most common way a small PR ends up with a long description.

**Limit the size of the description.** It scales *sub-linearly* with the size of the change: a description is the first few levels of a tree, each level pointing at the next and carrying exponentially more detail than the last. The larger the PR, the larger the fraction of self-describing content that has to live in the codebase instead.

Compute the budget before drafting, from the diff's changed lines (`additions + deletions`) — about 10 × √lines:

| Diff | Description |
|---|---|
| 1 line | ~10 words (one sentence) |
| 10 lines | ~30 words |
| 100 lines | ~100 words |
| 1,000 lines | ~300 words |
| 10,000 lines | ~900 words |

Under about 100 words the description is the summary paragraph and nothing else — no headings, no `## Tests` section. Headings start earning their keep when there is a reading order to impose.

**Cut what neither motivates nor orients** — investigation narrative (wrong hypotheses, the order in which things were discovered) and re-narration of what the diff already shows. Compression must not cost accuracy, though: re-check every name, count, and list that survives against the diff.

## Author the body as Markdown

PRs here are often created with `gh pr create --fill`, so the PR body is the commit description *verbatim*, and this repo squash-merges, so the body becomes the `main` commit message. GitHub renders it as GitHub-Flavored Markdown, so write commit descriptions as Markdown, not as traditional column-wrapped git prose:

- **Do not hard-wrap inside a paragraph.** Let each paragraph be one soft-wrapped line and separate paragraphs with a blank line — otherwise every wrap point renders as a ragged `<br>` on GitHub.
- **Backtick every code construct** — type/identifier names, file paths, field and flag names (`` `CompiledProgram` ``, `` `dead_code` ``, `` `src/ccl/lineage.rs` ``).
- Use real Markdown for structure where it helps: `-` bullet lists for enumerations, blank lines between paragraphs.

## Revise before posting

Write three revisions before posting. A description is read by every reviewer and then survives as the commit message, so it earns the extra passes:

1. **Draft** from the diff.
2. **Check against the rules.** Does the opening stand alone? Is the section order a reading order? Is anything durable stated only here — or restated here from a comment the diff itself adds? Then count the words and compare against the budget; if the draft is over, the cut comes from what the codebase already says, not from the reviewer's map.
3. **Check against the diff.** Re-verify every name, count, and list. A compression pass introduces factual errors more readily than a draft does — an over-cut description that says a pass is affected when the diff exempts it is worse than a long one.

## Posting and updating

`gh pr edit --body` fails with exit code 1 on a Projects (classic) deprecation warning even when the update succeeds. Use the REST API:

```bash
gh api repos/OWNER/REPO/pulls/PR_NUMBER --method PATCH --field body="..." --jq .number
```

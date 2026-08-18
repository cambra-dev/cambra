---
name: pr-description
description: Write or revise a pull-request title and description, or the commit description that becomes one (`gh pr create --fill` copies it verbatim). Use when creating a PR, writing a commit message that will become a PR body, or editing an existing PR title or body.
---

# PR descriptions

A PR body is a map for the reviewer.

## Draft it cold

**Delegate the drafting to a fresh reader.** If you authored the change, spawn a subagent to write the title and body: hand it the PR number or the commit range, and pass along *nothing else* about how the work went. Relay its draft rather than rewriting it from your own understanding of the change.

The author is the worst-placed person to describe a change. You know why every hunk exists, so you write from the shape of the investigation and in the vocabulary you invented while working — neither of which the reviewer has. A reader holding only the diff can write only what the diff supports, which is exactly what the reviewer will be holding.

Keep the fresh reader cold in two ways:

- **When rewriting an existing description, tell the subagent not to read the current title or body.** A weak description anchors its own rewrite on the framing you are trying to escape.
- **Read the diff with `gh pr diff <n>`, not `gh pr diff --patch <n>`.** `--patch` prefixes the commit message, and under `gh pr create --fill` the commit message *is* the existing body — so a draft meant to be blind has already read the text it replaces.

When you cannot delegate, hold to the same discipline directly: work from the diff and the files it touches, and treat any sentence you could not have written from the diff alone as suspect.

## The title

**The title is an imperative that summarizes the change** — it completes "this PR will ___". The reader learns what the change does to the codebase, plus enough mechanism to tell it apart from a neighboring PR.

Do **not** state the new behavior as a fact in the present tense. It reads as a claim about how things already are, so the outcome and the change become indistinguishable, and the mechanism gets forced into a colon-clause tail:

| Instead of | Write |
|---|---|
| "Partition collapse composes: replace the bridge arm with normalize-then-recurse" | "Make partition-domain subtyping transitive by normalizing before comparing" |
| "`constrain_go` asserts the uniquely-keyed invariant it rests on" | "Assert the uniquely-keyed invariant `constrain_go` rests on" |

The title obeys the body's rules too: it stands alone, and it uses the reviewer's terms rather than the ones the work invented. A title that only parses *after* the review orients nobody.

**Revising a description means revising the title.** Leaving the title behind is the more misleading half of a stale PR — it is what shows up in the PR list, in notifications, and in `git log` once the squash-merge takes it.

## The body

**Open with a summary that stands alone** — one paragraph, before the first heading: **why** (the problem in terms the reviewer can understand), **what** (a concise description of the change), **so what** (the impact of the change). A reader who stops there should be able to say what the PR does and why it exists. An opening that starts mid-mechanism fails that test; that sentence is the second paragraph's job.

**The description is a review guide.** Order sections the way the change should be read: the core mechanism of the change first, then its consequences, then test coverage and docs changes. One idea per section, and name a section for the idea rather than for the files it touches — a section per changed file is noise.

**Focus on the *changes*. Push long-lived information to the docs.** Some content belongs only in a PR description: what connects the old and new versions of the code — why the old shape was wrong, what a reviewer should be suspicious of, how to read the diff. Everything else belongs in the codebase itself, with the description carrying a short summary of it. Terms and concepts the PR introduces get a one-line gloss so the body still reads on its own.

**Where the body and a doc would say the same thing, cite and summarize in a sentence.** One sentence handing off to a doc or a code pointer beats a restatement: the restatement drifts from the doc by the next change, and then two places disagree. Use **absolute `blob/` URLs pinned to the PR's head branch** (`https://github.com/OWNER/REPO/blob/<head-branch>/path.md#anchor`) — a repo-relative link in a *description* does not resolve against the PR's branch, so a link to content the PR itself introduces lands on a 404; the branch-pinned form follows the branch as it moves and keeps working after a squash-merge deletes it only if the repo retains closed-PR branches, which is acceptable for a review-time map. Point at a heading rather than a section number — `§3.9` rots at the next reordering, which is why the repo's reference conventions require a heading. `./ci.sh doc_refs` does **not** check descriptions (nor anything under `.claude/`), so confirm by hand that the heading exists and the anchor spells it correctly.

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
2. **Check against the rules.** Is the title an imperative? Does the opening stand alone? Is the section order a reading order? Is anything durable stated only here — or restated here from a comment the diff itself adds? Then count the words and compare against the budget; if the draft is over, the cut comes from what the codebase already says, not from the reviewer's map.
3. **Check against the diff.** Re-verify every name, count, and list. A compression pass introduces factual errors more readily than a draft does — an over-cut description that says a pass is affected when the diff exempts it is worse than a long one.

## Posting and updating

`gh pr edit` fails with exit code 1 on a Projects (classic) deprecation warning even when the update succeeds. Use the REST API, and PATCH the title alongside the body:

```bash
gh api repos/OWNER/REPO/pulls/PR_NUMBER --method PATCH \
  --field title="..." --field body="$(cat body.md)" --jq '{number,title}'
```

Read the result back (`gh pr view N --json title,body`) — a PATCH that lands still leaves the branch's own commit message untouched, which is harmless here (a squash-merge takes the PR's title and body, not the branch commit's) but worth saying out loud rather than leaving the author to discover the two have diverged.

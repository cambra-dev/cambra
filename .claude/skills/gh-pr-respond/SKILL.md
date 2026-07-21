---
name: gh-pr-respond
description: Fetch PR review comments via shell scripts and produce a structured response plan for each comment — either a code fix, a direct reply, or a clarifying question. Use when a user asks to respond to PR review comments or review feedback on a pull request.
---

# PR Comment Response

## Overview

This skill fetches GitHub PR review comments and produces a per-comment action plan: a code fix, a drafted reply, or a clarifying question.

## Script

A single consolidated script lives alongside this skill:

```
.claude/skills/gh-pr-respond/gh_pr_comments.sh <pr_number> [--mode active|pending|all] [--org ORG] [--repo REPO] [--author AUTHOR] [-v|--verbose]
```

- **`--mode active`** (default) — unresolved review threads, via GraphQL
- **`--mode pending`** — pending (draft) review comments for `--author` (default: `groundlar`), via REST
- **`--mode all`** — both active and pending

Defaults: `org=cambra-dev`, `repo=cambra`, `author=groundlar`.

## Workflow

### 1. Parse Scope

From the user's invocation:

- **PR number**: required — ask if not provided.
- **Mode**: `active` (default), `pending`, or `all`.
- **Author**: default `groundlar`, overridable via `--author <name>`.

### 2. Fetch Comments

Run the script from the skill directory. Use `$SKILL_DIR` or a path relative to the repo root:

```bash
.claude/skills/gh-pr-respond/gh_pr_comments.sh <pr> --mode <mode> [--author <author>] [-v]
```

Always pass `-v` for pending comments to get diff hunk context.

### 3. Read Referenced Code

For each comment that references a file and line, read that file at and around the cited line to understand full context before deciding on a response.

### 4. Produce Response Plan

For each comment thread, choose exactly one action:

- **Fix**: describe the specific code change needed (or make the fix directly if small and unambiguous).
- **Reply**: draft a response explaining current code rationale, design intent, or correcting a misunderstanding.
- **Question**: ask the reviewer for more information when the comment is ambiguous.

### 5. Output Format

```
## PR #<N> — Comment Response Plan

### Active Threads   (or Pending Comments, or both)

#### <file>:<line> — @<author>
> <comment body>

**Action**: Fix | Reply | Question
**Draft**: <response or fix description>
---
```

If mode is `all`, output Active Threads first, then Pending Comments under separate `###` headings.

## Example Triggers

- `/gh-pr-respond 42` — active threads on PR #42
- `/gh-pr-respond 42 --mode pending` — pending comments only
- `/gh-pr-respond 42 --mode all` — both active and pending
- `/gh-pr-respond 42 --author skylar` — pending comments by author `skylar`

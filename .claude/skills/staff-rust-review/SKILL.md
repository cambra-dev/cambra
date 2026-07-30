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
- **Performance**: Pipelining, parallelization, and dataflow efficiency (per Cambra's goals).
- **Prioritize Impactful Feedback**
  - Ignore whitespace nits in markdown files (such as trailing whitespace).

### 4. Review Output

Provide a structured response:

- **Executive Summary**: High-level verdict on the changes.
- **Architectural Notes**: How well the code aligns with the design.
- **Detailed Feedback**: Specific line-by-line or function-level observations, categorized by "Critical," "Important," or "Nit."
- **Next Steps**: Recommended actions or refactors.

If there are Critical or Important findings, attempt to produce an illustrative, concise test case which exercises the gap in logic or bug, or comment why this is challenging to do.

## Example Triggers

- "Review the head commit against docs/design.md"
- "Give me a staff review of HEAD~2.. using docs/design.md"
- "Review branch feature-x"

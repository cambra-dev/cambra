# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

For architecture and design context, see [docs/design.md](docs/design.md).

## Build Commands

```bash
cargo fmt        # Run formatter
cargo build      # Build the project
cargo clippy --all-targets -- -D warnings # Run linter (part of the ci script)
ci.sh --fix      # Runs complete CI suite, auto-formatting first
cargo test       # Run all tests
cargo test <name>  # Run a specific test by name
```

## General Instructions

### When in Doubt, Ask
Stop and ask before proceeding when:
- A task is ambiguous and you could reasonably interpret it multiple ways
- Something in the code contradicts what you'd expect from the design docs or CLAUDE.md
- You're about to make a non-trivial architectural choice that isn't covered by existing patterns
- A test fails in a way that suggests the premise of the task may be wrong
- You're unsure whether a change should be made in the interpreter, lowering, or both

Prefer a short clarifying question over a best-guess implementation. Getting it wrong wastes more time than pausing to confirm.

### Skills
- `/pyast` — Quick reference for `rustpython_parser` AST types (ExprKind, StmtKind, Operator, Constant, etc.)

### Code Comments
Comment all objects (modules, structures and their fields, functions, etc) thoroughly, but concisely, in accordance with rustdoc best practices. For internal comments (for example, inside functions), strongly prefer commenting the _why_ of things, only commenting _what_ if the code is confusing and cannot be reasonably simplified.

### Workflow
After making code changes, run the formatter before running the code; prefer running the linter after ensuring the project builds, then progress to CI.

Before creating a PR, update the appropriate docs to reflect the changes. This includes `docs/design.md`, `docs/plan.md`, and other `*/design-*.md` files close to source files that were changed.

### Compact instructions
When you are using compact, focus on test output and code changes.

### Git Conventions
- Do not add "Co-Authored-By" lines attributing credit to AI models to commit messages.
- When making changes, verify the freshness of the local repo by fetching and comparing the diff. The following commands do this, if there are differences, warn the user and ask the user whether they would like to pull or rebase.
   1. `git fetch origin`
   2. `git log master..origin/master --pretty=format:"%h%x09%an%x09%ad%x09%s"| head -n 20`

### Stacked PRs with git-spice
This repo uses [git-spice](https://abhinav.github.io/git-spice/) (`gs`) for stacked PRs. Workflow for creating a new PR in a stack:

1. Create a new git branch with the commit message containing the desired title and body for the PR.
2. Submit the PR: `gs branch submit --fill --no-draft` (uses commit message for title/body), or explicitly: `gs branch submit --title "..." --body "..." --no-draft`
3. Post nav comments: `gs stack submit --update-only`

`gs stack submit` discovers existing PRs by branch name and adds a navigation comment linking all PRs in the stack. Use `--update-only` to skip prompts for branches without PRs yet.

To view the current stack: `gs log long`

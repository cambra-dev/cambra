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

### Rendering CCL ASTs in conversation
When showing a CCL AST in chat or when writing code comments — walking through an example, illustrating what a pass sees, comparing before/after a rewrite — **render it in symbolic form** (the output shape of `ccl::symbolic::symbolic` / `symbolic_typed`). The whole reasoning surface here is the algebra; symbolic notation makes that legible at a glance.

Vocabulary, matching `src/ccl/symbolic.rs`:

- **Apply**: `arg ▷ func` (left-assoc; `a ▷ f ▷ g` means `(a ▷ f) ▷ g`).
- **Apply with `Proj` as function**: postfix dot-access. `t ▷ .0` → `t.0`, `rec ▷ .name` → `rec.name`.
- **Compose**: `f ≫ g ≫ h`.
- **Lambda**: `λ x → body`. With annotated param: `λ x : T → body`. With refinement: `λ x : {T | predicate} → body` (or `{??? | predicate}` when the param type is `Hole`/`Infer`). After our cleanup of the `Refined(...)` wrapper, the predicate appears bare inside the braces — do not write `{T | Refined(p)}`.
- **Let**: `let x = e in body`.
- **Aggregate**: `Sum(input)`, `Max(input)`, etc. — the kind name then parens.
- **Loop**: `loop i = 0 over xs do body` (single accumulator), `loop (x = 0, y = 1) over xs do (x, y)` (multi).
- **Literals**: `1`, `true`/`false`, `"str"`, `unit`.
- **Binops**: standard infix with precedence parens (`a + b`, `x == y`, `p and q`, etc.).
- **Unary**: `-x`, `not x`.
- **Tuples / lists / records**: `(a, b)`, `[a, b, c]`, `{name: a, age: b}`.
- **List mappings** (in lowered list literals): `[0 ↦ e0, 1 ↦ e1]`.

Types (from `Display for Type` in `src/ccl/mod.rs`):

- **Function**: `(T ⇒ U)`.
- **Refinement**: `{T | predicate}` — predicate is rendered via `symbolic`.
- **UIntRange**: `[0, N]`, or `∅` when empty.
- **Hole**: `_`.
- **Infer**: `?N` (where `N` is the variable id).
- **DataSource**: `source(name)`.
- **Union**: `T1 | T2`.

Do **not** write `Apply { function: ..., argument: ... }`, `Apply(f, x)`, `Compose([f, g])`, or other constructor-style forms — those are AST node names, not the rendering. Do **not** fall back to source syntax when the point is what the *AST* looks like. Only deviate if explicitly asked (e.g. "show me the Debug form", "give me the source").

When the type matters to the point being made (e.g. showing a domain refinement that triggers operator dispatch), include type annotations via `symbolic_typed`-style suffixes: `expr:type`.

### Workflow
After making code changes, run the formatter before running the code; prefer running the linter after ensuring the project builds, then progress to CI.

When planning, include updates to the appropriate docs to reflect the changes; validate the docs are up to date before creating a PR. This includes `docs/design.md`, `docs/plan.md`, and other `*/design-*.md` files close to source files that were changed.

### Compact instructions
When you are using compact, focus on test output and code changes.

### Git Conventions
- Do not add "Co-Authored-By" lines attributing credit to AI models to commit messages.
- When making changes, verify the freshness of the local repo by fetching and comparing the diff. The following commands do this, if there are differences, warn the user and ask the user whether they would like to pull or rebase.
   1. `git fetch origin`
   2. `git log master..origin/master --pretty=format:"%h%x09%an%x09%ad%x09%s"| head -n 20`

### Updating PR descriptions
`gh pr edit --body` fails with exit code 1 due to a Projects (classic) deprecation warning, even when the body update would otherwise succeed. Use the REST API instead:

```bash
gh api repos/OWNER/REPO/pulls/PR_NUMBER --method PATCH --field body="..." --jq .number
```

### Stacked PRs with git-spice
This repo uses [git-spice](https://abhinav.github.io/git-spice/) (`gs`) for stacked PRs. Workflow for creating a new PR in a stack:

**Option A — git-spice branch creation** (stage changes first, then):
```bash
gs branch create -m "commit message"   # creates branch + commit in one step
gs branch submit --fill --no-draft     # submit to GitHub
gs stack submit --update-only          # add nav comments to all PRs in stack
```

**Option B — plain git then track** (more control over commit flow):
```bash
git checkout -b <branch-name>
git add <files> && git commit -m "..."
gs branch track --base <parent-branch>   # register with git-spice
gs branch submit --fill --no-draft
gs stack submit --update-only
```

Notes:
- Prefer `gs branch create` over `git checkout -b` for branch creation — if `spice.branchCreate.prefix` is configured, git-spice will apply it automatically, avoiding manual prefix guessing.
- For a PR stacked on `main`, `--base main` is implicit; for stacked PRs use `--base <parent-branch>`.
- `gs stack submit` discovers existing PRs by branch name and adds navigation comments. Use `--update-only` to skip prompts for branches without PRs yet.
- To view the current stack: `gs log long`

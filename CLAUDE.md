# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

For architecture and design context, see [docs/design.md](docs/design.md).

## Build Commands

```bash
cargo fmt        # Run formatter
cargo build      # Build the project
cargo clippy --all-targets -- -D warnings            # Lint (debug) — fast inner-loop check, NOT the full gate
cargo clippy --release --all-targets -- -D warnings  # Lint (release) — CI runs this too; catches debug-only (cfg(debug_assertions)) breakage the debug pass misses
./ci.sh --fix    # Authoritative gate: fmt + BOTH clippy passes + doc + tests, auto-formatting first. Must pass before pushing a PR.
cargo test -q --no-fail-fast      # Run all tests
cargo test <name>  # Run a specific test by name
```

CI lints in **both** debug and release (`ci_clippy` and `ci_clippy_release` in `ci.sh`). Passing the plain debug `cargo clippy` is **not** sufficient — a release-only failure (e.g. a `#[cfg(debug_assertions)]`-gated item referenced by ungated code) passes locally but fails GitHub CI. Run `./ci.sh` to catch both.

## General Instructions

### When in Doubt, Ask
Stop and ask before proceeding when:
- A task is ambiguous and you could reasonably interpret it multiple ways
- Something in the code contradicts what you'd expect from the design docs or CLAUDE.md
- You're about to make a non-trivial architectural choice that isn't covered by existing patterns
- A test fails in a way that suggests the premise of the task may be wrong
- You're unsure whether a change should be made in the interpreter, lowering, or both

Prefer a short clarifying question over a best-guess implementation. Getting it wrong wastes more time than pausing to confirm.

### How to think about changes to this codebase

Cambra is a language and database substrate, not product code. Two things follow:

**The substrate quality compounds.** In a language/type-system/database every piece interacts with every other piece, so complexity multiplies rather than adds. Tradeoffs that are fine in product code (a small special case here, a bit of duplication there) compound non-linearly here. Default toward simpler primitives even when the local diff is slightly larger.

**Abstractions are first-class deliverables.** Your task is to make Cambra better, not just to complete the current session's instructions. Cambra is a deliberately-constructed framework of abstractions; introducing well-justified ones is often the work itself, not something to avoid. An abstraction is justified if it either (a) makes a concept that is currently implicit in the code or semantics *explicit*, or (b) collapses a recurring shape that is already being duplicated. It is **not** justified by "this would be cleaner" or "we might need this later" — the signal has to come from the existing code or the existing semantics, not from aesthetics or speculation.

Specific decision points where this matters:

- **Adding a special case.** Before adding `if foo == X { ... } else { normal path }` or its equivalent, pause and ask whether the existing abstraction is wrong — whether `X` is revealing internal structure of the type/operation/concept that hasn't been named yet. The special case is sometimes right; the bar is "I noticed and decided," not "I noticed and didn't think about it."

- **Recurring shapes.** When the same structural pattern appears across what should be unrelated constructs, flag it — even if you are not going to refactor it as part of the current task. A comment, a note in the PR, or a question to the user is what keeps the signal from being lost. Silently leaving it for the third or fourth duplication is how complexity compounds.

- **New concepts threaded through layers.** When a task requires adding a new concept or special case across several layers (parse → lower → type-check → eval, say), stop and ask whether the concept is real or whether you are papering over a missing distinction. Threading something widely is expensive and hard to undo; a clarifying question first is usually worth it.

- **Bug fixes that reveal structural problems.** If a bug is a symptom of a structural confusion (a missing distinction, a wrong abstraction, a leaky boundary), the surface fix paves over it. If the structural fix is too big to fold into the current task, flag it as a separate change — neither silently widen the scope nor silently ignore it.

- **Defensive checks at internal boundaries.** Add `debug_assert!`, `unreachable!`, and explicit invariant checks at pass boundaries and between modules where load-bearing assumptions live. Don't go overboard — assertions that just restate what the type system already enforces are noise. Add them where the invariant is real but not type-enforced: pass output shapes, module-boundary preconditions, post-conditions on internal helpers. Name what the invariant *is* in the assertion message.

### Skills
- `/pyast` — Quick reference for `rustpython_parser` AST types (ExprKind, StmtKind, Operator, Constant, etc.)

### Code Comments
Comment when the *why* is non-obvious — a hidden constraint, a load-bearing invariant, an unusual choice, behavior that would surprise a reader. Skip comments when a good name and a clear signature already convey the intent. Follow rustdoc best practices for public items; don't manufacture docstrings to hit a coverage target.

Avoid comments that describe the history of the codebase.  Comments should explain how and why the code works.  If there is an alternative approach that seems reasonable but doesn't work, it's ok to describe that, but the comments should always fully make sense just by looking at the current version of the code.

### Rendering CCL ASTs in conversation
When showing a CCL AST in chat or when writing code comments — walking through an example, illustrating what a pass sees, comparing before/after a rewrite — **render it in symbolic form** (the output shape of `ccl::symbolic::symbolic` / `symbolic_typed`). The whole reasoning surface here is the algebra; symbolic notation makes that legible at a glance.

Vocabulary, matching `src/ccl/symbolic.rs`:

- **Apply**: `arg ▷ func` (left-assoc; `a ▷ f ▷ g` means `(a ▷ f) ▷ g`).
- **Apply with `Proj` as function**: postfix dot-access. `t ▷ .0` → `t.0`, `rec ▷ .name` → `rec.name`.
- **Compose**: `f ≫ g ≫ h`.
- **Lambda**: `λ x → body`. With annotated param: `λ x : T → body`. With refinement: `λ x : {T | predicate} → body` (an unresolved refined base renders by its own type form: `{_ | predicate}` for a `Hole`, `{?N | predicate}` for an `Infer`). The refinement rides the param *type* — there is no separate lambda refinement slot — and the predicate appears bare inside the braces; do not write `{T | Refined(p)}`.
- **Let**: `let x = e in body`.
- **Aggregate**: `Sum(input)`, `Max(input)`, etc. — the kind name then parens.
- **LetRec** (causal mutually-recursive group): `letrec b₁ = e₁; …; bₙ = eₙ in body` (bindings separated by `; `) — what the mutability-elimination phases (`mut_elim` for overwrite, `channelize` for append) emit before loop planning.
- **Transact** (the domain-parameterized recurrence carrier `plan_loops` produces from a `LetRec`): `transact (k₁ = init₁, …) { [reads]⇒[writes] over source do body; … }` — the store keys with their seeds, then one writer per site (its read/write footprint, iteration source, and decision body). `Transact` is born by loop planning (`plan_loops`, in `planning/loops.rs`) *after* `lambda_elim` (its writer bodies are already point-free); op-conversion dispatches on the domain: a concrete iteration extent → `Recurse`, `Txn` → the commit operator. (The former `Loop` carrier is retired — do not render it.)
- **Literals**: `1`, `true`/`false`, `"str"`, `unit`.
- **Binops**: standard infix with precedence parens (`a + b`, `x == y`, `p and q`, etc.).
- **Unary**: `-x`, `not x`.
- **Tuples / lists**: `(a, b)`, `[a, b, c]`.
- **Records**: a record **value** renders with parens + colons — `(name: a, age: b)` (the renderer emits `(field: val, …)`, `src/ccl/symbolic.rs`); a record **type** renders with braces + colons — `{name: T, age: U}` (`Display for Type`, `src/ccl/mod.rs`). Braces are for types only; do not render a record value with braces.
- **List mappings** (in lowered list literals): `[0 ↦ e0, 1 ↦ e1]`.

Types (from `Display for Type` in `src/ccl/mod.rs`):

- **Function**: `(T ⇒ U)` for a compute function (capability domain); `(T ⤇ U)` (plain-text `|=>`) for a data function (extent domain — the domain is the data map, joins must be lossless). Kind is inferred by the solver (`FunKind::Var`, resolved at coalesce — see `src/ccl/brainstorm/2026-07-15-kind-inference.md`) and `Display` renders it live: a data collection shows `⤇`, a capability (and an unresolved kind var) `⇒`. One benign quirk — an identity comprehension `[x for x in xs]` collapses to `iterate ≫ xs` and displays `⇒` though it denotes a collection.
- **Sigma** (in-flight, same stack): `Σ{D0, D1} ⤇ V` — a data function whose extent is exactly one of the listed choices; with a live witness binder, `(Σ n ∈ {D0, D1}. n ⤇ V)`.
- **Refinement**: `{T | predicate}` — predicate is rendered via `symbolic`.
- **UIntRange**: `[0, N]`, or `∅` when empty.
- **Hole**: `_`.
- **Infer**: `?N` (where `N` is the variable id).
- **DataSource**: `source(name)`.
- **Union**: `T1 | T2`.
- **Feed**: `Feed[T]` — a transient deferred-output type inference threads and `channelize` erases.
- **Mut**: `Mut[value, domain]` — a transient mutable-variable type inference threads and the mutability-elimination phases (`mut_elim`) erase; the domain is an induction extent or `Txn`. Its `HistoryKind` is `Overwrite` (the last-write-wins merge law); the append-law sibling is `Feed`'s `Append` kind.
- **Txn**: `Txn` — the (nullary) transaction-commit sequencing domain, the second slot of a `Mut[V, Txn]` register.

Do **not** write `Apply { function: ..., argument: ... }`, `Apply(f, x)`, `Compose([f, g])`, or other constructor-style forms — those are AST node names, not the rendering. Do **not** fall back to source syntax when the point is what the *AST* looks like. Only deviate if explicitly asked (e.g. "show me the Debug form", "give me the source").

When the type matters to the point being made (e.g. showing a domain refinement that triggers operator dispatch), include type annotations via `symbolic_typed`-style suffixes: `expr:type`.

### Metavariable notation in design docs
When design-doc prose and inline pseudo-code mix CCL syntax with meta-theoretic placeholders (stand-ins for any specific term, type, or predicate), italicize the placeholders using Unicode mathematical italic characters. Single-letter Latin: `𝑎`–`𝑧` (U+1D44E–U+1D467, lowercase, for term/value metas) and `𝐴`–`𝑍` (U+1D434–U+1D44D, uppercase, for type metas). One gotcha — italic lowercase `ℎ` lives at the legacy codepoint U+210E, not in the contiguous range. Digit subscripts: `₀`–`₉` (U+2080–U+2089) for indexed variants (`𝐷₁`, `𝐶₂`). Multi-character placeholders (`body`, `arg`, `param`, `predicate`, ...) and concrete identifiers (`xs`, `__gb_k`, `key_fn`, ...) stay upright. The convention applies to inline pseudo-code in backticks and to prose mentions, **not** to fenced code blocks — those represent literal source and stay in regular characters throughout. String literals (`"x"`, `"k"`) are also literal, not metavariables, and stay upright. Stars/underscores for italics don't work inside backticks; the Unicode math characters are pre-rendered italic glyphs that render correctly in any modern Markdown viewer.

### Symbolic notation for types and terms
Use the symbolic forms below in prose and inline pseudo-code (not in fenced code blocks, which represent literal source):

- **Function type with named binder** (`Type::Fun` with `name: Some(_)`): `(𝑥: 𝐴) ⇒ 𝐵`. `𝑥` is bound in `𝐵`.
- **Function type with no named binder** (`Type::Fun` with `name: None`): `𝐴 ⇒ 𝐵`.
- **Data function type** (`FunKind::Data`, kind inferred and rendered live): `𝐴 ⤇ 𝐵`, named-binder form `(𝑥: 𝐴) ⤇ 𝐵` — same associativity as `⇒`; the bar reads "the domain is a fixed extent". **Σ type** (formation live; witness binder still dormant): `Σ 𝑛 ∈ {𝐷₀, 𝐷₁}. 𝑛 ⤇ 𝑉` — a dependent sum over candidate extents; anonymous-witness shorthand `Σ{𝐷₀, 𝐷₁} ⤇ 𝑉`.
- **Refinement type**: `{𝑥: 𝑇 | 𝑝(𝑥)}` — standard subset-type notation.
- **Lambda** (term): `λ 𝑥 → body`. The `→` after the binder separates the parameter from the body.
- **Forward apply** (term level): `𝑎 ▷ 𝑓` means `𝑓(𝑎)`.
- **Forward compose** (term level): `𝑓 ≫ 𝑔` means `λ 𝑥 → 𝑔(𝑓(𝑥))`.

Both `⇒` and `→` are right-associative. They are distinct: `⇒` is for *types*, `→` is for *terms* (lambda body separator and similar). Don't mix them.

Do not render type information as Rust struct syntax (e.g., `Fun { name: Some("k"), domain: K, codomain: ... }`) when prose calls for symbolic notation — the struct form is appropriate inside fenced ` ```rust ` blocks that show actual Rust source, but in symbolic positions use the arrow / refinement-bracket notation above.

### Workflow
After making code changes, run the formatter before running the code; prefer running the linter after ensuring the project builds. **Before creating or pushing a PR, run `./ci.sh` and confirm it is clean** — GitHub CI gates on the same checks, and `./ci.sh` runs the parts no single `cargo` command covers: clippy in *both* debug and release mode plus the doc build. A green debug `cargo clippy` is not enough (see Build Commands above).

When planning, include updates to the appropriate docs to reflect the changes; validate the docs are up to date before creating a PR. This includes `docs/design.md`, `docs/plan.md`, and other `*/design-*.md` files close to source files that were changed.

### Compact instructions
When you are using compact, focus on test output and code changes.

### Git Conventions
- Do not attribute authorship to AI tools or models anywhere git records it — neither commit messages nor PR descriptions. This covers any form the attribution takes: `Co-Authored-By:` trailers, "Generated with"/"Created with" footers (e.g. `🤖 Generated with [Claude Code]`), tool/model names in the body, and any future variant. The rule is the intent (no AI authorship credit), not a fixed list of strings. PR descriptions matter because this repo squash-merges, so the PR body becomes the commit message on the main branch.
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

> **Before submitting:** run `./ci.sh` and confirm it passes. `gs branch submit` runs no checks of its own, so this is the only gate before GitHub CI sees the branch — and it lints in both debug *and* release (an un-run release clippy pass is the most common way CI fails after a green local `cargo clippy`).

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

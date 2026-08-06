# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

For architecture and design context, see [docs/design.md](docs/design.md).

## Build Commands

```bash
cargo fmt        # Run formatter
cargo build      # Build the project
cargo clippy --all-targets -- -D warnings            # Lint (debug) — fast inner-loop check, NOT the full gate
cargo clippy --release --all-targets -- -D warnings  # Lint (release) — CI runs this too; catches debug-only (cfg(debug_assertions)) breakage the debug pass misses
./ci.sh fast     # Inner-loop gate: fmt + debug clippy (lib/bins) + tests. Skips the release clippy pass, doc, shellcheck, doc-refs. ~1/3 the time of the full gate — use this while iterating.
./ci.sh --fix    # Authoritative gate: fmt + ALL FOUR clippy passes + doc + tests, auto-formatting first. Must pass before pushing a PR.
cargo test -q --no-fail-fast      # Run all tests
cargo test <name>  # Run a specific test by name
```

For the tight edit→check loop, prefer `./ci.sh fast` (or a bare `cargo test <name>`) over the full `./ci.sh`; run the full gate before pushing.

CI lints in **four configurations**, because each one compiles code the others do not. Passing the plain debug `cargo clippy` is **not** sufficient; run `./ci.sh` to catch all four.

| Pass | What only it compiles |
|---|---|
| `ci_clippy` | debug, all targets — the baseline |
| `ci_clippy_release` | release: `#[cfg(debug_assertions)]`-gated items referenced by ungated code |
| `ci_clippy_serde` | the default-OFF `serde` feature — the hand-written wire `Serialize` impls |
| `ci_clippy_lib` | the library with **no** features: the other three unify the self dev-dependency's `test-helpers` into the lib, so only this one compiles the configuration a consumer builds |

The pattern is the same in each case: a configuration that nothing compiles is a configuration that rots, and the failure is silent rather than loud — `--all-targets` hides the `test-helpers` gap exactly as a default-off feature hides the serde one.

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

### Code Comments

Comment when the *why* is non-obvious — a hidden constraint, a load-bearing invariant, an unusual choice, behavior that would surprise a reader. Skip comments when a good name and a clear signature already convey the intent. Follow rustdoc best practices for public items; don't manufacture docstrings to hit a coverage target.

Avoid comments that describe the history of the codebase.  Comments should explain how and why the code works.  If there is an alternative approach that seems reasonable but doesn't work, it's ok to describe that, but the comments should always fully make sense just by looking at the current version of the code.

### Referencing docs and sections

Cross-references into the docs are checked by `./ci.sh doc_refs` (Markdown
links/anchors between docs, and `<name>.md` citations in Rust comments *and* doc
prose) and a broken one fails CI. Two rules keep references from rotting:

**Use a checkable form.**

- *Doc → doc*: a Markdown link — `[text](path.md#anchor)`. The `#anchor` is
  validated against the target's headings. This is the preferred form in a doc:
  it survives the same renames a quoted title does, and the anchor is checked too.
- *Code → doc*: the doc path followed by the section's **exact heading text** in
  double quotes, adjacent — e.g. ``see `src/ccl/design/ir.md`, "Application
  shape"``. The checker confirms the quoted title is a real heading. Prefer this
  over an anchor fragment in code: a title survives section reordering and reads
  as prose. (Details and the citation grammar: `.github/scripts/doc-refs/README.md`.)

Either form must name a **heading**, spelled **exactly**. A bold paragraph
lead-in is not citable (no anchor, nothing to check) — promote it to a heading in
the same change if you need to point at it. An abbreviated title (`"The model"`
for *The model: histories and causal recursion*) reads fine and fails the check;
that gap is where silent rot lives. A quoted title in doc prose is checked
wherever it sits, including hanging off a link — both halves of `[mutability.md](mutability.md), "The model"` are validated. <!-- doc-refs-ignore: illustrative -->

**Never reference something uncheckable — it rots silently because nothing can
validate it.** Specifically avoid:

- *Section numbers across docs* (`§4.6`) — cite the heading (anchor link or
  quoted title) instead. (Existing `§`-refs are being migrated to links as a
  follow-up; don't add new ones.) A `§` *followed by a quoted title* is now
  checked on the title, but the number in front of it still isn't — drop it.
- *Transient identifiers*, which are wrong almost immediately: PR-stack positions
  ("the PR above/below", "PR 3 in the stack"), PR/issue numbers used as if they
  were stable section markers, review-comment numbers, and dated notes ("the
  2026-06-29 notes"). If the thing you want to point at is durable, give it a
  heading and cite that; if it isn't, inline the substance instead of pointing.

When you rename a heading, `./ci.sh doc_refs` flags every inbound link and
citation, from code and from docs — update them in the same change.

### Rendering CCL ASTs in conversation

When showing a CCL AST in chat or when writing code comments — walking through an example, illustrating what a pass sees, comparing before/after a rewrite — **render it in symbolic form** (the output shape of `ccl::symbolic::symbolic` / `symbolic_typed`). The whole reasoning surface here is the algebra; symbolic notation makes that legible at a glance.

Vocabulary, matching `src/ccl/symbolic.rs`:

- **Apply**: `arg ▷ func` (left-assoc; `a ▷ f ▷ g` means `(a ▷ f) ▷ g`).
- **Apply with `Proj` as function**: postfix dot-access. `t ▷ .0` → `t.0`, `rec ▷ .name` → `rec.name`.
- **Compose**: `f ≫ g ≫ h`.
- **Lambda**: `λ x → body`. With annotated param: `λ x : T → body`. With refinement: `λ x : {T | predicate} → body` (an unresolved refined base renders by its own type form: `{_ | predicate}` for a `Hole`, `{?N | predicate}` for an `Infer`). The refinement rides the param *type* — there is no separate lambda refinement slot — and the predicate appears bare inside the braces; do not write `{T | Refined(p)}`.
- **Let**: `let x = e in body`.
- **Aggregate**: `Sum(input)`, `Max(input)`, etc. — the kind name then parens.
- **LetRec** (causal mutually-recursive group): `letrec b₁ = e₁; …; bₙ = eₙ in body` (bindings separated by `;`) — what the mutability-elimination phases (`mut_elim` for overwrite, `channelize` for append) emit before loop planning.
- **Transact** (the domain-parameterized recurrence carrier `plan_loops` produces from a `LetRec`): `transact (k₁ = init₁, …) { [reads]⇒[writes] over source do body; … }` — the store keys with their seeds, then one writer per site (its read/write footprint, iteration source, and decision body). `Transact` is born by loop planning (`plan_loops`, in `planning/loops.rs`) *after* `lambda_elim` (its writer bodies are already point-free); op-conversion dispatches on the domain: a concrete iteration extent → the `InductionStore` changelog, `Txn` → the commit operator. `Transact` is the only recurrence carrier — every loop and every transaction renders as one.
- **Literals**: `1`, `true`/`false`, `"str"`, `unit`.
- **Binops**: standard infix with precedence parens (`a + b`, `x == y`, `p and q`, etc.).
- **Unary**: `-x`, `not x`.
- **Tuples / lists**: `(a, b)`, `[a, b, c]`.
- **Records**: a record **value** renders with parens + colons — `(name: a, age: b)` (the renderer emits `(field: val, …)`, `src/ccl/symbolic.rs`); a record **type** renders with braces + colons — `{name: T, age: U}` (`Display for Type`, `src/ccl/mod.rs`). Braces are for types only; do not render a record value with braces.
- **List mappings** (in lowered list literals): `[0 ↦ e0, 1 ↦ e1]`.
- **Variant construction / destructuring**: `` `tag(payload) `` — a backtick introduces an arm, in a term as in a type. **Arm names are lowercase**: an arm is a constructor (a term), and `Caps` in CHL means a type. A `match` arm destructures with the same form: ``match d { `commit(w) → w + 1 ; `abort(a) → 0 }``. The payload is always written in a *term*, including the nullary constructor's (`` `abort(unit) ``), because the `Unit`-valued expression sitting there is a real node — unlike an arm's type, where "stores nothing" is the whole content.
- **Variant project / wrap** (the point-free eliminator and constructor `lambda_elim` mints): ``variant_project(`commit)``, ``variant_wrap(`commit)`` — the tag keeps its backtick inside the builtin.

Types (from `Display for Type` in `src/ccl/mod.rs`):

- **Function**: `(T ⇒ U)` for a compute function; `(T ⤇ U)` (plain-text `|=>`) for a data function (the domain is the data map, joins must be lossless). FunKind is inferred by the solver (`FunKind::Var`, resolved at coalesce — see `src/ccl/design/type-inference.md` §4.6) and `Display` renders it live: a data collection shows `⤇`, a capability (and a genuinely unresolved kind var) `⇒`. A comprehension over a **let-bound** collection source resolves to `⤇` just like one over a literal source (`let x = [1,2,3] in [y + 10 for y in x]` is `⤇`) — its domain is a data collection.
- **Sigma** (in-flight, same stack): `Σ{D0, D1} ⤇ V` — a data function whose domain is exactly one of the listed choices; with a live witness binder, `(Σ n ∈ {D0, D1}. n ⤇ V)`.
- **Refinement**: `{T | predicate}` — predicate is rendered via `symbolic`.
- **UIntRange**: `[0, N]`, or `∅` when empty.
- **Hole**: `_`.
- **Infer**: `?N` (where `N` is the variable id).
- **DataSource**: `source(name)`.
- **Variant** (a tagged sum): ``{`arm1{T1} | `arm2{T2}}`` — braces around the arms, each arm introduced by a backtick with its stored type in braces. An arm that stores nothing is written bare (``{`commit{Int} | `abort}``, not `` `abort{Unit} ``), and a payload that is itself brace-delimited reuses those braces rather than doubling them (``{`pair{a: Int, b: Int}}``). A single-arm sum is just the general form with one arm: ``{`none}``, ``{`some{Int}}``.
- **Union** (an *anonymous positional* sum, what `++` / `CollectionUnion` produces — not a tagged variant): `T1 | T2`. Its `Index` keys carry no user-meaningful information, so it renders as a flat join with no arm tags.
- **Feed**: `Feed(T)` — a transient deferred-output type inference threads and `channelize` erases.
- **Mut**: `Mut(value, domain)` — a transient mutable-variable type inference threads and the mutability-elimination phases (`mut_elim`) erase; the domain is an induction extent or `Txn`. Its `HistoryKind` is `Overwrite` (the last-write-wins merge law); the append-law sibling is `Feed`'s `Append` kind.
- **Txn**: `Txn` — the (nullary) transaction-commit sequencing domain, the second slot of a `Mut(V, Txn)` register.

Do **not** write `Apply { function: ..., argument: ... }`, `Apply(f, x)`, `Compose([f, g])`, or other constructor-style forms — those are AST node names, not the rendering. Do **not** fall back to source syntax when the point is what the *AST* looks like. Only deviate if explicitly asked (e.g. "show me the Debug form", "give me the source").

When the type matters to the point being made (e.g. showing a domain refinement that triggers operator dispatch), include type annotations via `symbolic_typed`-style suffixes: `expr:type`.

### Metavariable notation in design docs

When design-doc prose and inline pseudo-code mix CCL syntax with meta-theoretic placeholders (stand-ins for any specific term, type, or predicate), italicize the placeholders using Unicode mathematical italic characters. Single-letter Latin: `𝑎`–`𝑧` (U+1D44E–U+1D467, lowercase, for term/value metas) and `𝐴`–`𝑍` (U+1D434–U+1D44D, uppercase, for type metas). One gotcha — italic lowercase `ℎ` lives at the legacy codepoint U+210E, not in the contiguous range. Digit subscripts: `₀`–`₉` (U+2080–U+2089) for indexed variants (`𝐷₁`, `𝐶₂`). Multi-character placeholders (`body`, `arg`, `param`, `predicate`, ...) and concrete identifiers (`xs`, `__gb_k`, `key_fn`, ...) stay upright. The convention applies to inline pseudo-code in backticks and to prose mentions, **not** to fenced code blocks — those represent literal source and stay in regular characters throughout. String literals (`"x"`, `"k"`) are also literal, not metavariables, and stay upright. Stars/underscores for italics don't work inside backticks; the Unicode math characters are pre-rendered italic glyphs that render correctly in any modern Markdown viewer.

### Symbolic notation for types and terms

Use the symbolic forms below in prose and inline pseudo-code (not in fenced code blocks, which represent literal source):

- **Function type with named binder** (`Type::Fun` with `name: Some(_)`): `(𝑥: 𝐴) ⇒ 𝐵`. `𝑥` is bound in `𝐵`.
- **Function type with no named binder** (`Type::Fun` with `name: None`): `𝐴 ⇒ 𝐵`.
- **Data function type** (`FunKind::Data`, kind inferred and rendered live): `𝐴 ⤇ 𝐵`, named-binder form `(𝑥: 𝐴) ⤇ 𝐵` — same associativity as `⇒`; the bar reads "the domain is the data". **Σ type** (formation live; witness binder still dormant): `Σ 𝑛 ∈ {𝐷₀, 𝐷₁}. 𝑛 ⤇ 𝑉` — a dependent sum over candidate domains; anonymous-witness shorthand `Σ{𝐷₀, 𝐷₁} ⤇ 𝑉`.
- **Refinement type**: `{𝑥: 𝑇 | 𝑝(𝑥)}` — standard subset-type notation.
- **Lambda** (term): `λ 𝑥 → body`. The `→` after the binder separates the parameter from the body.
- **Forward apply** (term level): `𝑎 ▷ 𝑓` means `𝑓(𝑎)`.
- **Forward compose** (term level): `𝑓 ≫ 𝑔` means `λ 𝑥 → 𝑔(𝑓(𝑥))`.

Both `⇒` and `→` are right-associative. They are distinct: `⇒` is for *types*, `→` is for *terms* (lambda body separator and similar). Don't mix them.

Do not render type information as Rust struct syntax (e.g., `Fun { name: Some("k"), domain: K, codomain: ... }`) when prose calls for symbolic notation — the struct form is appropriate inside fenced ` ```rust ` blocks that show actual Rust source, but in symbolic positions use the arrow / refinement-bracket notation above.

### Workflow

After making code changes, run the formatter before running the code; prefer running the linter after ensuring the project builds. While iterating, `./ci.sh fast` (fmt + debug clippy + tests) is the quick check — roughly a third of the full gate's time. **Before creating or pushing a PR, run the full `./ci.sh` and confirm it is clean** — GitHub CI gates on the same checks, and `./ci.sh` runs the parts no single `cargo` command covers and that `fast` skips: the other three clippy configurations (release, `serde`, lib-only) plus the doc build. A green debug `cargo clippy` (or `./ci.sh fast`) is not enough (see Build Commands above).

When planning, include updates to the appropriate docs to reflect the changes; validate the docs are up to date before creating a PR. This includes `docs/design.md` and other `*/design-*.md` files close to source files that were changed.

### Compact instructions

When you are using compact, focus on test output and code changes.

### Git Conventions

- Do not attribute authorship to AI tools or models anywhere git records it — neither commit messages nor PR descriptions. This covers any form the attribution takes: `Co-Authored-By:` trailers, "Generated with"/"Created with" footers (e.g. `🤖 Generated with [Claude Code]`), tool/model names in the body, and any future variant. The rule is the intent (no AI authorship credit), not a fixed list of strings. PR descriptions matter because this repo squash-merges, so the PR body becomes the commit message on the main branch.
- When making changes, verify the freshness of the local repo by fetching and comparing the diff. The following commands do this, if there are differences, warn the user and ask the user whether they would like to pull or rebase.
   1. `git fetch origin`
   2. `git log master..origin/master --pretty=format:"%h%x09%an%x09%ad%x09%s"| head -n 20`
- Writing a PR description — or a commit description, which `gh pr create --fill` copies into the body verbatim — is the `pr-description` skill's job (`.claude/skills/pr-description/SKILL.md`): summary first, then a review guide, sub-linear length, the Markdown mechanics, and the `gh api` workaround for editing a posted body. Load it rather than working from memory.

### Stack Management & Rebasing (jj vs git-spice)

Engineers in this repo manage and rebase stacked PRs using either `jj` (jujutsu) or `git-spice` (`gs`). **Default to trying `jj` first** for stack operations, but consult your memory files, environment-specific prompts, or the current repository state (e.g. active git branches vs. jj bookmarks) to verify if the engineer is actively using `git-spice`.

#### Option A: Stacked PRs with git-spice

This repo uses [git-spice](https://abhinav.github.io/git-spice/) (`gs`) for stacked PRs when working with standard Git branches. Workflow for creating a new PR in a stack:

> **Before submitting:** run `./ci.sh` and confirm it passes. `gs branch submit` runs no checks of its own, so this is the only gate before GitHub CI sees the branch — and it lints in all four configurations (an un-run release clippy pass is the most common way CI fails after a green local `cargo clippy`).

**git-spice branch creation** (stage changes first, then):

```bash
gs branch create -m "commit message"   # creates branch + commit in one step
gs branch submit --fill --no-draft     # submit to GitHub
gs stack submit --update-only          # add nav comments to all PRs in stack
```

**Plain git then track** (more control over commit flow):

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

#### Option B: Rebasing a stack with jujutsu (jj)

`jj` (jujutsu, currently 0.43) is initialized over the same git repo as git-spice. Unlike `git rebase`/`gs`, jj records conflicts *inside* commits and does not stop mid-rebase, so the whole stack moves in one command and you resolve conflicts afterward, bottom→tip, with automatic propagation.

Mental model:

- jj **bookmarks** are git branches. Each git-spice branch head appears as a bookmark on the matching commit; `main@origin`, `<name>@origin` are remote-tracking. `@` is the working-copy commit (itself a real, editable commit).
- Every operation is recorded in the **op log** — `jj op log` — and any prior state is recoverable with `jj op restore <op-id>`. This is your undo; there is no "rebase --abort" because a rebase never leaves you detached.

Workflow (validated rebasing the inspector stack onto `dmills/txn-mutability`):

1. **Sync + validate.** `jj git fetch`. If a local bookmark is stale, move it: `jj bookmark set <name> -r <name>@origin --allow-backwards`. Cross-check the stack against `gs ll` — every git-spice branch should be a bookmark on the expected commit, with matching per-branch commit counts.
2. **Check base lineage before rebasing.** `jj log -r 'main..<target>'` and confirm the target descends from what your stack assumes. A target that predates a layout-affecting change your stack is written against (e.g. a directory rename) causes *silent* structural breakage jj will not flag as a conflict — verify the file layout matches (`git ls-tree`) first.
3. **Checkpoint.** `jj op log --limit 1` — note the op id to `jj op restore` back to if needed.
4. **Rebase the whole stack in one command:** `jj rebase -s <stack-base-change-id> -d <target-bookmark>`. `-s` moves that commit and *all* descendants (bookmarks + working copy ride along). Conflicts are recorded in-commit; jj reports which commits are conflicted and does not stop.
5. **Resolve bottom→tip.** `jj edit <change-id>` enters a commit; `jj resolve --list` lists its conflicts; edit files to remove markers (jj uses git-style `<<<<<<<`/`>>>>>>>` plus diff-style `%%%%%%%`/`+++++++` hunks). Run `cargo build` before moving up — resolving a parent auto-propagates and shrinks descendants' conflicts. Aim for each stack commit (each is a PR head) to build green.
6. **Verify at the tip:** `jj edit <tip-bookmark>` then `./ci.sh` (the same authoritative gate as any push — all four clippy passes + doc + tests).

Gotchas:

- **Conflict propagation:** after `jj rebase`, *every* descendant of the first conflicted commit shows "(conflict)" — most of that is the parent's conflict propagated down, and clears when you resolve the parent. Don't resolve the same hunk in five commits; fix it once at the lowest commit that owns it.
- **Required-field fallout is not a conflict:** adding a required struct field low in the stack breaks construction sites in files with no textual conflict (including the new base's code). These surface as compile errors, not conflict markers — resolve them in the commit that introduced the field so that commit builds.
- **Stale editor diagnostics:** LSP/rustc diagnostics can lag the working copy after `jj edit` hops between commits — a reported conflict marker or missing field may be from a commit you already moved off of. Confirm ground truth with `jj status` / `grep` / a real `cargo build` before acting on a surprising diagnostic.
- **Bookmarks ride their commits automatically** — never move them by hand during a rebase.
- **No concurrent mutators:** never run two agents (or an agent + yourself) mutating the same jj working copy at once — the shared commit graph will corrupt. Read-only investigation in parallel is fine.
- jj resolves are amended in place (no separate "continue" step); the op log is the only undo you need.

### Parallel Workspaces (Multi-Tasking)

This repository supports parallel development using native `jj` workspaces (the `jj` equivalent of Git worktrees).

- **Create a workspace:** `jj workspace add ../cambra-feature --name feature`
- **List workspaces:** `jj workspace list`
- **Remove a workspace:** `jj workspace forget <name>` then `rm -rf ../path`

#### Stale Working Copies

Because all workspaces share a unified history graph, editing or rebasing an ancestor commit from Workspace A will cause Workspace B to become "stale" if its current commit depends on that ancestor.

If a workspace reports it is stale or blocks commands, synchronize its filesystem by running:

```bash
jj workspace update-stale

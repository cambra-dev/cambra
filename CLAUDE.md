# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Cambra is a programming language implementing a new paradigm that abstracts over memory, threads, and connections. Programs use Python-like syntax with for-comprehensions, which lowers to CCL (Cambra Core Language) for type-checking and interpretation.

The interpreter uses **dataflow semantics** with a producer/consumer protocol instead of term-wise beta reduction. This enables streaming execution with pipelining, parallelization, and vectorization.

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
After making changes, run the formatter before running code; prefer running the linter after ensuring the project builds, then progress to CI.

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



## Architecture

### Pipeline

```
Python source → parse (rustpython_parser) → lower (lowering.rs) → CCL operators → subscribe() → producer/consumer dataflow
```

### Core Concepts

- **Operators**: Stateless components corresponding to program syntax (`Literal`, `BinOp`, `Var`, `VarRef`, `Lambda`). Each has an `extent` (the set of values it can produce — equivalent to its type) and a `subscribe()` method that creates a producer/consumer pair for execution.
- **Producers/Consumers**: Runtime stateful objects created from operators via `subscribe()`. Form a dataflow graph where notifications flow downstream and data is pulled upstream.
- **Guards**: Predicates representing regions (subsets of extents). Three roles: *intent* (consumer registers interest), *yield* (producer announces data ready), and *obsolete* (consumer retracts interest). Yield guards grow monotonically — each notification is a superset of all previous ones.
- **ColumnValue**: Columnar batch of values with optional `parent_indices` for alignment across nesting levels. Enables vectorized execution; `expand()` composes indices through scan chains for multi-level alignment.

### Producer/Consumer Protocol

```rust
// Operator creates the dataflow link
Operator::subscribe(intent_guard, consumer, var_scope) -> Producer

// Producer pushes progress notifications to consumer
Consumer::notify(Notification::NewData)       // Data available — call get()
Consumer::notify(Notification::Yield(guard))  // Region complete, no new data

// Consumer pulls data and manages lifecycle
Producer::get() -> GetResult { column_value, yield_guard }
Producer::release(obsolete_guard) -> Guard
```

### Variable System

- **Var**: Variable definition (name + extent). Not an Operator — cannot be subscribed directly.
- **VarRef**: Variable reference (implements Operator). Looks up the variable in `VarScope` at subscribe time.
- **VarProducer**: Runtime subscription bridging a variable's source to its consumers. Source is one of:
  - `Argument` — lambda applied to an argument; wraps the argument's producer
  - `Iteration` — lambda consumed directly (e.g. by aggregation or output); iterates over extent with predicate filtering
- **VarScope**: Linked list for variable lookup with parent chaining. `lookup_variable()` returns both the subscription and the chain of intermediate iteration variables for alignment composition.

### Key Files

- `src/lib.rs` — Public API; wraps `rustpython_parser` for Python parsing
- `src/interpreter/` — CCL interpreter module:
  - `mod.rs` — `Consumer`, `Producer`, `Operator` traits and protocol types
  - `types.rs` — `Guard`, `Extent`, `Value`, `Notification`, `GetResult`, `ColumnValue`
  - `var.rs` — `Var`, `VarRef`, `VarProducer`, `VarScope`, `VarSource`
  - `lambda.rs` — `Lambda` operator and `LambdaProducer`
  - `literal.rs` — `Literal` operator
  - `binop.rs` — `BinOp` operator (Add, Sub, Mul, FloorDiv)
- `src/lowering.rs` — Lowers Python AST to CCL operators (constants, binops, let-bindings, list literals)
- `src/pretty_ast.rs` — Tree-style pretty-printer for rustpython AST (debugging aid)

## Design Reference

See `design.md` for the full specification including syntax, denotational/operational semantics, and detailed CCL operator descriptions.

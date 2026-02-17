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

When planning or implementing changes, prefer asking a user clarifying questions as necessary rather than making assumptions.

Comment all objects (modules, structures and their fields, functions, etc) thoroughly, but concisely, in accordance with rustdoc best practices. For internal comments (for example, inside functions), strongly prefer commenting the _why_ of things, only commenting _what_ if the code is confusing and cannot be reasonably simplified.

After making changes, run the formatter before running code; prefer running the linter after ensuring the project builds, then progress to CI.



## Architecture

### Core Concepts

- **Operators**: Stateless components corresponding to program syntax (`Literal`, `Var`, `VarRef`, `Lambda`)
- **Producers/Consumers**: Runtime stateful objects created from operators via `subscribe()`
- **Guards**: Predicates representing regions (subsets of extents); monotonically growing
- **Extents**: The set of values a term can take on (equivalent to types)
- **ColumnValue**: Columnar data with `parent_indices` for alignment across nesting levels

### Producer/Consumer Protocol

```rust
Consumer::notify(yield_guard)      // Producer notifies consumer data is ready
Producer::get() -> ColumnValue     // Consumer requests data synchronously
Producer::release(obsolete_guard)  // Consumer retracts interest in a region
```

### Key Files

- `src/lib.rs` - Public API and Python parsing
- `src/interpreter.rs` - CCL interpreter (operators, producers, consumers, guards, extents)

### Skills

- `/pyast` — Quick reference for `rustpython_parser` AST types (ExprKind, StmtKind, Operator, Constant, etc.)

### Variable System

Variables have two modes:
- **Bound**: Lambda applied to argument (`(\x. body) arg`) - VarSub wraps argument's producer
- **Scanning**: Lambda aggregated (`sum(\x. body)`) - VarSub iterates over extent, executes joins

`VarScope` is a linked list for variable lookup with parent chaining. For nested scans, `lookup_variable()` returns both the variable and the chain of inner scans for alignment composition.

### Guard Monotonicity Contract

Each `notify()` call provides a yield guard that is a superset of all previous yield guards. This allows storing a single yield guard rather than tracking history.

## Implementation Status

See `PLAN.md` for detailed progress. Currently implementing Step 7b (scan chain for multi-level alignment). Core operators (Literal, Var, VarRef, Lambda) and columnar values are complete. Application operator and join execution are next.

Simultaneously we're working on a lowering implementation, transforming the Python AST into CCL operators.

## Design Reference

See `design.md` for the full specification including syntax, denotational/operational semantics, and detailed CCL operator descriptions.


## Compact instructions

When you are using compact, focus on test output and code changes.

## Git Conventions

- Do not add "Co-Authored-By" lines attributing credit to AI models to commit messages.
- When making changes, verify the freshness of the local repo by fetching and comparing the diff. The following commands do this, if there are differences, warn the user and ask the user whether they would like to pull or rebase.
   1. `git fetch origin`
   2. `git log master..origin/master --pretty=format:"%h%x09%an%x09%ad%x09%s"| head -n 20`

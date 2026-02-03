# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
cargo build      # Build the project
cargo test       # Run all tests
cargo test <name>  # Run a specific test by name
```

## Project Overview

Pototo is a programming language implementing a new paradigm that abstracts over memory, threads, and connections. Programs use Python-like syntax with for-comprehensions, which lowers to PCL (Pototo Core Language) for type-checking and interpretation.

The interpreter uses **dataflow semantics** with a producer/consumer protocol instead of term-wise beta reduction. This enables streaming execution with pipelining, parallelization, and vectorization.

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
- `src/interpreter.rs` - PCL interpreter (operators, producers, consumers, guards, extents)

### Variable System

Variables have two modes:
- **Bound**: Lambda applied to argument (`(\x. body) arg`) - VarSub wraps argument's producer
- **Scanning**: Lambda aggregated (`sum(\x. body)`) - VarSub iterates over extent, executes joins

`VarScope` is a linked list for variable lookup with parent chaining. For nested scans, `lookup_variable()` returns both the variable and the chain of inner scans for alignment composition.

### Guard Monotonicity Contract

Each `notify()` call provides a yield guard that is a superset of all previous yield guards. This allows storing a single yield guard rather than tracking history.

## Implementation Status

See `PLAN.md` for detailed progress. Currently implementing Step 7b (scan chain for multi-level alignment). Core operators (Literal, Var, VarRef, Lambda) and columnar values are complete. Application operator and join execution are next.

## Design Reference

See `design.md` for the full specification including syntax, denotational/operational semantics, and detailed PCL operator descriptions.

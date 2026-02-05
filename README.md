# Cambra

Cambra is a programming language that implements a new programming paradigm, abstracting over low-level concepts like memory, threads, and connections. This allows programmers to focus on program logic, non-functional requirements, and high-level architectural decisions.

## Key Features

- **Python-like Syntax**: Programs are written in a Pythonic syntax that uses for-comprehensions for collection-level logic. This syntax is lowered to the Cambra Core Language (CCL) for type checking and interpretation.

- **Dataflow Semantics**: The operational semantics uses a producer/consumer interface that enables streaming dataflow execution with pipelining, parallelization, and vectorization. Progress is tracked through punctuations sent through this interface.

- **Dependently-Typed Functional Core**: The denotational semantics is a pure, dependently-typed, functional language. The core language (CCL) includes literals, variables, records, unions, lambdas, let-bindings, application, and pattern matching.

## Current Status

The project is currently in active development.

See [PLAN.md](PLAN.md) for detailed implementation status and [design.md](design.md) for the full design specification.

## Building

```bash
cargo build
```

## CI

CI runs formatting, linting, and tests via GitHub Actions on every push to `main` and on pull requests.

To run the full CI suite locally:

```bash
./ci.sh
```

You can also run individual checks:

```bash
./ci.sh fmt      # Check formatting
./ci.sh clippy   # Run lints
./ci.sh test     # Run tests
```


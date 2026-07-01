# Cambra

Cambra is a programming language that abstracts over low-level concerns like memory, threads, and connections, letting programmers focus on logic and high-level architecture. Programs are written in a Pythonic syntax (Cambra High-level Language, "CHL") that lowers to a small core language (Cambra Core Language, "CCL"), where execution uses streaming dataflow semantics rather than term-wise beta reduction.

## Docs

- [Design](docs/design.md) — language overview, CHL, CCL, execution pipeline
- [Plan](docs/plan.md) — implementation roadmap and status
- [Developer setup](docs/developer-setup-checklist.md)

## Building & CI

```bash
cargo build          # build
cargo test           # run tests
./ci.sh              # full CI suite (fmt + clippy in debug & release + doc + tests)
./ci.sh --fix        # same, with auto-formatting
```

## Usage

```bash
cargo run -- <input_file>
```

### Web Inspector

Pass `--inspect` to start a live web dashboard that shows the program's CHL AST, CCL operator graph, and runtime producer state:

```bash
cargo run -- --inspect program.cambra
```

The inspector defaults to port 8080. To use a different port:

```bash
cargo run -- --inspect=9090 program.cambra
```

After the program finishes, the process stays alive so you can browse the dashboard at `http://localhost:<port>`. Press Ctrl+C to exit.

# cambra-inspector

The user-facing **Cambra program inspector**: a small, read-only web app that
compiles a Cambra (CHL) program once and serves an interactive view of it —
the source alongside one IR tree pane per compiler stage, cross-linked by true
node→node provenance.

It is the second member of the Cambra workspace (the first is the `cambra`
compiler/engine crate at the repo root). This crate owns the pieces the core
deliberately keeps out — **serde + `serde_json`**, the **`tiny_http` server**,
and, once the frontend lands, the embedded bundle — so that `cargo build -p cambra`
compiles zero serde (serde is an optional, default-off feature on `cambra`).

> **Milestone 1 — static, no values.** The inspector currently shows the
> *program*, not an execution: types and structure, no runtime values or ticks.
> It is strictly read-only (no mutation endpoints).

> **Transport edge only.** What is here: the crate, the JSON edge, the server's
> `/api/*` routes, and the golden-fixture corpus with its gates. The `web/`
> frontend this README describes, its `GET /` route and its committed bundle
> land separately.

## What it shows

- **Source pane** — the CHL source in a read-only editor, with hover types,
  Ctrl/Cmd-click goto-definition, and diagnostic squiggles.
- **IR panes** — one collapsible tree per pipeline stage, ordered
  upstream → downstream: **pre-inference**, **post-inference**,
  **post-channelize**, **post-as-of-read**, **post-lambda-elim** and
  **post-planning**. The set is the compiler's `PANES` table, not a list this
  crate keeps.
- **Cross-stage links** — clicking in any pane highlights the corresponding
  node(s) in every other pane and the source span(s) they trace to, following
  the retained per-phase provenance (identity ∪ explicit remaps such as the
  monomorphization fan-out). Pre-inference holes (`_`/`?N`) show their resolved
  downstream type on hover.
- **Refinement predicates** — a predicate riding a type slot is a node like any
  other, reaching the frontend as a child edge marked `predicate`, so it links
  across panes the same way the value tree does.

See `web/README.md` for the full interaction table and the <!-- doc-refs-ignore -->
frontend's design.

## Architecture

Compile once at startup, serve a static snapshot; every interaction is then a
pure client-side lookup over that one payload (no per-request recompilation, no
round-trips).

- The **read-only model** — the payload shape and the span/name indices it is
  built from — lives in the **core** crate at `cambra::inspector_model` (behind
  its serde-gated wire types). That is the serde-isolation boundary. It answers
  no positional query: every lookup is the frontend's, over the shipped tables.
- **This crate is the transport edge**: it turns the model into JSON
  (`snapshot_json`) and serves it over HTTP (`src/server.rs`). The frontend that
  consumes it, and the route that delivers it, land with the frontend.

```
client ──HTTP──> cambra-inspector (this crate) ──> cambra::inspector_model ──> cambra compiler
     GET /api/snapshot   tiny_http + serde_json         read-only model          compile_program
```

## Directory contents

| Path | What it is |
|---|---|
| `Cargo.toml` | Crate manifest. Depends on `cambra` (with `serde`), `serde_json`, `tiny_http`. |
| `src/lib.rs` | The transport edge: `snapshot_json` (build-then-serialize), and `wire_check`, the structural validator both the crate's tests and `tests/goldens.rs` assert the wire against. |
| `src/server.rs` | The `tiny_http` server, its routes, and `snapshot_body_pretty` (what `--dump-snapshot` prints). |
| `src/main.rs` | The `cambra-inspector` binary / CLI (run the server, or `--dump-snapshot`). |
| `web/src/__fixtures__/` | The golden snapshot corpus the frontend's tests read, blessed by `scripts/regen-fixtures.sh`. The frontend itself lands separately. |
| `examples/` | Sample CHL programs (`arithmetic.chl`, `list_min.chl`, `polymorphic.chl`, `defer_*.chl`, `type_error.chl`, …). |

## Running it

From the repo root, with `cargo`:

```bash
cargo run -p cambra-inspector -- path/to/program.chl        # serves on :8080
cargo run -p cambra-inspector -- program.chl --port 9000    # custom port
cargo run -p cambra-inspector                               # no arg: a built-in demo program
```

Then open <http://localhost:8080> — the server binds loopback only. Ready-made
programs live in `examples/`:

```bash
cargo run -p cambra-inspector -- cambra-inspector/examples/polymorphic.chl
```

Routes: `GET /api/snapshot` (the full model — degrades gracefully to source +
diagnostics on a compile failure) and `GET /api/diagnostics`.

### One-shot snapshot dump

`--dump-snapshot` prints the `/api/snapshot` JSON to stdout and exits, **without
starting the (never-exiting) server**:

```bash
cargo run -q -p cambra-inspector -- cambra-inspector/examples/list_min.chl --dump-snapshot
```

Use this for inspecting the payload or regenerating the frontend's golden test
fixtures (see the README in the web frontend's `__fixtures__` directory).

A dump is always the whole payload. `scripts/fixtures.manifest` maps each
committed fixture to the example program it is dumped from, and a program whose
payload is too large to commit is asserted structurally in `tests/goldens.rs`
instead of being pinned as a document.

## Testing

**Backend (Rust):**

```bash
cargo test -p cambra-inspector          # this crate's tests
cargo test -p cambra                    # the read-only model + provenance substrate
```

The model, indices, and query logic are tested in the `cambra` core
(`src/inspector_model/`); this crate's tests cover the JSON shape and the server
response bodies.

**Frontend (TypeScript):** see `web/README.md`. In short, from <!-- doc-refs-ignore -->
`web/`: `npm run typecheck`, `npm run test` (vitest), `npm run build`.

> ⚠ **Never run `npm run dev`** — it starts a Vite server that does not exit.
> All of `typecheck` / `test` / `build` are one-shot. The `cambra-inspector`
> server itself also blocks forever; for scripted inspection use
> `--dump-snapshot` instead.

## Design & background

Design rationale, decisions, and the implementation plan live in the **design
vault** (a separate repository), under the `program-inspector` project — e.g.
`multi-pane-inspector.md` (the N-stage view + provenance chain), <!-- doc-refs-ignore: vault doc -->
`provenance-substrate.md` (stable IDs + side-table provenance), <!-- doc-refs-ignore: vault doc -->
`m1-static-plan.md`, and `api-surface.md`. The as-built provenance description <!-- doc-refs-ignore: vault docs -->
also lives next to the core code at `src/ccl/design/provenance.md`.

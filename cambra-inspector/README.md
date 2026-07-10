# cambra-inspector

The user-facing **Cambra program inspector**: a small, read-only web app that
compiles a Cambra (CHL) program once and serves an interactive view of it —
the source alongside one IR tree pane per compiler stage, cross-linked by true
node→node provenance.

It is the second member of the Cambra workspace (the first is the `cambra`
compiler/engine crate at the repo root). This crate owns the pieces the core
deliberately keeps out — **serde + `serde_json`**, the **`tiny_http` server**,
and the **embedded CodeMirror frontend** — so that `cargo build -p cambra`
compiles zero serde (serde is an optional, default-off feature on `cambra`).

> **Milestone 1 — static, no values.** The inspector currently shows the
> *program*, not an execution: types and structure, no runtime values or ticks.
> It is strictly read-only (no mutation endpoints).

## What it shows

- **Source pane** — the CHL source in a read-only editor, with hover types,
  Ctrl/Cmd-click goto-definition, and diagnostic squiggles.
- **IR panes** — one collapsible tree per pipeline stage, ordered
  upstream → downstream (currently **post-desugar** and **post-inference**).
- **Cross-stage links** — clicking in any pane highlights the corresponding
  node(s) in every other pane and the source span(s) they trace to, following
  the retained per-pass provenance (identity ∪ explicit remaps such as the
  monomorphization fan-out). Pre-inference holes (`_`/`?N`) show their resolved
  downstream type on hover.

See [`web/README.md`](web/README.md) for the full interaction table and the
frontend's design.

## Architecture

Compile once at startup, serve a static snapshot; every interaction is then a
pure client-side lookup over that one payload (no per-request recompilation, no
round-trips).

- The **read-only model** — the snapshot shape, span/name indices, and query
  handlers — lives in the **core** crate at `cambra::inspector_model` (behind
  its serde-gated wire types). That is the serde-isolation boundary.
- **This crate is the transport edge + delivery vehicle**: it turns the model
  into JSON (`snapshot_json` / `diagnose_json`), serves it over HTTP
  (`src/server.rs`), and embeds the built frontend bundle.

```
browser ──HTTP──> cambra-inspector (this crate) ──> cambra::inspector_model ──> cambra compiler
        GET /            tiny_http + serde_json          read-only model           compile_program
```

## Directory contents

| Path | What it is |
|---|---|
| `Cargo.toml` | Crate manifest. Depends on `cambra` (with `serde`), `serde_json`, `tiny_http`. |
| `src/lib.rs` | The transport edge: `snapshot_json` / `diagnose_json` (build-then-serialize). |
| `src/server.rs` | The `tiny_http` server, its routes, and `snapshot_body` (used by `--dump-snapshot`). |
| `src/main.rs` | The `cambra-inspector` binary / CLI (run the server, or `--dump-snapshot`). |
| `web/` | The CodeMirror 6 / TypeScript frontend. **Has its own [README](web/README.md)** — build, tests, module layout, and the byte↔char bridge. |
| `web/dist/index.html` | The built, self-contained single-file bundle, committed and `include_str!`-embedded by the server (so `cargo build` needs no Node). |
| `examples/` | Sample CHL programs (`arithmetic.chl`, `list_min.chl`, `polymorphic.chl`, `defer_*.chl`, `type_error.chl`, …). |
| `scripts/dump_spans.py` | Frontend-independent debug tool: prints each IR node's span↔CCL mapping + a coverage summary, to isolate "the inspector won't link X" to backend (no span) vs frontend (span present, not wired). |

## Running it

From the repo root, with `cargo`:

```bash
cargo run -p cambra-inspector -- path/to/program.chl        # serves on :8080
cargo run -p cambra-inspector -- program.chl --port 9000    # custom port
cargo run -p cambra-inspector                               # no arg: a built-in demo program
```

Then open <http://localhost:8080>. Ready-made programs live in `examples/`:

```bash
cargo run -p cambra-inspector -- cambra-inspector/examples/polymorphic.chl
```

Routes: `GET /` (the frontend), `GET /api/snapshot` (the full model — degrades
gracefully to source + diagnostics on a compile failure), `GET /api/diagnostics`.

### One-shot snapshot dump

`--dump-snapshot` prints the `/api/snapshot` JSON to stdout and exits, **without
starting the (never-exiting) server**:

```bash
cargo run -q -p cambra-inspector -- cambra-inspector/examples/list_min.chl --dump-snapshot
```

Use this for inspecting the payload, piping into `scripts/dump_spans.py`, or
regenerating the frontend's golden test fixtures (see `web/src/__fixtures__/README.md`).

## Testing

**Backend (Rust):**

```bash
cargo test -p cambra-inspector          # this crate's tests
cargo test -p cambra                    # the read-only model + provenance substrate
```

The model, indices, and query logic are tested in the `cambra` core
(`src/inspector_model/`); this crate's tests cover the JSON shape and the server
response bodies.

**Frontend (TypeScript):** see [`web/README.md`](web/README.md). In short, from
`web/`: `npm run typecheck`, `npm run test` (vitest), `npm run build`.

> ⚠ **Never run `npm run dev`** — it starts a Vite server that does not exit.
> All of `typecheck` / `test` / `build` are one-shot. The `cambra-inspector`
> server itself also blocks forever; for scripted inspection use
> `--dump-snapshot` instead.

**Span/provenance debugging:** `scripts/dump_spans.py` (see its header for
usage — it can manage the server for you or read a dumped/curled snapshot).

## Editing the frontend

`web/dist/index.html` is committed on purpose and embedded at compile time, so
the binary works without Node. **After changing anything under `web/src/`,
rerun `npm run build` and commit the regenerated bundle** (see the "Committed
bundle" section of [`web/README.md`](web/README.md)).

## Design & background

Design rationale, decisions, and the implementation plan live in the **design
vault** (a separate repository), under the `program-inspector` project — e.g.
`multi-pane-inspector.md` (the N-stage view + provenance chain),
`provenance-substrate.md` (stable IDs + side-table provenance),
`m1-static-plan.md`, and `api-surface.md`. The as-built provenance description
also lives next to the core code at `cambra/src/ccl/design-provenance.md`.

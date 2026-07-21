# The Cambra program inspector

A read-only web view of a compiled Cambra program: the source alongside one IR
tree pane per retained compiler pane, cross-linked by true node→node
provenance. It is served by the `cambra` binary itself — `cambra --inspect-only
<program>` — and this directory holds the CodeMirror frontend it embeds and
serves.

> **Milestone 1 — static, no values.** The inspector shows the *program*, not an
> execution: types and structure, no runtime values or ticks. It is strictly
> read-only (no mutation endpoints).

## What it shows

- **Source pane** — the CHL source in a read-only editor, with hover types,
  Ctrl/Cmd-click goto-definition, and diagnostic squiggles.
- **IR panes** — one collapsible tree per pipeline pane, ordered
  upstream → downstream: **pre-inference**, **post-inference**,
  **post-channelize**, **post-as-of-read**, **post-lambda-elim** and
  **post-planning**. The set is the compiler's `PANES` table, not a list the
  inspector keeps.
- **Cross-pane links** — clicking in any pane highlights the corresponding
  node(s) in every other pane and the source span(s) they trace to, following
  the retained per-phase provenance shipped dense (self-edges included, so a
  monomorphization fan-out is just the non-self edges). Pre-inference holes
  (`_`/`?N`) show their resolved downstream type on hover.
- **Refinement predicates** — a predicate riding a type slot is a node like any
  other, reaching the frontend as a child edge marked `predicate: true` rather
  than a positional one, so it links across panes the same way the value tree
  does. One predicate term shared by several type slots is one entry of the
  pane's node table that several edges name.

See [`web/README.md`](web/README.md) for the full interaction table and the
frontend's design.

## Architecture

Compile once at startup, serve a static snapshot; every interaction is then a
pure client-side lookup over that one payload (no per-request recompilation, no
round-trips).

Both halves of the server live in the `cambra` crate, because the thing being
inspected is the compiler:

- The **read-only model** — the payload shape and the span/name indices it is
  built from — is `src/inspector_model/`. It answers no positional query: every
  lookup is the frontend's, over the shipped tables.
- The **transport and delivery vehicle** is `src/inspector_server/`: it turns
  the model into JSON (`snapshot_json`), serves it over HTTP (`serve.rs`), and
  embeds the built frontend bundle. `wire_check.rs` is the structural validator
  both those tests and `tests/inspector_goldens.rs` assert the wire against.

```
browser ──HTTP──> cambra --inspect-only ──> inspector_server ──> inspector_model ──> compile_program
        GET / + /api/snapshot            tiny_http + serde_json    read-only model
```

## Directory contents

| Path | What it is |
|---|---|
| `web/` | The CodeMirror 6 / TypeScript frontend. **Has its own [README](web/README.md)** — build, tests, module layout, and the byte↔char bridge. |
| `web/dist/index.html` | The built, self-contained single-file bundle, committed and `include_str!`-embedded by the server (so `cargo build` needs no Node). |
| `web/src/__fixtures__/` | The golden snapshot corpus the frontend's tests read, blessed by `scripts/regen-fixtures.sh`. |
| `scripts/fixtures.manifest` | Which gallery program each committed fixture is dumped from. |
| `scripts/regen-fixtures.sh` | The re-bless path, and the `ci.sh` drift gate's regenerator. |

The programs are the demo gallery's (`tests/programs/`, tabulated in
[docs/demo-programs.md](../docs/demo-programs.md)) — the inspector has no
example corpus of its own.

## Running it

From the repo root:

```bash
cargo run -- tests/programs/polymorphic/program.cambra --inspect-only        # serves on :8080
cargo run -- program.cambra --inspect-only=9000                              # custom port
```

Then open <http://localhost:8080> — the server binds loopback only.

Routes: `GET /` (the frontend), `GET /api/snapshot` (the full model — degrades
gracefully to source + diagnostics on a compile failure), `GET /api/diagnostics`.

`--inspect-only` compiles the program and does not run it. Its sibling
`--inspect` runs the program and serves the live runtime dashboard
(`src/web_inspector.rs`) instead; the two are exclusive.

### One-shot snapshot dump

`--dump-snapshot` prints the `/api/snapshot` JSON to stdout and exits, **without
starting the (never-exiting) server**:

```bash
cargo run -q -- tests/programs/list_min/program.cambra --dump-snapshot
```

Use this for inspecting the payload or regenerating the frontend's golden test
fixtures (see the README in the web frontend's `__fixtures__` directory).

A dump is always the whole payload. `scripts/fixtures.manifest` maps each
committed fixture to the gallery program it is dumped from, and a program whose
payload is too large to commit is asserted structurally in
`tests/inspector_goldens.rs` instead of being pinned as a document.

## Testing

**Backend (Rust):** `cargo test -p cambra` — the model and provenance substrate
(`src/inspector_model/`), the JSON shape and server bodies
(`src/inspector_server/`), and the golden corpus
(`tests/inspector_goldens.rs`).

**Frontend (TypeScript):** see [`web/README.md`](web/README.md). In short, from
`web/`: `npm run typecheck`, `npm run test` (vitest), `npm run build`.

> ⚠ **Never run `npm run dev`** — it starts a Vite server that does not exit.
> All of `typecheck` / `test` / `build` are one-shot. `--inspect-only` also
> blocks forever; for scripted inspection use `--dump-snapshot` instead.

## Editing the frontend

`web/dist/index.html` is committed on purpose and embedded at compile time, so
the binary works without Node. **After changing anything under `web/src/`, rerun
`npm run build` and commit the regenerated bundle** — `ci.sh web` compares it
against a fresh build (see the "Committed bundle (R7)" section of
[`web/README.md`](web/README.md)).

## Design & background

Design rationale, decisions, and the implementation plan live in the **design
vault** (a separate repository), under the `program-inspector` project — e.g.
`multi-pane-inspector.md` (the N-stage view + provenance chain), <!-- doc-refs-ignore: vault doc -->
`provenance-substrate.md` (stable IDs + side-table provenance), <!-- doc-refs-ignore: vault doc -->
`m1-static-plan.md`, and `api-surface.md`. The as-built provenance description <!-- doc-refs-ignore: vault docs -->
also lives next to the core code at `src/ccl/design/provenance.md`.

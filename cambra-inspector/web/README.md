# Cambra Inspector — web frontend

The CodeMirror 6 frontend for the Cambra program inspector. It is a small,
read-only single-page app: on load it fetches `/api/snapshot` from the
`cambra-inspector` server and renders the program source alongside one IR tree
pane per pipeline stage (post-desugar, post-inference), with interactive
cross-linking across all panes via the stage provenance graph.

## Principle: snapshot-first, all client-side

Every interaction is a **pure client-side lookup over the `/api/snapshot`
payload the client already loaded** — zero round-trips, works offline. The
frontend calls exactly one endpoint (`/api/snapshot`) and never talks to the
backend again; hover types, goto-definition, squiggles, and source↔tree
highlighting are all computed from indices derived from that one payload.

> **Ship-everything-once is an M1 decision, not a permanent one.** It is correct
> *because M1 is static* — the whole model (source + typed IR + source map) is
> cheap, immutable, and computed once at compile time. The post-M1 live surface
> **cannot** ship everything: runtime values are `O(N·K·T)` and recomputed on
> demand, so they move to per-query/streaming over the CQRS transport (the
> `meta.tick` / value-summary seams are the forward-compat hooks). The `Store`
> here builds all indices eagerly in its constructor from one payload; adding
> live values is **not** a matter of populating those seams — it will require
> reworking the store into an incremental/streaming model. That is an expected,
> additive migration (the static read model is a true subset of the live one),
> but flagged here so the eager-load architecture is understood as scoped to M1.

## Running the inspector

The frontend is served by the `cambra-inspector` binary, which compiles one
program at startup and serves its snapshot. From the repo root:

```bash
cargo run -p cambra-inspector -- path/to/program.chl       # serves on :8080
cargo run -p cambra-inspector -- program.chl --port 9000   # custom port
```

Then open `http://localhost:8080`. With no file argument a small built-in demo
program is served. Ready-made examples live in `cambra-inspector/examples/`
(`arithmetic.chl`, `scopes.chl`, `comprehension.chl`, `accumulator.chl`,
`type_error.chl`).

The page loads the whole model once (`GET /api/snapshot`); every interaction
after that is a local lookup, so it stays responsive and works offline. (No
`cargo`? After `npm run build` you can also point `npm run dev` at a running
inspector via the Vite proxy — see [Build](#build).)

## Interactions

| Action | Result |
|---|---|
| **Hover** an identifier or expression in the source | Tooltip with the tightest enclosing IR node's `label`, its type(s), and `provenance`. A monomorphized definition shows the *set* of specialized types (e.g. `Int \| String`). On a use-site, the tooltip also offers a **"→ jump to definition"** link. |
| **Left-click** a term in the source | Selects the tightest enclosing IR node — highlights it in the source and reveals + highlights it in the IR tree (expanding ancestors). The source → tree cross-link. |
| **Ctrl/Cmd-click** a variable use in the source | Goto-definition: jumps + scrolls to the def-site and selects its node in both panels. The IDE/LSP-standard gesture (Ctrl, or ⌘ on macOS); the hover-tooltip link does the same thing for discoverability. |
| **Click** a node row in the IR tree | Selects the node — highlights its source span in the editor and scrolls to it. The tree → source cross-link. |
| **Click the ▸ / ▾ twisty** on a tree row | Expands / collapses that subtree (distinct from selecting the row). |
| **Hover a squiggle** or gutter marker in the source | The diagnostic message. Type errors underline the offending span — and still render even when the program fails to compile, since the source panel always loads. |

The header shows the program name, the snapshot kind (`post-inference`, or
`failed` when the program has errors), and a **static (no values)** badge — M1
inspects the program with no execution, so there are no runtime values yet.

Cross-linking is bidirectional: **left-click** a source term to find its IR
node, **click** an IR row to find its source span, and **Ctrl/Cmd-click** (or
the hover-tooltip link) on a use to jump to its definition. (Right-click is left
to the browser — hijacking it would also remove copy/inspect and is unreliable.)

## Toolchain

- **Vite** (build + dev server)
- **TypeScript** (strict)
- **CodeMirror 6** (`codemirror`, `@codemirror/state`, `@codemirror/view`) for
  the read-only source editor
- **`vite-plugin-singlefile`** — inlines all JS and CSS into one
  `dist/index.html` with zero external requests (no CDN, no external fonts), so
  the page is offline-capable and embeddable.

The IR tree is plain DOM (not a CodeMirror instance); only the source editor is
CodeMirror.

## Build

```bash
npm install
npm run build      # tsc --noEmit, then vite build -> dist/index.html
npm run typecheck  # tsc --noEmit only
npm run test       # vitest run (offsets + indices unit tests)
npm run dev        # local Vite dev server (proxy /api to a running inspector)
```

`npm run build` emits a single self-contained `dist/index.html`.

## Tests

The correctness-critical pure functions are unit-tested with **vitest** (run in
CI via `./ci.sh web`):

- `offsets.test.ts` — the byte↔char bridge, round-trips on multi-byte (`café`,
  `×`) and astral (emoji surrogate-pair) input.
- `indices.test.ts` — `tightestNodeAt` (nested → innermost; coincident spans →
  deepest), `typesAt` (narrowest-span type set, deduped, read from the node's
  `type` field), and `definitionAt`.
- `links.test.ts` — the cross-stage resolver: identity adjacency (both
  directions), mono fan-out edges (1→N, transitive to sibling clones),
  source-span projection/dedup, and graceful degradation on unknown seeds.
- `store.test.ts` — over golden fixtures: the B5 hole→type stitch, cross-pane
  resolution, and the wire-shape contract (including `meta.schema === 1`).
- `sourceView.test.ts` — the pure gesture logic `hoverPayloadAt` (label / type
  set / provenance / goto-def name) and `resolveSourceClick` (plain vs.
  Ctrl/Cmd-click goto-def), which the CodeMirror handlers call directly.
- `main.test.ts` — the byte-based `byteLineStarts`/`lineCol`/`formatSpan`
  arithmetic and a jsdom degraded-render test over `failed.snapshot.json`.
- `wireValidate.test.ts` — `validateSnapshot` accepts every real fixture and
  throws (naming the path) on malformed payloads; this is the runtime
  replacement for the old unchecked `as Snapshot` cast.

`offsets.ts` and `indices.ts` are slated for a Rust port (see below), so their
tests double as the behavioural spec for that port.

## Committed bundle (R7)

`dist/index.html` is **committed to the repo on purpose**. The server embeds it
via `include_str!("../web/dist/index.html")` (see `src/server.rs`), so a plain
`cargo build` produces a working inspector **without requiring Node**. The
`.gitignore` here keeps `node_modules/` and Vite caches out of the tree but
explicitly tracks `dist/index.html`. After changing anything under `src/`, rerun
`npm run build` and commit the regenerated bundle.

## Module layout

The frontend is vanilla TypeScript (no framework), split into small modules:

- `offsets.ts` — the **byte↔char bridge** (correctness-critical, see below).
- `indices.ts` — derived lookups over **one stage's** IR: `nodeById` /
  `depthById` (from flattening the IR), and the spatial queries
  `tightestNodeAt`, `typesAt`, `definitionAt`. Built once per stage.
- `links.ts` — the **cross-stage resolver** (correctness-critical, unit-tested):
  `buildLinkGraph` assembles the identity ∪ `stageLinks` graph; `resolveLinks`
  walks it bidirectionally/transitively from a seed set to per-stage highlight
  sets + source spans.
- `store.ts` — a tiny reactive layer holding the snapshot + per-stage indices +
  the link graph + a shared, cross-stage `selection`. It resolves each selection
  to a per-pane highlight set; that resolved state **is** the cross-pane link.
- `sourceView.ts` — the CodeMirror editor plus hover/goto-def/squiggles and the
  resolved source-span highlight (primary vs. linked).
- `treeView.ts` — one collapsible IR tree pane, parameterized by `stageId`,
  cross-linked to every other pane.
- `main.ts` — fetch `/api/snapshot`, build the store, render the source pane +
  one tree pane per stage.

### The byte↔char bridge (`offsets.ts`)

Cambra `Span`s carry **UTF-8 byte offsets**; CodeMirror positions are document
offsets in **UTF-16 code units**. They coincide for ASCII but diverge on any
multi-byte character, so **every** crossing between a Cambra span and a CM
position routes through `OffsetMap.byteToChar` / `charToByte`. The map is built
once per source (cumulative byte length per code-point boundary) and queried by
binary search.

## Scope: multi-pane (interactive, snapshot-first)

The view is a **generic, N-stage layout**: a source pane plus one IR tree pane
per pipeline stage, ordered upstream → downstream. The MVP renders three panes —
`[source] [post-desugar] [post-inference]` — each `flex: 1 1 0` (equal width).
Stages come from the snapshot's `stages[]`; adding a stage is a backend payload
change, not a frontend rewrite.

- **Source pane** — read-only CodeMirror editor with:
  - **hover tooltips**: hovered position → tightest enclosing IR node → its
    `label`, type set (joined with ` | `), and `provenance`. Anchored on the
    **post-inference** stage (the one carrying resolved types).
  - **goto-definition** on **Ctrl/Cmd-click** a use-site (or the hover-tooltip
    link): selects the def-site as a source selection so every pane follows.
  - **diagnostic squiggles** via the `@codemirror/lint` `linter` facet — gutter
    markers + hover messages mapped from `diagnostics[]`. **These render in the
    degraded snapshot too** (no stages but diagnostics present), so a type-error
    program still underlines its error.
  - **selection highlight**: a `StateField<DecorationSet>` marking the resolved
    source spans — the **primary** anchor span strongly, transitively-**linked**
    spans lightly.
- **IR panes** — one collapsible tree per stage (label, type, node id, edge
  labels), **cross-linked across all panes**: clicking a row selects that node
  in its stage; the store resolves it through the **stage link graph** to a
  highlight set in *every* pane (primary vs. linked) plus the source spans. A
  pre-inference stage (holes/untyped) carries a **"pre-inference (holes)"** badge
  in its header. On a degraded/`failed` snapshot a diagnostics list replaces the
  trees.
- **Header**: program name, `snapshotKind`, and a "static (no values)" badge
  reflecting the `meta.tick: null` seam.

### Cross-pane links = identity ∪ stageLinks (bidirectional, transitive)

The adjacency between two consecutive stages is **identity on shared NodeIds ∪
the non-identity `stageLinks` edges** (monomorphization fan-out, generalized-let
wrappers). `links.ts` resolves a click to the full provenance chain by walking
this graph **both directions, transitively** — so clicking one mono clone in the
post-inference pane lights up its pre-inference original *and* every sibling
clone (the type-set). The backend ships only the non-identity edges; the client
computes identity itself (`buildLinkGraph` / `resolveLinks`, unit-tested in
`links.test.ts`).

### `tightestNodeAt` is a TS prototype of the D4 policy

`tightestNodeAt` implements the **D4 tightest-enclosing** policy (smallest
containing extent; ties — coincident spans, e.g. the `def` case or
monomorphized clones — broken by greatest IR depth). It is deliberately
prototyped in TypeScript here; a **Rust port + dedup** against the source-level
`NameBinderIndex`/`SpanIndex` is a tracked followup. Until then, `indices.test.ts`
pins the behaviour as the port's spec.

**Not yet implemented** (F3):

- Scope/locals panel (the snapshot's `scopes` table is fetched but unused in
  F2), outline/symbol panel, a "show internals" (synthetic/derived nodes)
  toggle, syntax highlighting, theming polish.

# Cambra Inspector — web frontend

The CodeMirror 6 frontend for the Cambra program inspector. It is a small,
read-only single-page app: on load it fetches `/api/snapshot` from the
inspector server (`src/inspector_server/`) and renders the program source
alongside one IR tree pane per pipeline pane, cross-linked across all panes via
the pane provenance graph.

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
> demand, so they move to per-query/streaming over the CQRS transport. The
> `Store` here builds all indices eagerly in its constructor from one payload;
> adding live values is **not** a matter of adding a field — it will require
> reworking the store into an incremental/streaming model. That is an expected,
> additive migration (the static read model is a true subset of the live one),
> but flagged here so the eager-load architecture is understood as scoped to M1.

## Running the inspector

See [Running it](../README.md#running-it). No `cargo`? After `npm run build`,
`npm run dev` proxies `/api` to a running inspector — see [Build](#build).

## Interactions

| Action | Result |
|---|---|
| **Hover** an identifier or expression in the source | Tooltip with the tightest enclosing IR node's `label`, its type(s), and `provenance`. A monomorphized definition shows the *set* of specialized types (e.g. `Int \| String`). On a use-site, the tooltip also offers a **"→ jump to definition"** link. |
| **Left-click** a term in the source | Selects the tightest enclosing IR node — highlights it in the source and reveals + highlights it in the IR tree (expanding ancestors). The source → tree cross-link. |
| **Ctrl/Cmd-click** a variable use in the source | Goto-definition: jumps + scrolls to the def-site and selects its node in both panels. The IDE/LSP-standard gesture (Ctrl, or ⌘ on macOS); the hover-tooltip link does the same thing for discoverability. |
| **Click** a node row in the IR tree | Selects the node — highlights its source span in the editor and scrolls to it. The tree → source cross-link. |
| **Click the ▸ / ▾ twisty** on a tree row | Expands / collapses that subtree (distinct from selecting the row). |
| **Hover a squiggle** or gutter marker in the source | The diagnostic message. Type errors underline the offending span — and still render even when the program fails to compile, since the source panel always loads. |
| **Click a pane's Copy button** | Copies that pane's text to the clipboard. The source pane yields the program verbatim; a tree pane yields one indented line per row; the Diagnostics pane yields each card's three lines. The button reports the outcome — a refused write says so rather than looking like it worked. |

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
- `links.test.ts` — the cross-pane resolver: identity adjacency (both
  directions), mono fan-out edges (1→N, transitive to sibling clones),
  source-span projection/dedup, and graceful degradation on unknown seeds.
- `store.test.ts` — over golden fixtures: the B5 hole→type stitch, cross-pane
  resolution, and the wire-shape contract (including `meta.schema === 1`).
- `sourceView.test.ts` — the pure gesture logic `hoverPayloadAt` (label / type
  set / provenance / goto-def name) and `resolveSourceClick` (plain vs.
  Ctrl/Cmd-click goto-def), which the CodeMirror handlers call directly.
- `main.test.ts` — the byte-based `byteLineStarts`/`lineCol`/`formatSpan`
  arithmetic, `serializeDiagnostics` (the Diagnostics pane's copy text, asserted
  against the same `diagnosticLines` the pane renders from), and a jsdom
  degraded-render test over `failed.snapshot.json`.
- `treeView.test.ts` — `resolvedTypeTooltip`, and `serializeTree`: the copy
  grammar row by row, the two-space indent, the included `where.N` predicate
  subtrees, and a fixture case pinning one line per rendered node.
- `clipboard.test.ts` — `copyToClipboard`'s three outcomes: an absent API, a
  successful write, and a refused one.
- `wireValidate.test.ts` — `validateSnapshot` accepts every real fixture and
  throws (naming the path) on malformed payloads; this is the runtime
  replacement for the old unchecked `as Snapshot` cast.

`offsets.ts` and `indices.ts` are slated for a Rust port (see below), so their
tests double as the behavioural spec for that port.

## Committed bundle (R7)

`dist/index.html` is **committed to the repo on purpose**. The server embeds it
via `include_str!` (see `src/inspector_server/serve.rs` in the `cambra` crate),
so a plain `cargo build` produces a working inspector **without requiring
Node**. The
`.gitignore` here keeps `node_modules/` and Vite caches out of the tree but
explicitly tracks `dist/index.html`. After changing anything under `src/`, rerun
`npm run build` and commit the regenerated bundle.

## Module layout

The frontend is vanilla TypeScript (no framework), split into small modules:

- `offsets.ts` — the **byte↔char bridge** (correctness-critical, see below).
- `indices.ts` — derived lookups over **one pane's** node table: `nodeById`
  (the table, keyed) / `depthById` and `predicateIds` (walked from `root`
  through the child edges), and the spatial queries `tightestNodeAt`, `typesAt`,
  `definitionAt`. Built once per pane.
- `links.ts` — the **cross-pane resolver** (correctness-critical, unit-tested):
  `buildLinkGraph` keys the dense `paneLinks` edges by adjacent pair;
  `resolveLinks` walks them bidirectionally/transitively from a seed set to
  per-pane highlight sets + source spans.
- `store.ts` — a tiny reactive layer holding the snapshot + per-pane indices +
  the link graph + a shared, cross-pane `selection`. It resolves each selection
  to a per-pane highlight set; that resolved state **is** the cross-pane link.
- `sourceView.ts` — the CodeMirror editor plus hover/goto-def/squiggles and the
  resolved source-span highlight (primary vs. linked).
- `treeView.ts` — one collapsible IR tree pane, parameterized by `paneId`,
  rendered by walking the pane's node table from `root`, cross-linked to every
  other pane.
- `clipboard.ts` — the one impure clipboard call, isolated so the serializers
  that feed it stay DOM-free and directly testable.
- `main.ts` — fetch `/api/snapshot`, build the store, render the source pane +
  one tree pane per pane entry.

### The byte↔char bridge (`offsets.ts`)

Cambra `Span`s carry **UTF-8 byte offsets**; CodeMirror positions are document
offsets in **UTF-16 code units**. They coincide for ASCII but diverge on any
multi-byte character, so **every** crossing between a Cambra span and a CM
position routes through `OffsetMap.byteToChar` / `charToByte`. The map is built
once per source (cumulative byte length per code-point boundary) and queried by
binary search.

## Scope: multi-pane (interactive, snapshot-first)

The view is a **generic, N-pane layout**: a source pane plus one IR tree pane
per pipeline pane, ordered upstream → downstream. It renders `[source]` then one
pane per pipeline pane in order, each `flex: 1 1 0` (equal width). The panes come
from the payload's `panes[]`; adding a pane is a backend payload change, not a
frontend rewrite.

- **Source pane** — read-only CodeMirror editor with:
  - **hover tooltips**: hovered position → tightest enclosing IR node → its
    `label`, type set (joined with ` | `), and `provenance`. Anchored on the
    **post-inference** pane (the one carrying resolved types).
  - **goto-definition** on **Ctrl/Cmd-click** a use-site (or the hover-tooltip
    link): selects the def-site as a source selection so every pane follows.
  - **diagnostic squiggles** via the `@codemirror/lint` `linter` facet — gutter
    markers + hover messages mapped from `diagnostics[]`. **These render in the
    degraded snapshot too** (no panes but diagnostics present), so a type-error
    program still underlines its error.
  - **selection highlight**: a `StateField<DecorationSet>` marking the resolved
    source spans — the **primary** anchor span strongly, transitively-**linked**
    spans lightly.
- **IR panes** — one collapsible tree per pane (label, type, node id, edge
  labels), **cross-linked across all panes**: clicking a row selects that node
  in its pane; the store resolves it through the **pane link graph** to a
  highlight set in *every* pane (primary vs. linked) plus the source spans. A
  pre-inference pane (holes/untyped) carries a **"pre-inference (holes)"** badge
  in its header. On a degraded/`failed` snapshot a diagnostics list replaces the
  trees.
- **Header**: program name, `payloadKind`, and a "static (no values)" badge
  reflecting the `meta.tick: null` seam.

### Cross-pane links are the dense `paneLinks` (bidirectional, transitive)

The adjacency between two consecutive panes is the backend's **dense**
`paneLinks` map: every edge, self-edges included. A node reaches the same NodeId
in a neighbouring pane through the shipped `[id, id]` self-edge, so the client
follows edges only and has no identity special case; a monomorphization or inline
fan-out is the `u !== d` edges. `links.ts` resolves a click to the full
provenance chain by walking this graph **both directions, transitively** — so
clicking one mono clone in the post-inference pane lights up its pre-inference
original *and* every sibling clone (the type-set) (`buildLinkGraph` /
`resolveLinks`, unit-tested in `links.test.ts`).

### `tightestNodeAt` is a TS prototype of the D4 policy

`tightestNodeAt` implements the **D4 tightest-enclosing** policy (smallest
containing extent; ties — coincident spans, e.g. the `def` case or
monomorphized clones — broken by greatest IR depth). It is deliberately
prototyped in TypeScript here; a **Rust port** is a tracked followup, and the
backend answers no positional query, so this is the only implementation of the
policy. Until then, `indices.test.ts` pins the behaviour as the port's spec.

**Not yet implemented** (F3):

- Scope/locals panel — the payload carries no scope table, and adding one means
  a channel naming a binder site (`src/inspector_model/design.md`, "What the
  model cannot say"). Outline/symbol panel, a "show internals"
  (synthetic/derived nodes) toggle, syntax highlighting, theming polish.

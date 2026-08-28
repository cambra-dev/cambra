# The inspector model — the snapshot the inspector serves

`src/inspector_model/` turns a `CompiledProgram` into one read-only payload describing that program:
its source, its IR at every retained pane, the links between adjacent panes, and its source-level
name resolution. The `cambra-inspector` crate serves the payload; that crate's web frontend renders
it.

Nothing in the CCL pipeline reads this module. It is the only consumer of the pane folds'
projections and maps — the leak gate reads the same folds' `leaks` under
`CAMBRA_PROVENANCE_GATE`, see [provenance.md](../ccl/design/provenance.md#the-seam) — and a release
compile reads the lowering projection alone.

**Status.** The payload, the two indices, the per-pane node tables and the pane-pair links are in
tree.
Prose marked **planned** describes what is designed and not built: the live-value path. Every
disagreement between this document and the code is listed under
[Decided, not yet built](#decided-not-yet-built).

## At a glance

| | |
|---|---|
| Input | a `CompiledProgram`: the pane trees, the provenance table, the lowering projection, the parsed surface AST, the source text |
| Output | one `SnapshotPayload`: `source` (the program text), `panes` (per pane: a node table, its root, and its span rows), `paneLinks` (node→node relations between adjacent panes), `definitions` (use→binder pairs), `scopes` (visible names per region), `diagnostics` (compile errors, empty on success), `meta` |
| When it runs | once per compiled program, on the inspector's path only |
| Consumer | the `cambra-inspector` crate, which serves the payload, and that crate's frontend, which renders it |
| Feature gate | the wire types derive `Serialize` under the default-off `serde` feature; `ci_clippy_serde` is the CI pass that compiles them |
| `span` | throughout: a byte range in the **CHL source text**, never an offset into a rendered pane. Nothing in the payload addresses a pane's text |

## The usage model

### One payload per program; every lookup is the consumer's

`cambra-inspector` compiles a program once at startup and serves the rendered payload from memory.
Its frontend fetches that payload once and answers every interaction from it — clicking a node,
hovering a span, following a link from one pane to the next. No snapshot interaction reaches the
compiler or a running program; reading a running program is the separate path below.

Two rules follow.

- **Every static fact ships in the payload.** A fact about the program as written or as compiled is
  a field, not a request.
- **The consumer answers positional questions; this module ships the tables they are answered
  over.** "Which node is at this position" is a lookup over the span rows and the tree, both
  shipped. Answering it here as well would be a second implementation of one semantics, and the
  consumer's is the copy that runs.

So this module offers no positional query. `SpanIndex` and `NameBinderIndex` build their tables and
enumerate them onto the wire; neither answers "what is at this position".

The consumer's own lookup combines two shipped things: the `(span, node)` rows for containment, and
the pane's tree for structure. Depth, which breaks a tie between byte-identical spans, comes from
the tree it already walks, which is why a span row carries no depth.

### The live model is a separate path

**Planned.** Inspecting a running program means reading values: clicking a `source` shows its most
recent, not-yet-released data. A value is data-dependent and keyed by a tick, so it cannot ride a
payload built at compile time.

That path needs node identity in operator conversion and a tick channel; neither exists. On the
first, see
[provenance.md](../ccl/design/provenance.md#known-prerequisites-for-panes-past-post-planning).

It does not reuse the static lookups. A live read is `(node, tick) → value` and a static lookup is
`span → node`, so a static handler kept in anticipation of the live path gains it nothing.

## The data model

### A pane on the wire

`PANES` (`src/ccl/panes.rs`) is the topology and the payload is derived from it: one `panes[]`
entry per pane in pipeline order, one `paneLinks[]` entry per adjacent pair. A pane's `id` is the
pane's declared name, its `label` is that name rendered as `IR (POST-INFERENCE)`, and its `kind` is
`"holes"` before inference has run and `"typed"` at or after it, read off the phases the pane
declares rather than off its position. Adding a pane is an entry in `PANES` and no edit here.

`the_payload_ships_one_pane_entry_per_declared_pane_and_one_link_per_pair` (`snapshot.rs`) pins the
ids,
the order, the arity and the kind split.

### The anchor pane

`ANCHOR_PANE` is `"post-inference"` — the first fully-typed tree that is still source-shaped. It
decides which pane a binder's type is read from, so `scopes[].bindings[].type` is a post-inference
type. The pane is named rather than positional, and `Snapshot::new` panics if `PANES` does not
declare it, so inserting a pane ahead of it cannot silently move the anchor.

### A pane resolves against itself

A pane carries its own node table and its own `(span, node)` rows, both resolved against its own
attributions rather than the anchor's. A node id means the same thing in every pane that
holds it; what each pane says about that node is that pane's own answer.

### A node on the wire

A pane ships `nodes`, every node of that pane exactly once, and `root`, the id its walk starts from.
A node reached from several places — a shared refinement predicate, most often — is one entry that
several children name. The order is first-visit pre-order, so the payload is byte-reproducible.

Each node carries:

| field | what it holds |
|---|---|
| `label` | the node's kind, rendered — `BinOp(Arithmetic(Mul))`, `Lit(Int(1))`, `Let(x)` |
| `nodeId` | its `NodeId` as a number, the handle every link and span row names |
| `span` | the **narrowest** source span it traces to, or absent when it traces to none |
| `rewritten` | `null` for a lowering root, else `{ via, nature, label }` |
| `type` | its type, rendered ([Types on the wire](#types-on-the-wire)) |
| `typeKind` | which constructor sits at the top of that type — `"base"`, `"fun"`, `"dataFun"`, `"refinement"`, `"hole"`, … |
| `predicateRefs` | the predicates riding this node's own type, as ids into the same table |
| `children` | `{ edge, id, predicate }` — the child's id in this same table, its display label, and whether it is a type-interior subtree |

A node's `span` is one span even where it traces to several; the `(span, node)` rows carry all of
them, so a node several source spans fan into is reachable from each.

`rewritten` is `null` for a `Nature::Source` tag, which null-compresses at the one emission site via
`Nature::is_source`. `Source` is positional rather than a judgment about faithfulness: a node is
`Source` exactly when it is the root of a lowered source expression, so an interior image of source
text carries `Machinery` with the label `"lower.image"` instead — see
[provenance.md](../ccl/design/provenance.md#the-seam).

A node the pane's projection does not cover ships the same `null`, for both `rewritten` and `span`,
so the wire cannot tell an unexplained node from a lowering root.
`every_node_of_every_pane_carries_an_attribution` (`snapshot.rs`) is what keeps the first case from
arising, over the same corpus the other payload tests use.

The wire carries no flat `Source`/`Derived`/`Synthetic` string; a consumer formats the triple
itself.

**A refinement predicate is a child node.** A predicate is an expression tree in its own right
([Predicates are nodes](#predicates-are-nodes)), and it reaches the consumer as a child of the node
whose type carries it. `predicate` on the edge is what a consumer branches on. The `edge` label is
for display and follows the same split: a value child's is its positional index (`"0"`, `"1"`), a
predicate's is `where.N`.

`N` counts predicates in `walk_type_slots` order — the node's own type, its annotation, a `Cast`
target, then each binder's type and annotation — flattened across nested type children. The order is
stable, so a consumer can compare a node's predicate edges across panes.

### Pane links are dense and labelled

A `ProvenanceMap` is the compiler's node→node relation between two adjacent panes: what each node of
the upstream pane became, and what each node of the downstream pane came from. It ships verbatim,
self-edges included, so a node preserved across the phase appears as its own `[id, id]` edge and the
consumer may follow edges with no identity special case. Each edge carries the labels it asserts —
`"descends"` for a node made from the upstream one, `"relates"` for one that is about it but was not
made from it — as a set, since an edge reachable both ways carries both. The label set is never
empty.

Every endpoint of every edge is a node of the tree it points into: an edge a consumer follows always
lands somewhere. `every_pane_link_endpoint_is_a_node_of_the_tree_it_points_into` (`snapshot.rs`)
asserts it at the producer, and the consumer's wire validator re-checks it on the shipped payload —
that branch of the validator has no test of its own.

### Predicates are nodes

A refinement predicate is a term hanging off a type — `x > 2` in `[x * 2 for x in xs if x > 2]` — so
it is an expression tree with `NodeId`s of its own. The compiler tracks those ids like any other:
they carry attributions and they appear as endpoints of the pane links (see
[provenance.md](../ccl/design/provenance.md#walking-the-ids)). A tree that stopped at the main
expression tree would therefore ship links pointing at nodes it had left out, which is why every
walk here descends into predicates.

**A predicate ships once.** One predicate term is shared — the same term is reachable from a node's
own type, from a binder's type, and from the types of other nodes — so it is one entry in the node
table that several child edges name. That is what the table is for. A tree had to repeat the whole
subtree once per slot that reached it, and the span rows repeated with it: on the program measured
under [Cost](#cost), 2,443 node positions for 465 nodes, and 1,978 of 2,443 span rows repeating a
pair already present.

### Types on the wire

A node's `type` is rendered by `Display for Type`, and `Type`'s `Serialize` impl delegates to that
same `Display`, so every type on the wire is one rendered string. Every node has a type, so the
field is never absent.

The choice is provisional. A structural type would carry a refinement's predicate, which is an
expression tree with node ids, re-creating inside every `type` field the repetition the predicate
table removes;
and the compact spelling — `⇒` against `⤇`, `T@lit` singletons, `{T | p}`, `Σ`, `?N` — would have to
be reimplemented by the consumer.

Two narrow facts ride beside the string so a consumer is not left parsing it. `typeKind` is the
type's top constructor, which is what a consumer branches on to filter or colour by type.
`predicateRefs` names the predicates riding the node's own type, as ids into the pane's table, which
is what turns "this type is refined" into the predicate's own node. Both say something the rendering
cannot be asked for reliably, and neither describes what is inside the type.

What the rendering still forecloses: a consumer cannot diff a node's type across panes except by
string comparison, and cannot elide a long type by structure.

A node's `where.N` children cover every type slot it carries — its own type, an annotation, a `Cast`
target, each binder's — so they cannot say which predicate refines the node's *own* type.
`predicateRefs` is that subset, and it is the leading part of those children, since the walk reaches
the node's own type first.

### A binder's type is the binder's

A binding site takes its type from the IR binder occupying that site, not from the node whose span
contains it. Take this program:

```chl
g = "abc"
4
```

Its source spans:

| written | span |
|---|---|
| `g` | 0…1 |
| `"abc"` | 4…9 |
| `4` | 10…11 |

It lowers to one `Let` — `let g = "abc" in 4` — whose nodes carry:

| node | span | type | binder it declares |
|---|---|---|---|
| `Let(g)` | 0…9 | `Int@4` | `g : String@"abc"` |
| `Lit(String)` | 4…9 | `String@"abc"` | — |
| `Lit(Int)` | 10…11 | `Int@4` | — |

The binder `g` has no node of its own, because a name is not an expression. So the narrowest node
containing `g`'s span is the whole `Let`, and a `Let`'s type is the type of what follows the
binding — `Int@4` here, the trailing `4`. Clicking `"abc"` answers `String@"abc"` because the
literal is a node; clicking `g` has to answer from the binder, or it answers with an unrelated type
that happens to be well-formed.

**Why the payload cannot simply say so.** An attribution maps a node to the source spans it came
from. A binder is not a node, so nothing attributes it, and the `Let` holding it carries one span
covering the whole statement. No field says "the binder written at 0…1 is this node's".

`Snapshot::binder_type` recovers that correspondence by searching, among the nodes whose span covers
the binding site, for the node that holds the binder — by two tests, in order.

1. **The binder's name.** `g` is still a binder named `g` on the covering `Let`. Shadowed binders
   separate on span, since each statement's `Let` covers only its own binding site:

   | statement | span | the node binding it | its span |
   |---|---|---|---|
   | `x = 1` | 0…5 | outer `Let(x)` | 0…5 |
   | `x = x + 1` | 6…15 | inner `Let(x)` | 6…15 |

2. **The node's span equals the binding site.** A `def`'s binding site is its whole statement, and
   monomorphization has replaced the source binder with a `__mono` specialization, so the name test
   misses; the node standing at exactly that span is the binding one.

A parameter's name span is no node's span and no binder carries the name, so both tests miss and the
answer is `None`. `a_binder_joins_its_own_type_not_the_continuations`,
`a_def_binder_joins_its_function_type` and `a_substituted_multi_param_binder_joins_no_type`
(`query.rs`) pin the three outcomes.

**A better design exists and is not built.** The two tests reconstruct a fact the compiler had and
dropped. Either of two channels would replace them with a read, and both are follow-up work beyond
the changes this document ratifies, carried as a `TODO(binder-site)` on `binder_type`:

- a **source span on `TypedBinding`**, so a binder carries its own site; or
- a **binder-site entry in a pane's attributions**, so the pane says which node binds a given site.

Until one exists, a binder's type is recovered rather than looked up, and the recovery is only as
good as its two tests.

### Definitions and scopes are source-level

Name resolution runs over the parsed surface AST, not the IR, because lowering destroys the *name*
of a multi-param parameter: `uncurry_params` rewrites `Var(p)` to `__arg_tuple_N ▷ .i`, so nothing
downstream binds or mentions `p`. The occurrence keeps its own id and span, so a *use* of `p` still
resolves to a node and a type; what no IR pass can recover is which binder that use refers to, and
that is what `NameBinderIndex` answers.

A scope region is emitted per statement and per expression, minus those where no name is visible and
those repeating a span and binder set already emitted — a statement and its expression share a span,
so the walk reaches one region twice. The regions that remain are dense and nest.

### Diagnostics and the degraded payload

`diagnostics` is empty on a successful payload: it describes a program that compiled, and there are
no warnings. A failed compile ships `SnapshotPayload::degraded` instead — same type, so the two
shapes cannot drift — carrying the source text, the diagnostics, `meta.snapshotKind: "failed"`, and
empty `panes`, `paneLinks`, `definitions` and `scopes`.

A failed compile ships no panes even where the pipeline reached some: inference can fail after
channelization succeeded, and that channelized IR is displayable. Shipping what a failed compile did
reach is follow-up work beyond this document's ratified changes, since it needs the pipeline to hand
back its partial panes rather than one error; it is carried as `TODO(degraded-stages)` on
`SnapshotPayload::degraded`.

A `Diagnostic` is a `CompileError` with the compiler stage that raised it, a message and a span. The
message is the error's `Display` rendering — the same single line the terminal's ariadne label
carries — so the two renderers say the same thing rather than one of them shipping a struct dump.
Two variants have no `Display` and use `Debug`: `InferError`, whose `Debug` is its message by
convention, and `ConversionError`.

The span is the error's own wherever it has one. `Parse` and `Lower` read theirs off the error,
`Infer`'s is resolved at the `compile_program` boundary; `ChannelizeDefers`, `LambdaElim`,
`Conversion` and `Unsupported` carry none, so a consumer has nothing to underline for them.

`meta` carries `snapshotKind`, the always-null live seam `tick`, and `schema`. The schema's
`outline` field is omitted rather than stubbed, until an outline query exists.

### The schema version

`SCHEMA_VERSION` is the payload's wire version, carried as `meta.schema`, and is **5**. A breaking
change — a field removed, renamed or retyped, or a value shape an old consumer would misread — bumps
it; purely additive optional fields do not. The node table bumped it to 5, and the wire changes
still to land ride that bump rather than adding their own, since 5 has not shipped.

The wire is pinned on both sides. The consumer's golden fixtures compare whole payload documents,
every node id included, so any change re-blesses all of them; its wire validator pins the schema
number, the pane list and the edge-label vocabulary as literal lists. Both live in the
`cambra-inspector` crate, which owns the fixture corpus.

## Cost

Building the payload is the module's only cost, and it is off the release path. Per pane it is
O(tree) for the tree and the span rows; per scope binding it is one or two full walks of the anchor
tree, since `binder_type`'s probes run in sequence and a parameter's site misses both. So the scope
join is O(bindings × tree).

Measured at the time of writing, before the node table, which is what the size
figures below are dominated by:

```chl
xs = [1, 2, 3, 4]
ys = [x * 2 for x in xs if x > 2]
g = 10
def f(p, q):
  p + q + g
max(ys) + f(1, 2)
```

| | |
|---|---|
| nodes, six panes | 465, one entry per node |
| `post-planning` alone | 184 |
| span rows | 465 — one per node here, since every node of this program traces to exactly one span — with no pair repeated |
| predicate edges | 198, naming 465 nodes between them |
| pane-link edges | 419 |
| scope regions | 25, over 76 bindings |
| build time | about 10 ms, of which the payload is 2 ms |

Size is the cost that binds rather than time. The node table is what bounds it: a pane ships one
entry per node, so the payload grows with the program and not with how many type slots reach a
shared term.

## API shape

| item | what it is for |
|---|---|
| `Snapshot::new` | bundle every pane of a `CompiledProgram` with the two indices |
| `Snapshot::from_parts` | bundle one named pane; the payload then carries that pane alone and no pane links |
| `Snapshot::build_payload` | assemble the `SnapshotPayload` — the whole read model |
| `SpanIndex::build` / `entries` | build the `(span, node)` table over one pane and enumerate it for the wire |
| `NameBinderIndex::build` / `definitions` / `scopes` | resolve names over the surface AST and enumerate the results |
| `dense_edges` | project a pane pair's `ProvenanceMap` onto the wire |
| `diagnostics_from_compile_errors` / `SnapshotPayload::degraded` | the compile-failure path |
| the wire types | `SnapshotPayload`, `PaneEntry`, `PaneLinkEntry`, `SpanEntry`, `DefinitionEntry`, `ScopeEntry`, `ScopeBindingEntry`, `Diagnostic`, `DiagnosticLabel`, `Meta`, `SCHEMA_VERSION` |

`Snapshot::binder_type` is internal.

Unit tests live in the module they exercise. `snapshot.rs`'s run over a three-program `corpus()`
chosen for the shapes that reach the payload's moving parts: a comprehension for refinement
predicates, a monomorphized definition for one source span over several nodes, and a mutable loop
for a recurrence.

## Design considerations

### The wire belongs to this module

The payload's node type is this module's own, and `pretty_tree` is a renderer again: it carries no
serde and no `ccl` types, which is its standing invariant. Before, the payload rode
`pretty_tree::InspectNode` — a rendering type holding the tile-producer fields `annotations` and
`tiling`, which the payload never set and no consumer read, plus a hand-written `Serialize`
spelling this module's schema. A wire change was then a diff in a renderer.

One encoder now writes a `RewriteTag` to the wire. There were two, the second on
`SourceAttribution`, each with its own copy of the null-compression rule; it went with the query
results that were its only reader.

### Span containment is a scan

Containment is the integer test `start <= pos < end`, so the span table is a flat vector. One
program's tree is small enough that an interval tree would cost more complexity than it saves, and
the table is enumerated here rather than searched, so swapping the structure later stays a change
behind this API. `intervalsets` is not used: it is built for numeric value domains and carries a
`contains` bug on half-bounded intervals (see `src/interpreter/tiling/predicate.rs`).

### What the model cannot say

- **A pane pair cannot report that an untouched node was untouched** where the phase re-mints its
  pass-through nodes. `lambda_elim` is that phase today, so each pass-through node reads to a
  consumer as a rewrite of its predecessor — see
  [provenance.md](../ccl/design/provenance.md#the-edge-labels).
- **No pane exists past `post-planning`** until operator conversion carries a node identity. A pane
  may be issued at any point in the pipeline; that one has nothing to resolve against.
- **No channel names a binder site**, which is what
  [A binder's type is the binder's](#a-binders-type-is-the-binders) works around.

## Decided, not yet built

Each change is ratified here and lands on its own. They are named rather than numbered: a numbered
list renumbers as entries land, and a reference to "item 4" would then point at the wrong change.

- **The type renames.** `Snapshot` becomes `InspectedProgram` and `SnapshotPayload` becomes
  `InspectorPayload`. "Snapshot" reads as one retained AST snapshot, which is what `provenance.md`
  calls a pane, where the type is the whole read model over every pane. `InspectedProgram` parallels
  the `CompiledProgram` it is built from. `meta.snapshotKind` becomes `payloadKind` — its values say
  which payload this is, not which pane.
- **Module reorganization.** One concept per module, each owning its type, its inherent impl and its
  unit tests, with no module depending on one above it. The target, which the current file names do
  not yet match — today `snapshot.rs` holds the wire and `query.rs` holds the bundle:

  | module | owns |
  |---|---|
  | walk | the shared IR traversal, named for `walk_children`/`walk_type_slots`: predicate children, node labels |
  | span index | the `(span, node)` table over one pane |
  | name binder | source-level name resolution over the surface AST |
  | snapshot | the bundle and its per-pane projections |
  | wire | the payload types, the schema version, the payload assembly, and the pane-link projection |

  Vocabulary the reorganization settles: an **index** is a built structure, a **lookup** is a read
  of one, and the **payload** is what ships.

The type renames above touch the wire at `meta`, and ride schema 5, which the node table bumped and
which has not shipped.

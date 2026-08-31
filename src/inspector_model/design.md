# The inspector model — the payload the inspector serves

`src/inspector_model/` turns a `CompiledProgram` into one read-only payload describing that program:
its source, its IR at every retained pane, the links between adjacent panes, and its source-level
name resolution. The `cambra-inspector` crate serves the payload; that crate's web frontend renders
it.

Nothing in the CCL pipeline reads this module. It is the only consumer of the pane folds'
projections and maps — the leak gate reads the same folds' `leaks` under
`CAMBRA_PROVENANCE_GATE`, see [provenance.md](../ccl/design/provenance.md#the-seam) — and a release
compile reads the lowering projection alone.

## At a glance

| | |
|---|---|
| Input | a `CompiledProgram`: the pane trees, the provenance table, the lowering projection, the parsed surface AST, the source text |
| Output | one `InspectorPayload`: `source` (the program text), `panes` (per pane: a node table and its root), `paneLinks` (node→node relations between adjacent panes), `definitions` (use→binder pairs), `diagnostics` (compile errors, empty on success), `meta` |
| When it runs | once per compiled program, on the inspector's path only |
| Consumer | the `cambra-inspector` crate, which serves the payload, and that crate's frontend, which renders it |
| Feature gate | the wire types derive `Serialize` under the default-off `serde` feature; `ci_clippy_serde` is the CI pass that compiles them |
| `span` | throughout: a byte range in the **CHL source text**, never an offset into a rendered pane. Nothing in the payload addresses a pane's text |

## The usage model

### One payload per program; every lookup is the consumer's

`cambra-inspector` compiles a program once at startup and serves the rendered payload from memory.
Its frontend fetches that payload once and answers every interaction from it — clicking a node,
hovering a span, following a link from one pane to the next. None of that reaches the compiler or a
running program; reading a running program is the separate path below.

- **Every static fact ships in the payload.** A fact about the program as written or as compiled is
  a field, not a request.
- **The consumer answers positional questions; this module ships the table they are answered
  over.** "Which node is at this position" is a scan of the shipped nodes. Answering it here as
  well would be a second implementation of one semantics, and the consumer's is the copy that runs.

So this module offers no positional query. It enumerates its tables onto the wire and answers
nothing about a position.

The consumer's own lookup reads one shipped table two ways: a node's `spans` for containment, and
its `children` for structure. Depth, which breaks a tie between byte-identical spans, comes from the
edges it already walks, which is why a node carries no depth.

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

`the_payload_ships_one_pane_entry_per_declared_pane_and_one_link_per_pair` (`wire.rs`) pins the
ids,
the order, the arity and the kind split.

### A pane resolves against itself

A pane carries its own node table, resolved against its own attributions rather than a sibling
pane's. A node id means the same thing in every pane that holds it; what each pane says about that
node is that pane's own answer.

### A node on the wire

A pane ships `nodes`, every node of that pane exactly once, and `root`, the id its walk starts from.
A node reached from several places — a shared refinement predicate, most often — is one entry that
several children name. The order is first-visit pre-order, so the payload is byte-reproducible.

Each node carries:

| field | what it holds |
|---|---|
| `label` | the node's kind, rendered — `BinOp(Arithmetic(Mul))`, `Lit(Int(1))`, `Let(x)` |
| `nodeId` | its `NodeId` as a number, the handle every link names |
| `spans` | every source span it traces to, narrowest first, empty when it traces to none |
| `rewritten` | `null` for a lowering root, else `{ via, nature, label }` |
| `type` | its type, rendered ([Types on the wire](#types-on-the-wire)) |
| `children` | `{ edge, id, predicate }` — the child's id in this same table, its display label, and whether it is a type-interior subtree |

A node carries every span its attribution records, so a node several source positions fan into is
reachable from each of them. `fold` unions blame spans, which is what makes that plural. There is no
second span → node table: it held one row per node per span, which is what `spans` says, and the
node-table walk that would build it already reads the same attributions.
`a_nodes_spans_are_its_attributions_narrowest_first` and `no_node_repeats_a_span` (`wire.rs`) pin
the order and the uniqueness.

`rewritten` is `null` for a `Nature::Source` tag, which null-compresses at the one emission site via
`Nature::is_source`. `Source` is positional rather than a judgment about faithfulness: a node is
`Source` exactly when it is the root of a lowered source expression, so an interior image of source
text carries `Machinery` with the label `"lower.image"` instead — see
[provenance.md](../ccl/design/provenance.md#the-seam).

A node the pane's projection does not cover ships the same empty `spans` and `null` `rewritten` as
a lowering root, so the wire cannot tell an unexplained node from one.
`every_node_of_every_pane_carries_an_attribution` (`wire.rs`) is what keeps the first case from
arising, over the same corpus the other payload tests use.

The wire carries no flat `Source`/`Derived`/`Synthetic` string; a consumer formats the triple
itself.

**A refinement predicate is a child node.** A predicate is an expression tree in its own right
([Predicates are nodes](#predicates-are-nodes)), and it reaches the consumer as a child of the node
whose type carries it. `predicate` on the edge is what a consumer branches on. The `edge` label is
for display and follows the same split: a value child's is its positional index (`"0"`, `"1"`), a
predicate's is `where.N`.

`N` counts predicates in `walk_type_slots` order — the node's own type, its annotation, a `Cast`
target, then each binder's type and annotation — flattened across nested type children, and
deduplicated by node id. The order is stable, so a consumer can compare a node's predicate edges
across panes.

One node names one predicate once. The slots overlap: `walk_type_slots` yields a `Lambda`'s own type
and its binder's type, and for a lambda those are the same `Type`, so a slot-order walk reaches that
type's predicates once per slot. Since a shared predicate is one entry in the table, a second edge
to it asserts nothing the first does, and `no_node_repeats_a_predicate_edge` (`wire.rs`) pins the
absence. A predicate several *nodes* reach still carries an edge from each of them.

`where.N` is a position in that sequence rather than a path through the type, so it does not say
which slot a predicate came from. A consumer needing the slots apart needs a path; nothing on the
wire asks.

### Pane links are dense

A `ProvenanceMap` is the compiler's node→node relation between two adjacent panes: what each node of
the upstream pane became, and what each node of the downstream pane came from. It ships verbatim,
self-edges included, so a node preserved across the phase appears as its own `[id, id]` edge and the
consumer may follow edges with no identity special case.

An edge is `[upstream, downstream]` and carries no label. `EdgeLabels` distinguishes `descends` (the
downstream node was made from the upstream one) from `relates` (it is about the upstream node but
was not made from it), and that distinction is load-bearing in `ccl`, where `has_ancestry` drives
leak accounting — see [provenance.md](../ccl/design/provenance.md#the-edge-labels). It stops at the
wire: link resolution is bidirectional and transitive, so a consumer following edges treats the two
alike.

Every endpoint of every edge is a node of the tree it points into: an edge a consumer follows always
lands somewhere. `every_pane_link_endpoint_is_a_node_of_the_tree_it_points_into` (`wire.rs`)
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
table that several child edges name. A table can express that and a nested tree cannot: a tree
carries a shared subtree once per position that reaches it.

One descent reaches them. `Type::walk_refinements` visits every refinement riding a type or its
nested type children, and the three callers that need it project differently from each one: this
module's `where.N` child edges, `collect_tree_ids`' id domain, and `predicate_id_collisions`' per-term
`Rc` keys. Written out per caller it was the same match-and-recurse three times, and a predicate this
module enumerated but `collect_tree_ids` did not would be a node the pane fold never explains.

### Types on the wire

A node's `type` is rendered by `Display for Type`, and `Type`'s `Serialize` impl delegates to that
same `Display`, so every type on the wire is one rendered string. Every node has a type, so the
field is never absent.

A structural type would carry a refinement's predicate, which is an expression tree with node ids,
re-creating inside every `type` field the repetition the node table removes; and the compact
spelling — `⇒` against `⤇`, `T@lit` singletons, `{T | p}`, `Σ`, `?N` — would have to be
reimplemented by the consumer.

The rendering is all the wire says about a type. A consumer cannot diff a node's type across panes
except by string comparison, cannot elide a long type by structure, and cannot branch on the top
constructor without parsing. What it can do is reach a refinement's predicate, which is a node with
an edge to it.

### Definitions resolve over the IR

`definitions` is one `{useSpan, defSpan, name}` row per resolved use, and it is read off the
**pre-inference** pane rather than the parsed surface AST.

Uid equality is lexical resolution. Every binder carries a globally-fresh `Uid` after
uniquification, copies preserve it, and a bound occurrence names its binder — so a use's binder is
the binder sharing its uid, capture-free by construction (`src/ccl/names.rs`). A binder is not a
node and has no span of its own, so the site reported is the span of the node that binds it: a use of
`g` in `g = 10` resolves to the statement rather than to the name, and a call resolves to the whole
`def`.

The pane is named, not positional: monomorphization splits a generalized definition into one
specialization per resolved type, so a later pane holds one copy of a `def` body per specialization
and would report each use once per copy. Pre-inference is the pane where a source name occurs as
often as it does in the program.

A multi-argument function's parameters bind nothing — `uncurry_params` substitutes
`__arg_tuple_N ▷ .i` for every occurrence — so uid equality cannot answer for them. They resolve
through the projection's two spans instead, the occurrence on the `Apply` and the declaration on its
`Proj` child ([ir.md](../ccl/design/ir.md#a-substituted-parameters-site-rides-its-projection)). The
projection is identified by its `lower.uncurry_proj` tag, so an author-written `t.0` is not mistaken
for one.

**What does not resolve.** A `Feed`, `Define` or `MutWrite` names a binder bound elsewhere, and that
name is a field rather than a node, so the only span available is the whole node's. A use span
covering a statement would contain the narrower uses inside it, and a consumer takes the first
containing row, so a broad row would shadow them. Those uses contribute none: `out` in
`out << value` does not resolve to its declaration. Closing it needs a span on the name field, which
is a `ccl` change. Over the fixture corpus this is 2 rows of 31.

This layer implements no scoping of its own. CHL's binding structure is stated in `ccl/scope.rs`
and minted by `uniquify`, and resolution here reads the result rather than recomputing it, so a
binding form added to the language cannot be answered wrong here without failing there first.

### Diagnostics and the degraded payload

`diagnostics` is empty on a successful payload: it describes a program that compiled, and there are
no warnings. A failed compile ships `InspectorPayload::degraded` instead — same type, so the two
shapes cannot drift — carrying the source text, the diagnostics, `meta.payloadKind: "failed"`, and
empty `panes`, `paneLinks` and `definitions`.

A failed compile ships no panes even where the pipeline reached some: inference can fail after
channelization succeeded, and that channelized IR is displayable. Shipping what a failed compile did
reach is follow-up work beyond this document's ratified changes, since it needs the pipeline to hand
back its partial panes rather than one error; it is carried as `TODO(degraded-panes)` on
`InspectorPayload::degraded`.

A `Diagnostic` is a `CompileError` with the compiler stage that raised it, a message and a span. One
span, not a list of labelled ranges: a diagnostic is built from one error, which carries at most one
range, so a label list could only repeat the message against the span already there. Pointing at
several ranges with distinct texts is a different type, and needs a producer holding those texts.
The
message is the error's `Display` rendering — the same single line the terminal's ariadne label
carries — so the two renderers say the same thing rather than one of them shipping a struct dump.
Two variants have no `Display` and use `Debug`: `InferError`, whose `Debug` is its message by
convention, and `ConversionError`.

The span is the error's own wherever it has one. `Parse` and `Lower` read theirs off the error,
`Infer`'s is resolved at the `compile_program` boundary; `ChannelizeDefers`, `LambdaElim`,
`Conversion` and `Unsupported` carry none, so a consumer has nothing to underline for them.

`meta` carries `payloadKind` — `"program"` for a compiled program, `"failed"` for a degraded
payload — and `schema`. Neither kind is a pane id, so one word never names both a pipeline position
and a document kind; `a_payload_kind_is_never_a_pane_id` (`wire.rs`) pins that. The schema's
`outline` field and a live-value `tick` are both omitted rather than stubbed, until something reads
them.

### The schema version

`SCHEMA_VERSION` is the payload's wire version, carried as `meta.schema`, and is **1**. A breaking
change — a field removed, renamed or retyped, or a value shape an old consumer would misread — bumps
it; purely additive optional fields do not.

The wire is pinned on both sides. The consumer's golden fixtures compare whole payload documents,
every node id included, so any change re-blesses all of them; its wire validator pins the schema
number and the pane list as literal lists. Both live in the `cambra-inspector` crate, which owns the
fixture corpus.

## Cost

Building the payload is the module's only cost, and it is off the release path. It is O(tree) per
pane: one walk building the node table, each node's spans read off the attribution that walk already
fetches. Name resolution is one walk of the surface AST.

Size is the cost that binds rather than time. The node table bounds it: a pane ships one entry per
node, so the payload grows with the program and not with how many type slots reach a shared term.

## API shape

| item | what it is for |
|---|---|
| `InspectedProgram::new` | bundle every pane of a `CompiledProgram` with the name index — the whole read model over one compiled program |
| `InspectedProgram::build_payload` | assemble the `InspectorPayload` — the whole read model |
| `diagnostics_from_compile_errors` / `InspectorPayload::degraded` | the compile-failure path |
| the wire types | `InspectorPayload`, `PaneEntry`, `IrNode`, `IrChild`, `RewriteInfo`, `PaneLinkEntry`, `DefinitionEntry`, `Diagnostic`, `Meta`, `SourceInfo`, `SCHEMA_VERSION` |

`new` and `build_payload` are the entry surface. `definitions` and `dense_edges` are internal:
the payload is what ships, and a consumer names the wire types through `InspectorPayload`'s fields.
`InspectedProgram::from_parts` builds a one-pane model for tests and is `#[cfg(test)]`, because the
shape it produces — one pane, no pane links — is one to assert against rather than one to serve.

**Module layout.** One concept per module, each owning its type, its inherent impl and its unit
tests, and no module depending on one below it:

| module | owns |
|---|---|
| `walk` | the IR traversal, named for `walk_children`/`walk_type_slots`: predicate children, node labels |
| `definitions` | use→binder resolution over the IR |
| `program` | `InspectedProgram` and its per-pane projections |
| `wire` | the payload types, the schema version, the payload assembly, and the pane-link projection |

The words the layout settles: an **index** is a built structure, a **lookup** is a read of one, and
the **payload** is what ships.

Unit tests live in the module they exercise. `wire.rs`'s run over a three-program `corpus()`
chosen for the shapes that reach the payload's moving parts: a comprehension for refinement
predicates, a monomorphized definition for one source span over several nodes, and a mutable loop
for a recurrence.

## Design considerations

### The wire belongs to this module

The payload's node type is this module's own. Two invariants hold the boundary: `pretty_tree`
carries no serde and no `ccl` type, so a wire change is never a diff in a renderer; and exactly one
encoder writes a `RewriteTag` to the wire, so the null-compression rule has one copy.

### Span containment is a scan

Containment is the integer test `start <= pos < end`, and a position is resolved by scanning the
shipped nodes. One program's tree is small enough that an interval tree would cost more complexity
than it saves, and the scan is the consumer's, so a structure over the spans is a change behind the
consumer's own API rather than a wire change. `intervalsets` is not used: it is built for numeric
value domains and carries a `contains` bug on half-bounded intervals (see
`src/interpreter/tiling/predicate.rs`).

### What the model cannot say

- **A pane pair cannot report that an untouched node was untouched** where the phase re-mints its
  pass-through nodes. `lambda_elim` is that phase today, so each pass-through node reads to a
  consumer as a rewrite of its predecessor — see
  [provenance.md](../ccl/design/provenance.md#the-edge-labels).
- **No pane exists past `post-planning`** until operator conversion carries a node identity. A pane
  may be issued at any point in the pipeline; that one has nothing to resolve against.
- **No channel names a binder site.** A binder is not an expression, so nothing attributes it and no
  field says which node binds the name written at a given span. The payload therefore carries no
  binder types, and a consumer clicking a binder resolves the node whose span contains it — for
  `g = "abc"` that is the whole `Let`, whose type is the type of what follows the binding. Closing
  the gap means a source span on `TypedBinding`, after which the binder's type is a read; that is a
  `ccl` change, carried as `TODO(binder-site)`.

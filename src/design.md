# Source Layout & Design Docs

An index of the `src/` tree and where each module's design notes live. For the
language overview, CHL/CCL split, and the end-to-end execution pipeline, see
[docs/design.md](/docs/design.md).

## Crate structure (`src/`)

| Path | Role | Design docs |
| --- | --- | --- |
| `ccl/` | Cambra Core Language: lowering (CHL AST → CCL), type inference, the optimization/compilation passes, and the typed AST programs lower into. | [design/](ccl/design/README.md) — IR, type inference, lowering, mutability, optimization; [CLAUDE.md](ccl/CLAUDE.md) |
| `chl_parser/` | Parser for the Cambra High-level Language: lexer, grammar, AST, and error recovery. | [design-chl-parser.md](chl_parser/design-chl-parser.md) |
| `inspector_model/` | The read-only model the program inspector serves: the snapshot payload, the span and name-binder indices, the per-pane projections, and the pane-pair links. | [design.md](inspector_model/design.md) |
| `interpreter/` | Dataflow runtime: the tile producer/consumer operators, tilings, the scheduler, and data sources/sinks. | [design-operators.md](interpreter/design-operators.md), [design-http-server.md](interpreter/design-http-server.md), [CLAUDE.md](interpreter/CLAUDE.md) |
| `pretty_graph.rs`, `pretty_tree.rs` | Human-readable rendering of the operator graph and AST trees (debug / inspector output). | — |
| `web_inspector.rs` | Live web dashboard served with `--inspect`; renders the CHL AST, lowered CCL, operator graph, and runtime producer state. Static assets in `resources/`. | — |
| `util.rs` | Cross-cutting helpers. | — |
| `main.rs`, `lib.rs` | CLI entry point and crate root (module declarations). | — |

## Operational semantics

The runtime's formal model lives under
[docs/operational-semantics/](/docs/operational-semantics/):
[summary.md](/docs/operational-semantics/summary.md) (overview),
[semantics.md](/docs/operational-semantics/semantics.md) (formal definitions),
[example.md](/docs/operational-semantics/example.md) (worked example),
[lowering.md](/docs/operational-semantics/lowering.md), and
[deprecation.md](/docs/operational-semantics/deprecation.md).

## Pass pipeline

The pass order (parse → lower → uniquify → infer → inline → mut_elim →
channelize → lambda_elim → planning → operator_conversion) and the file
implementing each pass are listed in
[docs/design.md](/docs/design.md#program-execution-pipeline).

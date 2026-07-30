# CCL Design

The **Cambra Core Language** is the small, typed core that CHL programs lower into. It carries literals, variables, records, variants, lambdas, let-bindings, application, pattern matching, refinements, and type annotations — every node denotes a pure value (see [ir.md](ir.md#purity-invariant-ccl-is-a-pure-value-language)). This directory documents the CCL **intermediate representation** and the **compiler passes** that operate on it.

For the language-level picture (CHL ↔ CCL split, the product/vision framing), see [/docs/design.md](/docs/design.md). For the runtime model that CCL compiles onto, see [/docs/operational-semantics/](/docs/operational-semantics/).

## Pass pipeline

```
CHL source
  → parse             (chl_parser)                    — CHL source → CHL AST
  → lower             (ccl/lower/)                     — CHL AST → CCL Expr          →  lowering.md
  → uniquify          (ccl/uniquify.rs)                — α-uniquify binders           →  lowering.md
  → infer             (ccl/infer/ → ccl/infer/solver/) — type inference + refinements →  type-inference.md
  → inline            (ccl/inline.rs)                  — inline scalar/UDF lets       →  optimization.md
  → transact_phase    (ccl/transact_phase.rs)          — with begin(): Mut(V,Txn) loops → get_prev_txn-guarded LetRec  →  mutability.md
  → mut_elim      (ccl/mut_elim.rs)            — induction mutation loops → get_prev_seq-causal LetRec, then plan_loops → Transact  →  mutability.md
  → channelize        (ccl/channelize.rs)              — Defer/Feed/Define → channels; feed-routing step (channelize) of mutability elimination (after infer + the mutability phases; type-preserving)  →  mutability.md §4
  → lambda_elim       (ccl/lambda_elim.rs)             — λ → point-free combinators (runs simplify internally)  →  optimization.md
  → planning          (ccl/planning/)                  — hash-join / keyed-aggregate; brackets its marker pass with simplify (ccl/simplify.rs)  →  optimization.md
  → operator_conversion (interpreter/)                 — point-free CCL → tile ops     →  optimization.md
```

## The documents

| Doc | Covers |
| --- | --- |
| [ir.md](ir.md) | The typed AST: `TypedExpr`/`Type`, the purity invariant, structured names & α-uniquification, the Lambda/Apply iteration encoding, the `Aggregate`/`Cast`/`Case`/`Transact`/`LetRec` nodes, `TypedBinding`, and the transient `Hole`/`Infer`/`Feed`/`Mut` variants. |
| [type-inference.md](type-inference.md) | Cambra's inference algorithm: the two-pass emit → coalesce engine (`ccl/infer/`), the constraint solver (`ccl/infer/solver/`), let-polymorphism, dependent Pi types and refinements, and post-inference validation. |
| [lowering.md](lowering.md) | CHL → CCL lowering: how comprehensions, lambdas, `def`s, and generators become CCL shapes, and the surface syntax of the deferred-collection operators. |
| [optimization.md](optimization.md) | The optimization/compilation passes: inlining, lambda elimination, join/aggregate planning, algebraic simplification, and conversion to tile operators. |
| [provenance.md](provenance.md) | How a node keeps its link to the source the user wrote across the whole pipeline: the `NodeId`/`Pass` identity primitives, the `RewriteStep` lineage model and its collapse, the recorder, the always-on lowering projection release diagnostics read, and what the inspector consumes. |

Provenance is the one cross-cutting concern in the table: every pass above both
preserves node identity and records what it rewrote, so
[provenance.md](provenance.md) is the doc to read before touching how a pass
rebuilds nodes.

The feed-channelization step (`ccl/channelize.rs`) has no dedicated design doc: its design of
record is [Compilation pipeline](mutability.md#compilation-pipeline) in `mutability.md` — feed
routing is the append-law half of mutability elimination — and the in-depth
implementation notes (cluster algorithm, per-shape extraction, error modes, navigation map) live in
the module's own rustdoc.

## Companion docs (elsewhere)

- [`ccl/CLAUDE.md`](../CLAUDE.md) — the load-bearing purity invariant and pass-authoring guidance.
- [`docs/operational-semantics/`](/docs/operational-semantics/) — tilings, guards, and the dataflow semantics the compiled operators obey.

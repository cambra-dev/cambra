# CCL Design

The **Cambra Core Language** is the small, typed core that CHL programs lower into. It carries literals, variables, records, variants, lambdas, let-bindings, application, pattern matching, refinements, and type annotations — every node denotes a pure value (see [ir.md](ir.md#purity-invariant)). This directory documents the CCL **intermediate representation** and the **compiler passes** that operate on it.

For the language-level picture (CHL ↔ CCL split, the product/vision framing), see [/docs/design.md](/docs/design.md). For the runtime model that CCL compiles onto, see [/docs/operational-semantics/](/docs/operational-semantics/).

## Pass pipeline

```
CHL source
  → parse             (chl_parser)                    — CHL source → CHL AST
  → lower             (ccl/lower/)                     — CHL AST → CCL Expr          →  lowering.md
  → uniquify          (ccl/uniquify.rs)                — α-uniquify binders           →  lowering.md
  → infer             (ccl/infer/ → ccl/infer/solver/) — type inference + refinements →  type-inference.md
  → inline            (ccl/inline.rs)                  — inline scalar/UDF lets       →  optimization.md
  → transact_phase    (ccl/transact_phase.rs)          — with begin(): Mut[V,Txn] loops → get_prev_txn-guarded LetRec  →  ../design-mut-txn-feed.md
  → letrec_phase      (ccl/letrec_phase.rs)            — induction mutation loops → get_prev_seq-guarded LetRec, then recognize → Transact  →  ../design-mut-txn-feed.md
  → desugar_defers    (ccl/desugar_defers.rs)          — Defer/Feed/Define → channels (after infer + the mutability phases; type-preserving)  →  desugar-defers.md
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
| [desugar-defers.md](desugar-defers.md) | The `desugar_defers` pass in depth — how `Defer`/`Feed`/`Define` clusters become let-chains and record channels. *(Active prototype; see the doc's own status notes.)* |
| [optimization.md](optimization.md) | The optimization/compilation passes: inlining, lambda elimination, join/aggregate planning, algebraic simplification, and conversion to tile operators. |

## Companion docs (elsewhere)

- [`ccl/CLAUDE.md`](../CLAUDE.md) — the load-bearing purity invariant and pass-authoring guidance.
- [`docs/operational-semantics/`](/docs/operational-semantics/) — tilings, guards, and the dataflow semantics the compiled operators obey.

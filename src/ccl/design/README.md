# CCL Design

The Cambra Core Language is the typed intermediate representation that CHL programs lower into.
Each CCL node denotes a pure value; see
[the purity invariant](ir.md#purity-invariant-ccl-is-a-pure-value-language).
This directory specifies the representation and the compiler passes that transform it.

[The language overview](../../../docs/design.md) describes the CHL/CCL boundary.
[Operational semantics](../../../docs/operational-semantics/summary.md) specifies the runtime model.

## Pass pipeline

[Program Execution Pipeline](../../../docs/design.md#program-execution-pipeline) owns the phase
order and maps each stage to its implementation and design reference. The driver is
[`context.rs`](../context.rs); `run_frontend` and `run_passes` are shared by full compilation
and phase-limited compilation. Loop recognition is included in the planning phase.

## The documents

| Doc | Covers |
| --- | --- |
| [ir.md](ir.md) | The typed AST: `TypedExpr`/`Type`, the purity invariant, structured names & α-uniquification, the single statement of binding structure (`ccl/scope.rs`), the Lambda/Apply iteration encoding, the `Aggregate`/`Cast`/`Case`/`Transact`/`LetRec` nodes, `TypedBinding`, and the transient `Hole`/`Infer`/`Feed`/`Mut` variants. |
| [type-inference.md](type-inference.md) | Cambra's inference algorithm: the two-pass emit → coalesce engine (`ccl/infer/`), the constraint solver (`ccl/infer/solver/`), let-polymorphism, dependent Pi types and refinements, and post-inference validation. |
| [type-parameters.md](type-parameters.md) | Written polymorphic types: `Type::Poly` and `Type::Param`, checking a binding against a polymorphic type, trait requirements as assumptions, instantiation at a use, and specialization. |
| [nominal-types.md](nominal-types.md) | `type` declarations: `Type::Nominal` and its declaration, constructors as functions bound around the module, subtyping by variance, and reading a nominal type's shape through its representation after inference. |
| [diagnostics.md](diagnostics.md) | How an inference diagnostic writes a type, in CHL for an annotation mismatch (`chl_print`), and the secondary labels an error carries. |
| [lowering.md](lowering.md) | CHL → CCL lowering: how comprehensions, lambdas, `def`s, and generators become CCL shapes, and the surface syntax of the deferred-collection operators. |
| [optimization.md](optimization.md) | The optimization/compilation passes: inlining, lambda elimination, join/aggregate planning, algebraic simplification, and conversion to tile operators. |
| [mutability.md](mutability.md) | The unified history model: mutable variables, transactions, and feeds as functions over a sequencing domain, eliminated into a causal `LetRec`; the `Mut`/`Feed`/`Txn` types and the loop/commit engines. |
| [collections.md](collections.md) | Collections as data functions `𝐷 ⤇ 𝑉`: the five surface types as domain shapes, the referenceable opaque domain (Σ-witness activation) behind maps/sets and runtime-length lists, membership-discharge lookup, keyed feeds, and mutable collections. |
| [provenance.md](provenance.md) | How a node keeps its link to the source the user wrote across the whole pipeline: the `NodeId`/`Phase` identity primitives, the `ProvenanceTable` model and its fold, the recorder, the always-on lowering projection release diagnostics read, and what the inspector consumes. |
| [diffing.md](diffing.md) | Program diffing: α-invariant content addressing of CCL terms and the GumTree correspondence between two compiled programs. |
| [program-evolution.md](program-evolution.md) | How a running program becomes a different program: the control-port verbs (`/diff`, `/reload`, `/branch`, `/branches`), the branch table that maps each numbered branch to the operators it holds and shares with the branch it was created from, the reload mechanism that keeps every operator whose computation is unchanged, and the *state takeover* guard. |

Branching in [program-evolution.md](program-evolution.md) is a *model*, not a
pass — nothing in the pipeline above implements it yet (`docs/design.md` marks
program branching **[Open]**), though the reload half of that doc is built. It
sits here because the analysis it turns on, divergence reachability, is a
property of the CCL dataflow graph.

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

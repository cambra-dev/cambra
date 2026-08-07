# CLAUDE.md
This file provides guidance to Claude Code (claude.ai/code) when working with code in this directory.


## Core invariant: CCL is a pure value language

**Every `TypedExprNode` variant must denote a pure value.  Effects belong at the program boundary, not inside the AST.**

Concretely: no `TypedExprNode` variant may represent an effectful operation that is executed by the CCL pipeline itself (type inference, lambda elimination, join planning, simplification).  Side-effecting operations such as I/O, network calls, or sink dispatch must be modelled as data-source/sink registrations in `LoweringContext` and wired into the interpreter at the boundary (`ccl/context.rs :: compile_program`), not as AST nodes that carry runtime behaviour.

For example, an effectful `Sink(String)` node embedding an I/O dispatch would violate this invariant: optimization passes could duplicate or reorder it, causing skipped or double-fired responses.  Sink dispatch is instead modelled as a pure `Defer` placeholder plus an out-of-band sink-binding pair — `Defer` carries no behaviour, and the actual dispatch is assembled by `compile_program` at the boundary.

If you find yourself adding a new `TypedExprNode` variant that "does something" at runtime rather than representing a value to be computed, stop and reconsider.  Model the effect at the boundary instead.


## General Instructions

### Workflow
When planning, include updates to the appropriate docs to reflect the changes; validate the docs are up to date before creating a PR. This includes the CCL design docs in `design/` (`ir.md`, `type-inference.md`, `lowering.md`, `optimization.md`, `mutability.md`, `provenance.md`, `diffing.md`, `branching.md`) and other `*/design-*.md` files close to source files that were changed.

### Node identity and lineage
Every pass rebuilds IR nodes, and every rebuild must carry the node's `NodeId` (or record the mint/copy it performs). This is not incidental bookkeeping: the always-on lowering projection is what turns an inference error into a source span, so a pass that mints where it should preserve degrades release diagnostics. Read `design/provenance.md` before changing how a pass constructs, clones, or discards nodes.

# CLAUDE.md
This file provides guidance to Claude Code (claude.ai/code) when working with code in this directory.


## Core invariant: CCL is a pure value language

**Every `TypedExprNode` variant must denote a pure value.  Effects belong at the program boundary, not inside the AST.**

Concretely: no `TypedExprNode` variant may represent an effectful operation that is executed by the CCL pipeline itself (type inference, lambda elimination, join planning, simplification).  Side-effecting operations such as I/O, network calls, or sink dispatch must be modelled as data-source/sink registrations in `LoweringContext` and wired into the interpreter at the boundary (`ccl/context.rs :: compile_program`), not as AST nodes that carry runtime behaviour.

Historically, `TypedExprNode::Sink(String)` violated this invariant: it embedded an I/O dispatch operation directly in the AST, which caused correctness issues when optimization passes duplicated or reordered nodes.  The refactor that removed it replaced the variant with a `Defer`/sink-binding pair — `Defer` is a pure placeholder, and the actual dispatch is assembled out-of-band by `compile_program`.

If you find yourself adding a new `TypedExprNode` variant that "does something" at runtime rather than representing a value to be computed, stop and reconsider.  Model the effect at the boundary instead.


## General Instructions

### Workflow
When planning, include updates to the appropriate docs to reflect the changes; validate the docs are up to date before creating a PR. This includes `design-ccl-ast.md` and other `*/design-*.md` files close to source files that were changed.

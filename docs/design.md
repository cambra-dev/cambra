# Cambra 

Cambra is a programming language that implements a new programming paradigm.
It abstracts over low level concepts like memory, threads, and connections, enabling programmers to focus on the logic of their program, non-functional requirements, and high-level architectural decisions.

The denotational semantics of the language is a pure, dependently-typed, functional language.
The operational semantics is very unlike the lambda calculus: rather than operating via term-wise beta reduction, terms implement a producer/consumer interface which allows the runtime to implement streaming dataflow semantics, with pipelining, parallelization, and vectorization.


## Cambra High-level Language (CHL)

Programs are written in a Pythonic syntax, called CHL, that uses for-comprehensions for the definition of collection-level logic. CHL is lowered to the Cambra Core Language (CCL), where it is typechecked and interpreted.

CHL ↔ Python interop is planned in the future, but not part of the MVP.


## Cambra Core Language (CCL)

CCL is the small core language that programs lower into. It contains: literals, variables, records, unions, lambdas, let-bindings, application, pattern matching, and type annotations.

To execute CCL, the interpreter walks the AST, converting each node into a **dataflow operator**. Execution is kicked off by subscribing to the top-level operator, which creates and wires together subscriptions from each operator.


A **scheduler** orchestrates the execution, triggering source operators and coordinating the work among different operators.

See [docs/operational-semantics/summary.md](operational-semantics/summary.md) for a description of CCL's operational semantics. Detailed formal definitions are in [semantics.md](operational-semantics/semantics.md).

## Program Execution Pipeline

```
Python source
  → parse            (rustpython_parser today; being replaced by chl_parser — see src/chl_parser/design-chl-parser.md)
  → lower            (ccl/lower.rs: Python AST → CCL Expr)
  → infer            (ccl/infer.rs: type inference + check_fully_typed validation)
  → inline           (ccl/inline.rs: inline UDF Let bindings with non-iterable domains; beta-reduce at call sites)
  → lambda_elim      (ccl/lambda_elim.rs: lambda → point-free combinators)
  → remove_defers    (ccl/remove_defers.rs: inline deferred collection definitions)
  → join_plan        (ccl/join_plan.rs: hash-join and keyed aggregate optimization)
  → simplify         (ccl/simplify.rs: CCC algebraic rewrites to fixed point)
  → operator_conversion  (interpreter/operator_conversion.rs: λ-free CCL → tile operators)
  → subscribe()
  → tile producer/consumer dataflow
```

For source layout and design doc locations, see [src/design.md](/src/design.md).

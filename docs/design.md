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

See [design-operational-semantics.md](design-operational-semantics.md) for a description of CCL's operational semantics: progress algebras, the model, guards, yield guards and embedded closure, the two-layer picture, protocol rules, terminology.

## Program Execution Pipeline

```
Python source
  → parse (rustpython_parser)
  → lower (lowering.rs)
  → CCL operators
  → subscribe()
  → producer/consumer dataflow
```

For source layout and design doc locations, see [src/design.md](/src/design.md).

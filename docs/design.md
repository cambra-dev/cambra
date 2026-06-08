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
CHL source
  → parse            (chl_parser, see src/chl_parser/design-chl-parser.md)
  → lower            (ccl/lower.rs: CHL AST → CCL Expr)
  → desugar_defers   (ccl/desugar_defers.rs: Defer/Feed/Define → let-chain + Record channels)
  → infer            (ccl/infer.rs: type inference via simple-sub; delegates to ccl/infer_simple_sub.rs)
  → inline           (ccl/inline.rs: inline UDF Let bindings with non-iterable domains; beta-reduce at call sites)
  → lambda_elim      (ccl/lambda_elim.rs: lambda → point-free combinators)
  → planning        (ccl/planning.rs: hash-join and keyed aggregate optimization)
  → simplify         (ccl/simplify.rs: CCC algebraic rewrites to fixed point)
  → operator_conversion  (interpreter/operator_conversion.rs: λ-free CCL → tile operators)
  → subscribe()
  → tile producer/consumer dataflow
```

For source layout and design doc locations, see [src/design.md](/src/design.md).

## Notation conventions

Design docs that mix CCL syntax with meta-theoretic variables (placeholders for any specific term, type, or predicate) italicize the placeholders using Unicode mathematical italic characters:

- Single-letter term/value metas: `𝑎` `𝑏` `𝑐` `𝑑` `𝑒` `𝑓` `𝑔` `ℎ` `𝑖` `𝑗` `𝑘` `𝑙` `𝑚` `𝑛` `𝑜` `𝑝` `𝑞` `𝑟` `𝑠` `𝑡` `𝑢` `𝑣` `𝑤` `𝑥` `𝑦` `𝑧` (U+1D44E–U+1D467, with `ℎ` at the legacy U+210E).
- Single-letter type metas: `𝐴` `𝐵` `𝐶` `𝐷` `𝐸` `𝐹` `𝐺` `𝐻` `𝐼` `𝐽` `𝐾` `𝐿` `𝑀` `𝑁` `𝑂` `𝑃` `𝑄` `𝑅` `𝑆` `𝑇` `𝑈` `𝑉` `𝑊` `𝑋` `𝑌` `𝑍` (U+1D434–U+1D44D).
- Digit subscripts: `₀` `₁` `₂` `₃` `₄` `₅` `₆` `₇` `₈` `₉` (U+2080–U+2089) for indexed variants like `𝐷₁`, `𝐶₂`.

Multi-character placeholders (`body`, `arg`, `param`, `predicate`, ...) and concrete identifiers (`xs`, `__gb_k`, `key_fn`, ...) stay upright. The convention applies to inline pseudo-code in backticks and to prose mentions; fenced code blocks (which represent literal source) stay in regular characters. String literals (`"x"`, `"k"`) are also literal, not metavariables, and stay upright.

Stars/underscores for italics don't work inside backticks — CommonMark skips emphasis parsing inside code spans. The Unicode math italic characters are pre-rendered italic glyphs that render correctly in any modern Markdown viewer (GitHub, VS Code, browsers) without needing markup.

### Function types and terms

Cambra's `Type::Fun` has an optional binder name; the symbolic form distinguishes the two cases:

- `(𝑥: 𝐴) ⇒ 𝐵` — function type with named binder. `𝑥` is bound in `𝐵` and may be referenced by refinements or other types nested there.
- `𝐴 ⇒ 𝐵` — function type with no named binder. The codomain is independent of the argument value.

Refinement types use the standard subset-type notation `{𝑥: 𝑇 | 𝑝(𝑥)}`. The function-type arrow `⇒` is right-associative: `𝐴 ⇒ 𝐵 ⇒ 𝐶` parses as `𝐴 ⇒ (𝐵 ⇒ 𝐶)`.

At the term level: `λ 𝑥 → body` is a lambda (the `→` separates the binder from the body); `𝑎 ▷ 𝑓` is forward apply (`𝑓(𝑎)` with the argument first); `𝑓 ≫ 𝑔` is forward compose (`λ 𝑥 → 𝑔(𝑓(𝑥))`).

The two arrows are deliberately distinct: `⇒` is the type arrow, `→` is the term-level lambda separator. Don't mix them.

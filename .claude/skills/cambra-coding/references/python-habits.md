# Python habits and their CHL forms

Each row was compiled on main when written, and `scripts/check_program.py` decides when a row and
main disagree. The diagnostic column is the start of the message main prints, so a
diagnostic seen while checking a program can be looked up here. Where a row cites a spec section,
that section owns the rule.

## Contents

- [Values and syntax](#values-and-syntax)
- [Functions](#functions)
- [Loops and comprehensions](#loops-and-comprehensions)
- [Missing builtins and statements](#missing-builtins-and-statements)

## Values and syntax

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `{"a": 1}` or `{a: 1}` as a record | `(a=1, b="x")`; `{…}` is type syntax only (spec [2.4 Atoms](../../../../docs/chl-spec.md#24-atoms)) | `` `{…}` is type syntax (a record type `{name: T}`); a record value is written `(name=value)` `` |
| `t[0]` on a tuple | `t.0` | `Expected function type at Apply, found (Int@1, Int@2)` with a hint to project |
| `s[0]` on a string | no string indexing; strings support `+` only | `Expected function type at Apply, found String` |
| `true`, `None` | `True`, `False`; absence is `Option::none` of `Option(T)` | `Unbound variable: 'true'` |
| `7 / 2`, `7 % 2` | `7 // 2`; there are no floats and no `%`; a remainder is `n - (n // d) * d` | `lex error: unrecognized token` |
| `f"{x}"`, `str(x)` | no formatting or conversion, `Int` to `String` included; concatenate `String`s with `+` | parse error / `Unbound variable: 'str'` |
| `if x:` on an `Int` | an explicit comparison; there is no truthiness | `Type mismatch for Case guard: expected Bool, found Int` |
| `s == "running"` on a tag | `match s:` with `` case `running: ``; variants have no `==` ([Trait requirements](../../../../docs/chl-spec.md#trait-requirements)) | `No Equatable instance for BinOp: operand 1 is {`running}, …` |
| `class Bill:` and `Bill(bill_id="42")` | `type Bill = {bill_id: String}`, built with `Bill::new((bill_id="42"))` (two parentheses: one call, one record) and read with `b.extract().bill_id` (`tests/it/compilation_pipeline/nominal_types.rs`) | parse error at `=` |
| `xs: List[int] = [1, 2]` | `xs: List(Int) = box([1, 2])`; a literal is an `Array` until boxed (spec [7.5 `box`](../../../../docs/chl-spec.md#75-box)) | `Annotation mismatch: annotated as List(Int), but inferred as Array(2, Int)` |
| `m.get(k)` | `m[k]?` gives an `Option(V)`, unwrapped with `match` arms `case Option::some(v):` and `case Option::none:`; `m[k]` needs the key proven present (spec [3.9 Subscript and attribute access](../../../../docs/chl-spec.md#39-subscript-and-attribute-access)) | — |
| `` `some(v) `` as an `Option` | `Option` is a nominal type: build `Option::some(1)`, `Option::none`; the variant `` `some(1) `` is a different type (spec [3.15 Variant constructors](../../../../docs/chl-spec.md#315-variant-constructors)) | ``Type mismatch for Case scrutinee: expected {`none{…} \| `some{…}}, found Option(Int)`` with a hint |
| `m[k]?` where `m` is a parameter | bind the collection with `=` in the scope that looks it up, or iterate it | ``Unsupported: checked lookup `c[k]?` needs the collection's type at this point…`` |

## Functions

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `lambda x: x + 1`, `(x) => x + 1` | `\x -> x + 1` (spec [3.10 Lambda](../../../../docs/chl-spec.md#310-lambda)) | parse error / `` `T => U` is a function *type* `` |
| `def f():` | every function takes at least one parameter | `function/lambda with no parameters not supported` |
| `def f(a, b=2)`, `f(a=1)` | positional parameters only; no defaults, no keyword arguments (spec [3.8 Function calls](../../../../docs/chl-spec.md#38-function-calls)) | parse error at `=` |
| `return x` | the body's last expression is its value, and an `if`/`else` whose branches are values replaces an early return; lowering refuses every `return` (spec [4.8 `return`](../../../../docs/chl-spec.md#48-return) is `[Planned]`) | `last statement must be a bare expression, if/else, or for/yield generator loop` |
| a recursive `def` | no recursion (spec [4.1 `def`](../../../../docs/chl-spec.md#41-def--function-definition)) | `Unbound variable: 'f'` |
| a generic function | `def first(T, a: T, b: T) => T:`; bounds with `requires Orderable(T, T)` (spec [6.10 Polymorphic types](../../../../docs/chl-spec.md#610-polymorphic-types)) | — |
| a `yield` generator with setup and several loops | one top-level `for` that yields, optionally after `:=` setup (spec [4.2 generator `def`](../../../../docs/chl-spec.md#42-def--generator-function)) | — |

## Loops and comprehensions

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `total = 0` then `total = total + x` in a loop | `total := 0` then `total += x` (spec [8.1 Mutation](../../../../docs/chl-spec.md#81-mutation-is-explicit-the--operator)) | ``assignment to `total` is mutation: … `=` binds immutably`` |
| a mutable variable first assigned inside the loop | declare it before the loop with `:=` | `` `acc` is a mutable variable introduced inside a for-loop body, which is not supported `` |
| `for k, v in m.items()`, `for k -> v in m` | `for v in m` binds values, so a `Set` iterates unit; carry the key in the value (spec [4.6 `for`](../../../../docs/chl-spec.md#46-for--iteration), the "[Interim]" note) | parse error at `,` / `for-loop target: only simple name targets are supported` |
| `{k: sum(...) for k, g in groupby(...)}` | `[sum([s.amount for s in g]) for g in groupby(sales, \r -> r.region)]`; the result is a map keyed by the group key, so the key needs no lookup (spec [7.2 `groupby`](../../../../docs/chl-spec.md#72-groupby); `groupby_filtered_rollup`'s test shows the keyed output) | — |
| `[[x] for x in xs]` | list literal elements are constants; build with a comprehension, e.g. `[(x, 1) for x in xs]` | ``a list element must be a constant, but this one varies with `x` `` |
| `if k in m`, `x in xs` | `match m[k]?:` (spec [3.4 Comparisons](../../../../docs/chl-spec.md#34-comparisons): membership is `[Decided]`) | parse error at `in` |
| `while` | a `for` over a collection (spec [13. Reserved for future work](../../../../docs/chl-spec.md#13-reserved-for-future-work)) | parse error |
| a loop relying on iteration order | iterations are unordered and may run in parallel; only a `:=` accumulator orders them | — |

## Missing builtins and statements

The builtins main has are the rows of `SURFACE_BUILTINS` in `chl-parser/src/builtins.rs`; a name
not there is unbound.

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `len(xs)`, `count(xs)` | `sum([1 for x in xs])` | `Unbound variable: 'len'` |
| `del m[k]` | no deletion | parse error |
| `import x`, `from x import y` | one file per program (spec [9. Modules](../../../../docs/chl-spec.md#9-modules-decided) is `[Decided]`) | `` `import` is not supported yet: a program is a single module `` |
| `try`/`except`, `assert`, `class` | absent (spec [13. Reserved for future work](../../../../docs/chl-spec.md#13-reserved-for-future-work)); use `Option` or variant results | parse error |

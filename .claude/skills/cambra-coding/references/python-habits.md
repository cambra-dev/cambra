# Python habits and their CHL forms

Each row compiled on main as written, and a run decides when a row and main disagree. The
diagnostic column is the start of the message main prints, so a diagnostic seen while running a
program can be looked up here. Where a row cites a spec section, that section owns the
rule.

## Contents

- [Values and syntax](#values-and-syntax)
- [Functions](#functions)
- [Loops and comprehensions](#loops-and-comprehensions)
- [State and transactions](#state-and-transactions)
- [Missing builtins and statements](#missing-builtins-and-statements)

## Values and syntax

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `{"a": 1}` or `{a: 1}` as a record | `(a=1, b="x")`; `{…}` is type syntax only (spec [2.4 Atoms](../../../../docs/chl-spec.md#24-atoms)) | `` `{…}` is type syntax: a record type `{field: T}` or a tuple type `{T, U}`; a map is written `[k -> v]` `` |
| `t[0]` on a tuple | `t.0` | `Expected a function, found {…}` with a hint to project |
| `s[0]` on a string | no string indexing; strings support `==` and `+` only | `Expected a function, found {String where …}` |
| `true`, `None` | `True`, `False`; absence is `Option::none` of `Option(T)` | `Unbound variable: 'true'` |
| `7 / 2`, `7 % 2` | `7 // 2`; there are no floats and no `%`; `**` is integer power; `&`, `\|`, `^` are `Bool` operators | `lex error: unrecognized token` |
| `f"{x}"`, `str(x)` | no formatting or conversion, `Int` to `String` included; concatenate `String`s with `+` | parse error / `Unbound variable: 'str'` |
| `if x:` on an `Int` | an explicit comparison; there is no truthiness | `Type mismatch for Case guard: expected Bool, found Int` |
| `y = a if c else b`, `y = if c: …` | `if` is a statement, not a value. Write a helper whose body is the `if`/`else` and bind its call; `y = with begin(): …` is the only block allowed on the right of `=` | `found 'else', expected statement` |
| `s == "running"` on a tag | `match s:` with `` case `running: ``; variants have no `==` ([Trait requirements](../../../../docs/chl-spec.md#trait-requirements)) | ``No Equatable instance for `==`: operand 1 is {`running}, …`` |
| `class Bill:` and `Bill(bill_id="42")` | `type Bill = {bill_id: String}`, built with `Bill::new(bill_id="42")` and read with `b.extract().bill_id`; `type Shape:` with one constructor per line for several, each written `circle(Int)` or `rect(Int, Int)` and built `Shape::circle(2)` ([6.8 Nominal types and methods](../../../../docs/chl-spec.md#68-nominal-types-and-methods)) | parse error |
| `LIMIT = 3` | a capitalized name declares a type alias; name a constant in `snake_case` | `` `LIMIT` is capitalized, so `LIMIT = …` declares a type alias `` |
| `xs: List[int] = [1, 2]` | `xs: List(Int) = box([1, 2])`; a literal is an `Array` until boxed (spec [7.4 `box`](../../../../docs/chl-spec.md#74-box)) | `Annotation mismatch: annotated as List(Int), but inferred as Array(2, Int)` |
| `m: dict = {…}` as a `Map` | `box(map([k -> v, …]))`; `map(…)` re-keys a list of pairs, `box` makes it a `Map` | ``(a plain collection reached a sum — a collection becomes a sum only through `box`)`` |
| `m = {}` as an empty map | there is no empty map: `box(map([]))` cannot be typed, even under a `Mut(Map(…))` annotation. Seed the map with a placeholder entry, such as `"" -> …`, and skip it where the map is read | `The width of the tuple {_, ..} is never fixed` |
| `m.get(k)` | `m[k]` is an `Option(V)`, unwrapped with `match` arms `case Option::some(v):` and `case Option::none:`; `m[k]!` unwraps only where the key is proven present (spec [3.9 Subscript and attribute access](../../../../docs/chl-spec.md#39-subscript-and-attribute-access)) | `?` after `m[k]` is `lex error: unrecognized token` |
| `` `some(v) `` as an `Option` | `Option` is a nominal type: build `Option::some(1)`, `Option::none`; the variant `` `some(1) `` is a different type (spec [3.15 Variant constructors](../../../../docs/chl-spec.md#315-variant-constructors)) | `Type mismatch for the matched value: expected Option(…)` with a hint |
| `m[k]` where `m` is a parameter | bind the collection with `=` in the scope that looks it up, or iterate it | ``Unsupported: checked lookup `c[k]` needs the collection's type at this point…`` |

## Functions

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `lambda x: x + 1`, `(x) => x + 1` | `\x -> x + 1`, `\ -> 3` (spec [3.10 Lambda](../../../../docs/chl-spec.md#310-lambda)) | parse error / `` `T => U` is a function *type* `` |
| `def f(a, b=2)` | no default values. `f(a=1, b=2)` is one record argument, `f((a=1, b=2))`, read as `r.a` (spec [3.8 Function calls](../../../../docs/chl-spec.md#38-function-calls)) | parse error at `=` |
| `f(1, b=2)` | all positional or all named | `a call's arguments are all positional or all named` |
| `return x` | the body's last expression is its value; an `if`/`else`, `match` or `try` whose branches end in values replaces an early return. Lowering refuses every `return`, although the spec's unmarked text describes it | `last statement must be a bare expression, if/else, or for/yield generator loop` |
| a recursive `def` | no recursion (spec [4.1 `def`](../../../../docs/chl-spec.md#41-def--function-definition)) | `Unbound variable: 'f'` |
| calling a `def` defined further down the file | define a function above its first use; there are no forward references | `Unbound variable: 'g'` |
| `def run(…)` | `run` is a keyword, the statement that runs a module; choose another name | ``found 'run', expected function name`` |
| `f: Callable[[int], int]` on a callback parameter | leave it unannotated, `def apply(f, x)`, so the callback's capabilities are inferred, or write `f: (Int => Int requires _ causes _)`, parenthesized in a parameter list. `f: Int => Int` admits only a function that requires and causes nothing (spec [6.9 Capabilities](../../../../docs/chl-spec.md#69-capabilities)) | ``this has `Transaction`, which the function type it must have does not state`` |
| a generic function | `def first(T, a: T, b: T) => T:`; bounds with `requires Orderable(T, T)` (spec [6.10 Polymorphic types](../../../../docs/chl-spec.md#610-polymorphic-types)) | — |
| `raise E()` after `case …:` on one line | a `case` line takes an expression; put a statement such as `raise` or `x := …` in the arm's indented block | ``found 'raise', expected expression, or indented block`` |
| a `yield` generator with setup and several loops | one top-level `for` that yields (spec [4.2 generator `def`](../../../../docs/chl-spec.md#42-def--generator-function)) | — |

## Loops and comprehensions

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `total = 0` then `total = total + x` in a loop | `total := 0` then `total += x` (spec [8.1 Mutation](../../../../docs/chl-spec.md#81-mutation-is-explicit-the--operator)) | ``assignment to `total` is mutation: … `=` binds immutably`` |
| a variable that should carry across iterations, first assigned inside the loop | declare it before the loop with `:=`. A `:=` inside a loop body introduces a variable that restarts each iteration ([4.6 `for`](../../../../docs/chl-spec.md#46-for--iteration)); main refuses one in a loop that writes no variable declared outside it | `` `acc` is a mutable variable introduced inside a for-loop body, which is not supported `` |
| `for k, v in m.items()`, `for k -> v in m` | a tuple pattern destructures, `for (a, b) in pairs`, but `for v in m` binds a map's values, so carry the key in the value (spec [4.6 `for`](../../../../docs/chl-spec.md#46-for--iteration), the "[Interim]" note) | ``Type mismatch for projection `.1`: expected {‹?1›, ‹?2›, ..}, found Int`` |
| `{k: sum(...) for k, g in groupby(...)}` | `[sum([s.amount for s in g]) for g in groupby(sales, \r -> r.region)]`; the result is a map keyed by the group key (spec [7.2 `groupby`](../../../../docs/chl-spec.md#72-groupby)) | — |
| `[[x] for x in xs]` | list literal elements are constants; build with a comprehension, e.g. `[(x, 1) for x in xs]` | ``a list element must be a constant, but this one varies with `x` `` |
| `if k in m`, `x in xs` | `match m[k]:`, or `sum([1 for y in xs if y == x]) > 0` (spec [Membership expressions](../../../../docs/chl-spec.md#membership-expressions-decided) is `[Decided]`) | parse error at `in` |
| `while` | a `for` over a collection (spec [13. Reserved for future work](../../../../docs/chl-spec.md#13-reserved-for-future-work)) | parse error |
| statements with side effects run top to bottom | only a dependency orders two statements: one uses the other's result, they share a variable, or the earlier one may raise. Chain the calls' results, or `raise` on failure, to sequence them ([The model](../SKILL.md#the-model); spec [8.5 Ordering and concurrency](../../../../docs/chl-spec.md#85-ordering-and-concurrency)) | — |
| a loop relying on iteration order | iterations are unordered and may run in parallel; writing a variable declared outside the loop orders them by position ([Ordered loops](../../../../docs/chl-spec.md#ordered-loops)) | — |

## State and transactions

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `out = []` then `out.append(v)` | `out: Feed(_)` then `out << v`; `defer()` is gone (spec [Declaring a feed](../../../../docs/chl-spec.md#declaring-a-feed)) | `` `defer()` no longer introduces a feed `` |
| a global shared by two handlers | `x: Mut(V, Txn) := init`, read and written only inside `with begin():` or a function it calls | ``this requires `Transaction` outside a `with begin():` block`` |
| a helper that opens its own transaction, called from another | open the block at the outermost caller; a function called inside a block joins its transaction | ``this commits a transaction inside a `with begin():` block's body, directly or through a call; transactions do not nest`` |
| a `for` inside `with begin():` | a block holds no loop, so a transaction writes the keys its code names. Loop outside and open a block per iteration, or read a collection with a comprehension inside the block | ``a `with begin():` block supports mutable writes (`x := …`, `x += …`), local bindings`` |
| importing a module that keeps a counter | `run counter as c`, then call `c::bump(…)` inside a block; a module whose top level writes `Txn` state is run ([9.7 Importing asserts a shareable module](../../../../docs/chl-spec.md#97-importing-asserts-a-shareable-module)) | ``module `counter` is run, since its top level causes `WriteTxn(count)`, so importing it is an error: run it instead`` |
| a name assigned inside `with` and used after | `v = with begin(): …` binds the block's last value; a plain binding inside the block ends with it | `Unbound variable: 'got'` |
| `with begin(): pass` | a block writes a `Txn` variable or feeds something | ``this `with begin():` block does nothing`` |
| a mutable field in an object | `Mut` appears only at the top of a declaration or parameter annotation | ``unknown type application: `Mut(…)` `` |
| `with lock as t:`, `abort()` | `with begin():`; a guard that writes nothing, or an exception escaping the block, declines (spec [8.7](../../../../docs/chl-spec.md#87-transactions-as-contextual-parameters)) | ``the `with t = begin():` transaction handle is not supported yet`` |
| `del state` across a deploy | load it into a name nothing reads; `@Discard` is `[Decided]` ([reload.md](reload.md)) | `` `@Discard` is not supported yet `` |

## Missing builtins and statements

The builtins main has are the rows of `SURFACE_BUILTINS` in `chl-parser/src/builtins.rs`; a name
not there is unbound.

| Python habit | CHL | Diagnostic for the habit |
| --- | --- | --- |
| `len(xs)`, `count(xs)` | `sum([1 for x in xs])` | `Unbound variable: 'len'` |
| `s.split(" ")`, `s.startswith(p)`, `int(s)` | none exist: strings support `==` and `+` only. Compare a whole string against each string expected, or take each value on its own route or input | ``no type this module declares or reaches has a method `split` `` / `Unbound variable: 'int'` |
| `os.environ["API_KEY"]`, a config file | configuration is not supported: there is no environment, file or configuration access. Write the value as a literal | `Unbound variable: 'env'` |
| `del m[k]` | no deletion | parse error |
| `import x` | loads `x.cambra` beside the root file; a module with state is `run`, not imported ([9. Modules](../../../../docs/chl-spec.md#9-modules)) | ``no module `x`: there is no file `x.cambra` `` |
| a module parameter used as a route's port, method or path | declare it `const param path: String`; `http_serve` takes constants only | `` `path` is a parameter without `const`, so it is not a constant `` |
| `assert`, `class` | absent (spec [13. Reserved for future work](../../../../docs/chl-spec.md#13-reserved-for-future-work)); use `type`, `raise`, `Option` or variant results | parse error |
| a capitalized entry file | a root file's name starts with a lowercase letter | ``the root file `Main.cambra` does not name a module`` |

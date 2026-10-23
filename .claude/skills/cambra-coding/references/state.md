# State, transactions, feeds and reload

The rules below are what a program author applies at the keyboard. Each links the section that owns
it; read that section when a case is not covered here.
[mutability-walkthrough.md, "4. What a programmer writes"](../../../../docs/mutability-walkthrough.md#4-what-a-programmer-writes)
is the author-facing explanation of all of it, with worked programs.

## Contents

- [Two kinds of mutable variable](#two-kinds-of-mutable-variable)
- [Transactions](#transactions)
- [Reads](#reads)
- [Feeds and where a `<<` sits](#feeds-and-where-a--sits)
- [Hot reload](#hot-reload)

## Two kinds of mutable variable

Spec: [8.1 Mutation is explicit](../../../../docs/chl-spec.md#81-mutation-is-explicit-the--operator).

- **Induction:** `total := 0`, written with `:=`, `+=`, `-=`, `*=`, `//=`. One owner, ordered by the
  loop that writes it. After the loop, a bare `total` is its final value.
- **Transactional:** `balance: Mut(Int, Txn) := 0`. The only form of state shared between
  concurrent loops, such as two HTTP routes. `Txn` is never inferred; spell it.
- A keyed map is `m: Mut(Map(String, Int), Txn) := empty_map()`, written per key with
  `m[k] := v`.
- `Mut` appears only at the top of a declaration or parameter annotation, never inside a record,
  tuple or collection type (`unknown type application: Mut(…)`). A `Mut(Int)` parameter is
  pass-by-reference and its argument is a bare mutable variable.
- A mutable variable is declared before the loop that writes it, never inside the loop body or a
  `with begin():` block.

## Transactions

Spec: [8.2 Transactions](../../../../docs/chl-spec.md#82-transactions-with-begin). The cases main
refuses are in
[mutability.md, "Not yet implemented"](../../../../src/ccl/design/mutability.md#not-yet-implemented).

- Every read and write of a `Txn` variable is inside `with begin():`. The block's writes commit
  atomically, and its reads see one snapshot plus its own writes.
- A block writes or feeds something; an empty or read-only-and-silent block is refused.
- `if`/`elif`/`else` and `match` go inside the block. A block inside an `if` in a loop body is
  refused (`move it to the loop's top level`), and so is a block inside a nested `for` or a
  generator.
- Blocks do not nest. `with t = begin():`, `abort()` and `requires Transaction` are not implemented
  (spec [8.7](../../../../docs/chl-spec.md#87-direction-decided-transactions-as-contextual-parameters)
  is `[Decided]`). A guard that does not write is how a transaction declines.
- A function cannot write a `Txn` variable on the caller's behalf; the write is in the block.

## Reads

Spec: [8.3 Reads](../../../../docs/chl-spec.md#83-reads) and
[8.6 `await_final`](../../../../docs/chl-spec.md#86-await_final).

- A `Txn` read outside a block is refused: `read transactional variable `n` inside a `with begin():`
  block (or `await_final(n)` for its final committed value)`.
- A value fed out of a block that does not write the variable is an as-of sample at an arbitrary
  commit position, not the latest value and not the final one.
- `await_final(x)` is the only read of a final value. It sits outside every block, and nothing names
  `x` after it. A test that asserts a `Txn` variable's value reads it with `await_final`.
- Commit order is chosen at run time. Two transactions from one loop commit in either order.

## Feeds and where a `<<` sits

Spec: [3.7 Feed operator](../../../../docs/chl-spec.md#37-feed-operator-),
[7.3 `defer`](../../../../docs/chl-spec.md#73-defer) and
[8.4](../../../../docs/chl-spec.md#84-feeds-are-the-second-form-of-mutability). The placement table
is
[mutability-walkthrough.md, "Where a `<<` sits decides what it means"](../../../../docs/mutability-walkthrough.md#where-a--sits-decides-what-it-means).

- `out = defer()` makes a feed; `out << v` appends; the program's trailing `out` is its output.
- `reqs, resps = http_serve("8080", "POST", "/path")` sits at the top level. Each request is its
  body as a `String`, and `resps << v` inside `for req in reqs:` answers that request with `v` as
  the response body, which is a `String`. Structured
  requests (`req.body.key`), status codes and `http.serve` are not implemented
  ([7.4 Sources](../../../../docs/chl-spec.md#74-sources)).
- A `<<` inside the block that writes fires only when the transaction commits. A `<<` outside any
  block fires every iteration and cannot read a `Txn` variable. A `<<` inside a read-only block is
  an as-of sample. To reply only when a write happened, put the reply in the writing block.
- A `for` whose body neither feeds, yields, writes an outer mutable variable, nor branches does
  nothing.

## Hot reload

Spec: [8.8 `@LoadFrom`](../../../../docs/chl-spec.md#88-loadfrom). Mechanism and refusals:
[program-evolution.md, "State takeover"](../../../../src/ccl/design/program-evolution.md#state-takeover)
and ["Six refusals"](../../../../src/ccl/design/program-evolution.md#six-refusals). The control port
is [program-evolution.md, "The control port"](../../../../src/ccl/design/program-evolution.md#the-control-port).

- Run with `--control[=PORT]` (default `DEFAULT_CONTROL_PORT` in `src/main.rs`); `POST` the new
  source to `/diff` to preview and to `/reload` to swap. The route table is the module comment of
  `src/control_port.rs`.
- A mutable variable keeps its value across a reload when the new version declares it under the
  same name at a type its value fits.
- A load binds a plain value: `@LoadFrom(old)` on an annotation-only declaration `held: T`, with
  `T` the value type, not `Mut(T, Txn)`. A rename then introduces the new mutable variable from it,
  `new_name: Mut(T, Txn) := held`. The argument of `@LoadFrom` is a name, never a field or
  expression, and the load is valid only on a reload, not on a cold start.
- A reload that drops a stateful variable is refused (`` `x` is no longer declared ``), and
  `@Discard` is not implemented. Retire a variable by loading it into a name nothing reads.
- Any state whose type mentions a nominal type (`type Bill = …`) is refused on reload.
- One version runs at a time. Drain-style versioning, running two versions side by side, is
  `[Open]`.

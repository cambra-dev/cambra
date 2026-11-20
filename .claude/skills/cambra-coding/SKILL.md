---
name: cambra-coding
description: Write, edit, or review CHL programs, the Cambra language (`.cambra` files), so they compile and run on Cambra main. Use when writing or changing any `.cambra` source or CHL code, even when the request only says "write a Cambra program".
paths:
  - "**/*.cambra"
---

# Writing CHL

CHL looks like Python and is not Python. A program is a dataflow graph: the compiler turns every
statement into operators over collections, and a live source such as `stdin()` or an HTTP route
keeps the graph running. Most broken CHL is a Python habit, a construct the spec marks as not
implemented, or syntax copied from a program that does not compile.

## The model

- **Collections are unordered bags.** A list literal, a comprehension, a generator's yields and a
  feed are all bags. A `for` loop's iterations run in any order, in parallel included, unless the
  loop writes a variable declared outside it; then they run one at a time in the source's position
  order ([Ordered loops](../../../docs/chl-spec.md#ordered-loops)).
- **Statements are not sequenced by where they are written.** Execution is concurrent by default:
  two statements run in either order, or at once, unless a dependency connects them, and a side
  effect is not a dependency. The three calls in this loop body are unordered, though each causes
  `AffectWorld`, because no call can fail and none uses another's result:

  ```python
  for order in orders:
      financial_client::authorize(order)
      fulfill(order)
      financial_client::charge(order)
  ```

  Three things order one statement before another:
  - **A value.** The later statement consumes what the earlier one returned:
    `auth = authorize(order)`, then `fulfill(auth)`. Matching on a returned `Option` or `Result`
    consumes it too.
  - **A variable.** One statement writes a variable the other reads or writes.
  - **An exception.** The earlier statement may raise (`causes Raise(T)`), so what is written after
    it runs only where it did not raise.

  Appends to a feed commute, so `<<` orders nothing
  ([8.5 Ordering and concurrency](../../../docs/chl-spec.md#85-ordering-and-concurrency)).
- **`=` binds once; `:=` declares and writes a mutable variable.** Declare it before the loop that
  writes it. After the loop, a bare reference is its final value
  ([8.1](../../../docs/chl-spec.md#81-mutation-is-explicit-the--operator)).
- **State shared between loops is `x: Mut(V, Txn) := init`.** It is read and written only inside
  `with begin():`, or in a function such a block calls. The blocks of a loop commit in an order the
  runtime picks, and each block reads one snapshot plus its own writes. `await_final(x)` is the only
  read of a final value ([8. Mutability, transactions, and
  feeds](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds)).
- **Output is a feed.** `out: Feed(_)` then `out << v`. An HTTP reply is `resps << v` in the loop
  over that route's requests. A `<<` inside a block is sent only if the block commits
  ([3.7 Feed operator](../../../docs/chl-spec.md#37-feed-operator-)).
- **A program's value is its last expression.** A program with any sink, `http_serve` included,
  produces only its sinks and discards its last expression without a diagnostic
  ([10. Sinks](../../../docs/chl-spec.md#10-sinks)).
- **A function's type states its capabilities.** `requires` lists what a call takes from where it
  is made, such as `Transaction` or `ReadTxn(x)`. `causes` lists what it does besides returning,
  such as `WriteTxn(x)`, `Append(out)`, `Raise(T)` or `RunTransaction`. Inference derives both from
  the body and passes them on to every caller, so a contract is written only to bound it. Touching a
  `Txn` variable requires `Transaction`, which only a `with begin():` body supplies; a block causes
  `RunTransaction`, so blocks do not nest. A function-typed parameter annotated without clauses,
  `f: Int => Int`, admits only a function that requires and causes nothing
  ([6.9 Capabilities](../../../docs/chl-spec.md#69-capabilities)).
- **A file is a module.** `import` brings in a shareable module's `pub` members; `run` starts a
  module that holds state or serves routes, once per `run` statement. A module whose top level
  writes `Txn` state is run, never imported ([9. Modules](../../../docs/chl-spec.md#9-modules)).

## Read an example before writing

Each example is a complete program whose comments carry the rules, and the repository's tests run
each one, so they compile on main. Read the one closest to the task first:

| Example | Shows |
| --- | --- |
| [sales_report.cambra](examples/sales_report.cambra) | records, tags, `map` and `Option` lookup, a nominal type with a method, a refinement, a join, `groupby`, a generator |
| [inventory_service.cambra](examples/inventory_service.cambra) | HTTP routes sharing `Txn` state, a function writing in its caller's block and the contract inferred for it, `raise`/`try`, a block's value as the reply |
| [command_stream.cambra](examples/command_stream.cambra) | `stdin()`, a streaming filter, an ordered accumulator loop, when an aggregate over a live source answers |
| [modules/shop.cambra](examples/modules/shop.cambra) | `import`, `run … as`, `param`, `pub` state and the contract of a function over it, `await_final` across runs |

[references/python-habits.md](references/python-habits.md) maps each Python habit to its CHL form
and the diagnostic main prints for it; look a diagnostic up there. Hot reload, `@LoadFrom` and the
reload refusals are in [references/reload.md](references/reload.md).

## Run and test every program

`cambra` is the binary `cargo build --release` puts at `target/release/cambra`. Running a program
compiles it first, and every compile error prints before anything runs. Run under `timeout`,
because a run that never finishes prints nothing useful:

- **Finite program:** `cambra prog.cambra`. Each result prints as `Got value: <tile>`. A scalar
  prints as `Scalar(Ints([3]))`. A list, map or feed prints as `DataFunction { domain: …,
  codomain: … }`, whose `codomain` lists the values in the order of `domain`'s keys. A feed prints
  only when it is the program's last expression: `out << v` with another last expression prints
  that expression alone.
- **`stdin()` program:** `printf 'a\nb\n' | cambra prog.cambra`.
- **HTTP program:** start it in the background, `curl` each route, then stop it.

Test a program as in any language. Choose inputs that exercise each path: a literal list, a stdin
file, a sequence of HTTP requests. Work out each expected output by hand before running, keep the
inputs and outputs with the program, and rerun them after every change. A program is done when every
run prints the value worked out by hand.

A module that another file runs or imports has no run of its own. `cambra check lib.cambra` checks
it alone and prints its interface: each `pub` member's contract, capabilities included
([9.14 Checking a module on its own](../../../docs/chl-spec.md#914-checking-a-module-on-its-own)).
Test it by running a root that uses it.

## A panic, a hang, or a wrong answer is a compiler bug

A diagnostic is the compiler rejecting the program; fix the program. A Rust panic, a stack overflow,
a run that never finishes, a wrong answer, or `internal compiler error in …` is a defect in the
compiler. Rewriting the program until the symptom disappears hides the defect. For each one:

1. Minimize the program to the smallest one that still fails, and keep it.
2. Find the nearest working neighbour, such as the same shape without the `try`, or over a literal
   list instead of `stdin()`. The difference between the two is the report.
3. Report the repro and its neighbour to the user. A program may use the neighbour's shape as a
   workaround only with a comment naming the bug, and the report lists every workaround.

## Which source says what compiles

Trust these in order; a lower source that disagrees with a higher one is stale.

1. **The compiler**, through a run.
2. **The tests.** `tests/it/compilation_pipeline/` holds the CHL cases, one file per feature. Grep
   there for a construct before writing it.
3. **The unmarked text of [chl-spec.md](../../../docs/chl-spec.md).** Its
   [status markers](../../../docs/chl-spec.md#how-to-read-this-document-status-markers) mean:
   unmarked is implemented; `[Planned]`, `[Decided]`, `[Tentative]` and `[Open]` are not. A marker
   can lag the implementation in either direction.
4. **[design.md](../../../docs/design.md), the README, and the gallery programs under
   `tests/programs/` whose `mod.rs` expects a compile error** are orientation only. Never copy syntax
   from them.

---
name: cambra-coding
description: Write, edit, or review CHL programs (`.cambra` files) so they compile and run on Cambra main, and add CHL programs to the test corpus. Use when writing or changing any `.cambra` source, a CHL snippet inside a Rust test (`indoc!` programs in `tests/`), a gallery program under `tests/programs/`, or CHL example code in a design sketch, even when the request only says "write a Cambra program" or "add a test program".
paths:
  - "**/*.cambra"
  - "tests/programs/**"
  - "tests/it/compilation_pipeline/**"
---

# Writing CHL

CHL looks like Python and is not Python. Most broken CHL is a Python habit, a construct the spec
marks as not implemented, or syntax copied from a program that does not compile. This skill says
which sources to trust, what to imitate, and how to check a program before calling it done.

## Which source says what compiles

Trust these in order. A lower source that disagrees with a higher one is stale.

1. **The compiler.** Run `scripts/check_program.py` (below) on the program.
2. **The tests.** `tests/it/compilation_pipeline/` holds the CHL cases, one file per feature; list
   the directory for the features. Grep there for a construct before writing it. Each
   `tests/programs/<name>/mod.rs` pins its program's result or its rejection.
3. **The unmarked text of [chl-spec.md](../../../docs/chl-spec.md).** Its
   [status markers](../../../docs/chl-spec.md#how-to-read-this-document-status-markers) mean:
   unmarked is implemented; `[Planned]`, `[Decided]`, `[Tentative]` and `[Open]` are not. A marker
   can lag the implementation in either direction, which is why the tests rank above the spec.
4. **[design.md](../../../docs/design.md) and the README** are orientation only. Their code may be
   target syntax that main rejects. Never copy syntax from them.

## Imitate these programs

A gallery program's `mod.rs` says whether it runs. One that asserts a result (`expect_scalar`,
`expect_stdin_program`, or requests whose replies it checks) runs; one that calls
`expect_compile_error` or `expect_compile_error_past` is blocked or rejected by design. The status
column of [demo-programs.md](../../../docs/demo-programs.md#programs) summarizes it. Imitate the
working ones, after confirming the `mod.rs` still asserts a result:

| Program | Shows |
| --- | --- |
| `tests/programs/inner_join/program.cambra` | records `(a=1)`, a comprehension join |
| `tests/programs/groupby_rollup/program.cambra` | `groupby` with a `\r -> r.k` lambda, `sum` |
| `tests/programs/generator_pipeline/program.cambra` | `def` with `yield`, composed generators |
| `tests/programs/source_accumulator/program.cambra` | `stdin()` and a `:=` accumulator |
| `tests/programs/txn_multi_read/program.cambra` | `Mut(Int, Txn)`, a guard inside a block, `await_final` |
| `tests/programs/http_greeter/program.cambra` | `http_serve` routes, replying with `<<` |
| `tests/programs/http_counter/program.cambra` | shared `Txn` state across two HTTP routes |

Do not imitate a blocked program (`grep -l expect_compile_error tests/programs/*/mod.rs`). Most are
north-star programs written in the target syntax, and their tests pin the compile error that blocks
them. The same holds for CHL in a design doc or in another
repository: it compiles only if a test says so.

## The differences that matter

[references/python-habits.md](references/python-habits.md) is the table of Python habits and their
CHL forms, each with the diagnostic main prints. Read it before writing a first program. The
model behind it, with the spec section that owns each rule:

- **A program is one file and one module.** `import`, `run`, `param` and `pub` are refused
  ([9. Modules](../../../docs/chl-spec.md#9-modules-decided) is `[Decided]`). Its value is its
  last expression, or the record of its sinks ([10. Sinks](../../../docs/chl-spec.md#10-sinks)).
- **Collections are unordered and `for` iterations run in any order**
  ([Collections are unordered](../../../docs/chl-spec.md#collections-are-unordered)). A `:=`
  accumulator is the only thing that serializes a loop. Commit order is not source order.
- **`=` binds once; `:=` declares and writes a mutable variable**
  ([8.1](../../../docs/chl-spec.md#81-mutation-is-explicit-the--operator)). Shared state is
  `x: Mut(V, Txn) := init`, read and written only inside `with begin():`
  ([8.2](../../../docs/chl-spec.md#82-transactions-with-begin),
  [8.3](../../../docs/chl-spec.md#83-reads)).
- **Output is a feed.** `out = defer()` then `out << v`; an HTTP reply is `resps << v` inside
  the request's loop ([3.7](../../../docs/chl-spec.md#37-feed-operator-)). Where a `<<` sits
  relative to a `with begin():` block changes what it reads.

[references/state.md](references/state.md) covers mutation, transactions, feeds and hot reload:
the placement rules, the read that gives a final value, and the reload refusals. Read it before
writing any `:=`, `Txn` or `<<`.

## Check every program

Run the checker on every program you write or change:

```bash
python3 .claude/skills/cambra-coding/scripts/check_program.py path/to/prog.cambra
```

It compiles without running and prints `file:line:col: message` per diagnostic. Exit 0 means it
compiles, 1 means a diagnostic, 2 means the compiler crashed or ran past its timeout
(`CAMBRA_CHECK_TIMEOUT`, default 60 seconds). It builds with `cargo run --release`
unless `CAMBRA_BIN` names a built binary. Compiling an `http_serve` program binds its port, so a
port another process holds is reported as `failed to bind port`.

A compile does not exercise the runtime, so then run the program under `timeout`, since a run that
never finishes prints nothing:

- **Finite program:** `cargo run --release -- prog.cambra`. Each pulled output prints as
  `Got value: <tile>`; a compile error exits 1.
- **`stdin()` program:** `printf 'a\nb\n' | cargo run --release -- prog.cambra`.
- **HTTP program:** start it in the background, `curl` each route, then stop it. A gallery
  program's `{PORT}` placeholder is substituted by its test; replace it with a literal port.
- **Reload:** `cargo run --release -- --control prog.cambra`, then
  `curl -X POST --data-binary @v2.cambra localhost:8081/reload`. A refusal is a 400 naming the
  conflict. The routes are the table in `src/control_port.rs`'s module comment, and the default
  port is `DEFAULT_CONTROL_PORT` in `src/main.rs`.

Work out the expected output by hand before running, and compare every value. A program that
compiles and runs can still print a wrong answer, and a wrong answer is a compiler bug like the
ones below. A program is done when its run prints the value worked out by hand.

## A panic, a hang, or an internal compiler error is a compiler bug

A diagnostic is the compiler rejecting the program; fix the program. A Rust panic, a stack
overflow, a run that never finishes, a wrong answer, or `internal compiler error in …` is a defect
in the compiler. Rewriting the program until the symptom disappears hides the defect. For each
one:

1. Minimize the program to the smallest one that still fails, and keep it.
2. Find the nearest working neighbour, such as the same shape over a literal list instead of
   `stdin()`. The difference between the two is the report.
3. Grep `tests/` for the panic message. A test already pinning it (`should_panic` or `#[ignore]`)
   is a known bug; cite it.
4. Report the repro, its neighbour and any pinning test to the user. A program may use the
   neighbour's shape as a workaround only with a comment naming the bug and its repro, and the
   report lists every workaround.

## Adding a program to the test corpus

- **Gallery program:** `tests/programs/<name>/program.cambra` and `mod.rs`, plus a `mod <name>;`
  line in `tests/programs/mod.rs` and a row in
  [demo-programs.md](../../../docs/demo-programs.md#programs). `mod.rs` asserts with a `pub fn`
  from `tests/programs/common/mod.rs`; each one's doc comment says when it applies, and
  `expect_scalar`'s lists the canonical output forms. Run with
  `cargo test --test it programs::<name>`.
- **Pipeline case:** a test in the feature's file under `tests/it/compilation_pipeline/`, using a
  `check_*` helper from `helpers.rs`. Inline programs use `indoc!`. Grep the file first; one case
  per behaviour.
- **Pinning a compiler bug:** pin the failure, so the test goes red the day the failure changes.
  Never `#[ignore]` it: an ignored test reports the same green whether the bug was fixed, moved, or
  never ran, and nothing runs ignored tests here. Each failure has its pin:
  - A panic: a test that asserts the correct result, marked
    `#[should_panic(expected = "<stable part of the panic>")]`.
    `grep -rn -B15 'should_panic(expected' tests/it/compilation_pipeline/` finds the models.
  - A wrong answer: a gallery program pins the current output with
    `expect_scalar_currently_buggy`.
  - A hang: run the program as a subprocess of the `cambra` binary, as `expect_stdin_program`
    does, and assert it is still running at a deadline of a few seconds, then kill it. A thread
    cannot be killed, so a hang pinned in-process keeps a core busy for the rest of the suite.

  Two bugs on two spellings of one program get one pin each. The doc comment states the correct
  behaviour and the narrowing.

## CHL in a design sketch

A sketch may use constructs main lacks. Keep it checkable:

- Check each construct against the spec before marking it. A construct the spec already decides is
  cited by a link to its heading (`[8.8 @LoadFrom](docs/chl-spec.md#88-loadfrom)`), not marked as
  new. A bare `§8.8` is uncheckable
  ([Referencing docs and sections](../../../CLAUDE.md#referencing-docs-and-sections)).
- Cite a spec rule; do not restate it. A sketch that re-derives the transaction read rule or the
  reload pairing in its own words drifts from the spec on the next spec change.
- Mark only what the spec lacks, with one marker, and list those constructs in one place.
- The unmarked spec text binds a sketch too. A sketch that puts a `Mut` inside a record, builds a
  workflow inside a `def`, or reads a `Txn` variable outside a block contradicts implemented rules,
  not missing features.

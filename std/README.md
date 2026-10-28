# The CHL standard library

This directory is the std root ([9.16 The std root](../docs/chl-spec.md#916-the-std-root)): the CHL
source of the modules every program can reach under the `std` path. The std root is [Planned], and
the modules here are proposed: the spec does not describe them yet, no module here compiles, and
the compiler does not embed them. `[proposed]` marks each construct a file uses that the compiler
lacks, and the programs under `tests/` pin the errors the compiler reports for them
([Tests](#tests)).

## Layout

A module's path is its file's path under this directory, with `std` in place of the directory
([9.15 Module files](../docs/chl-spec.md#915-module-files)):

| Module | File | Used by | Holds |
| -- | -- | -- | -- |
| `std::time` | [time.cambra](time.cambra) | `import std::time` | `Instant`, `Duration`, `now()`, durations, and conversions to integer counts and Unix time |
| `std::time::timer` | [time/timer.cambra](time/timer.cambra) | `run std::time::timer(Key=K) as t` | Keyed one-shot timers: `register`, `cancel`, `pending`, `fired` |
| `std::retry` | [retry.cambra](retry.cambra) | `import std::retry` | Retry policy: reply classification, backoff, deadlines, `transient_http_retry` |
| `std::wf` | [wf.cambra](wf.cambra) | `import std::wf` | The workflow library's shared types, traits and client contract ([workflow_library.md](../docs/libs/workflow_library.md)) |
| `std::wf::workflow` | [wf/workflow.cambra](wf/workflow.cambra) | `run std::wf::workflow(…) as w` | A workflow's run table, limits and `for_each` |
| `std::wf::effect` | [wf/effect.cambra](wf/effect.cambra) | `run std::wf::effect(…) as e` | Calls to a remote, once per key: `send_request`, retries, cancellation |
| `std::wf::schedule` | [wf/schedule.cambra](wf/schedule.cambra) | `run std::wf::schedule(…) as s` | A child workflow with one run per parent run per slot |
| `std::wf::detached` | [wf/detached.cambra](wf/detached.cambra) | imported by `std::wf::workflow` | The default parent: a workflow with no runs |

- **A module that declares state or performs IO is run; every other module is imported.** Importing
  asserts that a module declares no mutable variable or feed and opens no source
  ([9.7 Importing asserts no IO and no state](../docs/chl-spec.md#97-importing-asserts-no-io-and-no-state)).
  A concept that needs both, such as time and waiting for a time, is two modules: the stateless
  half imported, the stateful half run.
- **A submodule refines its parent's concept.** `std::time::timer` is in `time/` because it waits
  for a `time::Instant`. Importing `std::time` does not bring `std::time::timer` into scope.
- **One concept per module, named by a noun:** `time`, `timer`, `http`. A module's members read
  qualified, `time::now()`, so a member does not repeat the module's name: `timer::register`, not
  `timer::register_timer`, as in Go.
- **Names follow the language.** Types are capitalized nouns (`Instant`, `Firing`), and functions,
  sources and parameters are lowercase with underscores (`now`, `fired`). A module's type parameter
  is capitalized (`param Key`).
- **A function's name says what it acts on.** `timer::cancel(key)` cancels one timer; a name such
  as `clear`, which in Rust's `HashMap` and Python's `dict` empties the whole collection, would not
  say so.

### Adding a module

1. Choose its path by the rules above, and check that the name is free in
   [the type sketch](../docs/chl-spec.md#6-types-informal-sketch) and the prelude, as `Instant` is
   and `Time` is not.
2. Write the file with the documentation below.
3. Add its row to the layout table.
4. Import or run it from a program under `tests/`, and bless that program's errors ([Tests](#tests)).

## Documentation

CHL has `#` comments and no doc-comment syntax, so placement marks documentation, as in Go: the
comment block directly above a `pub` declaration documents it, and the file's first comment block
documents the module. A private declaration takes a comment only when its reason is not obvious
from its name and type.

### The module comment

The first block of a file says, in order:

1. One sentence naming what the module provides, as its summary.
2. How a program reaches it, `import` or `run`, and why.
3. The rules that hold across the module, such as what `Instant` means and what is out of scope.
4. An `Example:`, a whole program fragment that uses the module the way a program would.
5. A `Status:` line: `proposed, not in the spec` until the spec describes the module, then the
   spec's status marker for it, and what `[proposed]` marks in the file.

### Item comments

- **The first sentence is a summary**: one sentence, in the third person, stating what the item is
  or does, as in Rust's standard library. "Returns the current instant", not "This function will
  return the current instant". A type's summary is a noun phrase: "A point on the UTC timeline."
  Go begins the sentence with the item's name and PEP 257 uses the imperative; in CHL the
  declaration on the next line names the item, so the summary does not repeat it.
- **Then the contract**, one paragraph or bullet per rule: what the item guarantees, under which
  conditions, and what it does at the edges (an instant already passed, a key never registered).
  Each rule states a bound rather than a tendency: "at or after its instant", not "around its
  instant".
- **Name every requirement the signature does not show**: that a call needs a transaction, that a
  source delivers each element once, that an order is undefined.
- **An `Example:` section where usage is not obvious from the signature**, as Rust's `# Examples`.
  The example is a fragment of a real program, indented four spaces, using qualified names as a
  caller writes them.
- **`[proposed]` on the item's last comment line** lists each construct the item uses that the
  compiler lacks, with the spec section that comes closest.

### Prose

Documentation is specification: the summary first, the present tense, no history of the code, and
no hedges. The repo's
[prose rules](../CLAUDE.md#prose-style-specifications-not-blog-posts) apply in full.

- **Cite the spec by heading**: the path, then the heading's exact text in double quotes,
  `docs/chl-spec.md, "9.7 Importing asserts no IO and no state"`, never a section number alone.
  `./ci.sh doc_refs` checks it in full-line comments; a citation in a comment trailing code is not
  read.
- **Use the spec's names.** A std concept the spec already names takes that name. A name the spec
  uses for another concept is not reused: the builtin `Time` is a position in the commit order, so
  a wall-clock reading is `time::Instant`.
- **Wrap comments at 100 columns**, as this repo wraps Markdown.

## Tests

`tests/` holds programs that import or run the std modules as a user program does. It is not a std
module. `tests/it/std_root.rs` compiles each program against the sources here in place of the
compiler's std root, which is empty, and compares the rendered errors with the golden `.errors`
file beside the program. A program that compiles has no golden. `CAMBRA_BLESS=1 cargo test
std_root` rewrites the goldens. A construct that lands removes its errors from a golden, and a
module that no program loads fails the test.

Every error in a golden is a construct a `[proposed]` line names. An error no `[proposed]` line
accounts for is a bug in the module or in the program.

## Stability

No module here is stable: until the spec describes a module, any change to it may break the
programs that use it. Once the compiler embeds the std root, a std module's run is a run like any
other, so a std change that alters a stateful module's state reloads under the same rules as user
code ([9.18 Reloading a program of modules](../docs/chl-spec.md#918-reloading-a-program-of-modules)):
a change to `std::time::timer`'s `instants` needs a compatible type or a conversion, as a user
module's variable does. A std module records its compatibility promises in its module comment.

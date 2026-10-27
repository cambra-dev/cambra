# The CHL standard library

`src/` is the std root ([9.16 The std root](../docs/chl-spec.md#916-the-std-root)): the CHL source
of the modules every program can reach under the `std` path. The std root is [Planned]: no module
here compiles, and the compiler does not embed them. A module's `Status:` line gives the spec's
status for it. `[proposed]` marks each construct a file uses that the compiler lacks, and the
programs under `tests/` check that every module parses and loads ([Tests](#tests)).

## Layout

A module's path is its file's path under `src/`, as a user module's is under the module root
([9.15 Module files](../docs/chl-spec.md#915-module-files)): `src/std/time.cambra` is `std::time`.
`std` alone names no module, so `src/` holds no `std.cambra`. `tests/` holds the programs that
load the modules ([Tests](#tests)).


| Module | File | Used by | Holds |
| -- | -- | -- | -- |
| `std::time` | [src/std/time.cambra](src/std/time.cambra) | `import std::time` | `Instant`, `Duration`, `now()`, `alarms`, durations, and conversions to integer counts and Unix time |
| `std::env` | [src/std/env.cambra](src/std/env.cambra) | `import std::env` | `var`, the environment variables a program names, read by the host |

- **A module that declares state or performs IO is run; every other module is imported.** Importing
  asserts that a module declares no mutable variable or feed and opens no source
  ([9.7 Importing asserts no IO and no state](../docs/chl-spec.md#97-importing-asserts-no-io-and-no-state)).
  A function that performs IO when called, such as `time::now()` or `time::alarms()`, leaves its
  module importable: the IO belongs to the module whose evaluation calls it.
- **One concept per module, named by a noun:** `time`, `http`. A module's members read qualified,
  `time::now()`, so a member does not repeat the module's name: `time::alarms`, not
  `time::time_alarms`.
- **Names follow the language.** Types are capitalized nouns (`Instant`, `Duration`), and
  functions, sources and parameters are lowercase with underscores (`now`, `as_seconds`). A type
  parameter is capitalized (`R` in `alarms`).
- **A function's name says what it acts on.** `time::as_seconds(d)` converts a `Duration` and
  `time::unix_seconds(t)` an `Instant`.

### Adding a module

1. Choose its path by the rules above, and check that the name is free in
   [the type sketch](../docs/chl-spec.md#6-types-informal-sketch), as `Instant` is and `Time` is
   not.
2. Write the file with the documentation below.
3. Add its row to the layout table.
4. Import or run it from a program under `tests/` ([Tests](#tests)).

## Documentation

CHL has `#` comments and no doc-comment syntax, so placement marks documentation: the
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
  or does. "Returns the current instant", not "This function will return the current instant". A
  type's summary is a noun phrase: "A point on the UTC timeline." The declaration on the next line
  names the item, so the summary does not repeat it.
- **Then the contract**, one paragraph or bullet per rule: what the item guarantees, under which
  conditions, and what it does at the edges (an instant already passed, two rows with equal `at`).
  Each rule states a bound rather than a tendency: "at or after its instant", not "around its
  instant".
- **Name every requirement the signature does not show**: that a call needs a transaction, that a
  source delivers each element once, that an order is undefined.
- **An `Example:` section where usage is not obvious from the signature.** The example is a fragment of a real program, indented four spaces, using qualified names as a
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

`tests/` holds programs that import or run the std modules as a user program does.
`tests/it/std_root.rs` loads each program against the sources under `src/` in place of the
compiler's std root, which is empty. Each program, and every std module it reaches, must parse and
resolve its module paths. A module that no program loads fails the test.

The programs are not compiled until a std module compiles. The `[proposed]` lines are the record of
what each module waits on.

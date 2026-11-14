# The CHL standard library

`src/` is the std root ([9.16 The std root](../docs/chl-spec.md#916-the-std-root)): the CHL source
of the modules every program can reach under the `std` path. The compiler embeds each module that
compiles (`STD_MODULES` in `src/ccl/load/mod.rs`), and a path naming another one names no module.
A module's `Status:` line gives the spec's status for it. `[proposed]` marks each construct a file
uses that the compiler lacks, and the programs under `tests/` check that every module parses and
loads ([Tests](#tests)).

`prelude.cambra` is the prelude: the `import` statements whose `use` items every module outside
the std root names without an import. It is no module, so it stands outside `src/`.

## Layout

A module's path is its file's path under `src/`, as a user module's is under the module root
([9.15 Module files](../docs/chl-spec.md#915-module-files)): `src/std/time.cambra` is `std::time`,
and `src/std.cambra` is `std`, the core module. `tests/` holds the programs that load the modules
([Tests](#tests)).


| Module | File | Used by | Holds |
| -- | -- | -- | -- |
| `std` | [src/std.cambra](src/std.cambra) | the prelude | `Option`, and the traits operators, loops and aggregates require, with their `@Builtin` instances for base types |
| `std::random` | [src/std/random.cambra](src/std/random.cambra) | `import std::random` | `next()`, a random `Int` read once per position |
| `std::time` | [src/std/time.cambra](src/std/time.cambra) | `import std::time` | `Instant`, `Duration`, `now()`, `alarms`, durations, and conversions to integer counts and Unix time |

- **A module whose top level requires or causes something is run; every other module is imported.**
  Importing asserts that a module is shareable: its top level reads nothing from outside the program
  and leaves behind no output and no state another module could reach
  ([9.7 Importing asserts a shareable module](../docs/chl-spec.md#97-importing-asserts-a-shareable-module)).
  A function that performs IO when called, such as `time::now()` or `time::alarms()`, leaves its
  module importable: the IO belongs to the module whose top level calls it.
- **The core module holds what every program names:** the types, traits and functions the
  language's own constructs answer or require, such as `Option` and `Addable`. The prelude imports
  them, so they read bare.
- **`@Builtin` marks what the compiler implements.** The declaration states the member's type,
  and the compiler supplies what CHL cannot state: a trait's answers beyond its instances, and an
  instance's primitives ([9.16 The std root](../docs/chl-spec.md#916-the-std-root)). Only `std`
  declares one.
- **Every other module holds one concept, named by a noun:** `time`, `http`. A module's members
  read qualified, `time::now()`, so a member does not repeat the module's name: `time::alarms`, not
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
5. Once it compiles, add it to `STD_MODULES`. A module the prelude imports compiles, and a std
   module reaches no prelude, so it imports each std module whose members it names.

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
  `docs/chl-spec.md, "9.7 Importing asserts a shareable module"`, never a section number alone.
  `./ci.sh doc_refs` checks it in full-line comments; a citation in a comment trailing code is not
  read.
- **Use the spec's names.** A std concept the spec already names takes that name. A name the spec
  uses for another concept is not reused: the builtin `Time` is a position in the commit order, so
  a wall-clock reading is `time::Instant`.
- **Wrap comments at 100 columns**, as this repo wraps Markdown.

## Tests

`tests/` holds programs that import or run the std modules as a user program does.
`tests/it/std_root.rs` loads each program against every source under `src/` in place of the
compiler's std root, which holds only the modules that compile, with the compiler's prelude. Each
program, and every std module it reaches, must parse and resolve its module paths. A module that no
program loads fails the test.

The programs are not compiled, since each reaches a module that does not compile. The `[proposed]`
lines are the record of what each module waits on. The compiler's own tests compile the embedded
modules through the prelude, `Option`'s in `tests/it/compilation_pipeline/nominal_types.rs`.

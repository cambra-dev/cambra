# cambra-lsp design

`cambra-lsp` is a language server for CHL. An editor starts it as `cambra --lsp` and talks to it
over standard input and output using the Language Server Protocol (LSP) 3.17. The first version
reports lex and parse errors as you type, lists a file's functions and top-level bindings, and
folds blocks, brackets and comment runs. It works on one file at a time and serves any client,
counting columns in UTF-8 or UTF-16 ([Positions](#positions)).

## Scope

The first version has three features:

- **Diagnostics** for the lex and parse errors `parse_module` reports.
- **Document symbols**, the outline of a file.
- **Folding ranges.**

Each of them needs only the parser. Each is computed from the text the editor holds, saved or
not, and none reads other files from disk.

Not in the first version, in the order planned:

- Diagnostics from the rest of the compiler: lowering, type inference and later phases. This
  needs the `cambra` library ([Package layout](#package-layout)) and a worker thread
  ([its design](#later-compiler-diagnostics-on-a-worker-thread)).
- Semantic tokens, hover types, go-to-definition and completion.

## Package layout

`cambra-lsp` is a workspace package that depends on `chl-parser`, on `lsp-server` 0.10 for the
transport, and on `gen-lsp-types` 0.11 with its `url` feature for the protocol types.
`gen-lsp-types` is generated from the protocol's published model. Rust-analyzer, Ruff and Gleam
use it in place of `lsp-types`, which has had no release since 0.97 in 2024.

`src/main.rs` handles `--lsp` by calling `cambra_lsp::run_stdio()`, which returns when the editor
shuts the server down.

Compiler diagnostics need `cambra-lsp` to depend on the `cambra` library. Since the `cambra`
binary depends on `cambra-lsp`, and the library and binary share one package, that is a cycle
Cargo rejects. When compiler diagnostics arrive, the binary moves to a package of its own that
depends on both, as Ruff (`crates/ruff` over `ruff_server`) and Gleam (`compiler-cli` over
`language-server`) are arranged. The first version needs no compiler, so it has no cycle.

## Lifecycle

The server runs on one thread and handles messages in batches, in the order they arrive.

- **Start.** The server reads `initialize`, picks a position encoding from the client's
  capabilities ([Positions](#positions)), and answers with its capabilities and `serverInfo`. It
  uses `lsp-server`'s `initialize_start` and `initialize_finish`, which reject anything sent
  before `initialize` or between it and `initialized`.
- **Batches.** The loop waits for one message, then takes every message already waiting behind
  it, and handles them in order as one batch:
  - Edits are applied to the document text without reparsing.
  - Before it answers a request, the server reparses each document changed since its last parse.
  - After the batch, it reparses each changed document and publishes its diagnostics once.

  Work for an intermediate version of a document is skipped, and nothing waits on a timer, so an
  idle server answers at once. The edits themselves are never skipped: each describes a change to
  the text before it.
- **Cancellation.** A request whose `$/cancelRequest` is in the same batch is answered with the
  `RequestCanceled` error and not computed; the protocol requires a response to every request.
  A cancellation for a request already answered is ignored.
- **Edits after a request.** A request is answered from the text as of its place in the batch:
  the edits before it apply, and the edits after it do not. A position in a request refers to
  that text. The protocol reserves `ContentModified` for a change found while a request runs, not
  for one waiting in the queue, so the server does not send it.
- **Malformed messages.** A notification whose parameters do not parse is logged with
  `window/logMessage`. A request whose parameters do not parse gets `InvalidParams`, and a request
  the server does not handle gets `MethodNotFound`. Neither ends the session.
- **Stop.** `shutdown` is answered, after which every request gets `InvalidRequest` and every
  notification but `exit` is ignored. `exit` ends the session. The process exits with status 0 if
  `shutdown` came first, and 1 otherwise, as the protocol specifies. `lsp-server`'s
  `handle_shutdown` is not used: it reads `exit` from the connection, and in a batch `exit` may
  already have been read.

Parsing runs on the loop's thread. A release build parses `tests/programs/storefront/v1.cambra`
(133 lines) in 0.5 ms and that file repeated 500 times (66,500 lines) in 19 ms. Neovim already
holds edits for 150 ms before sending them (`flags.debounce_text_changes`), so the server adds no
delay of its own.

### Later: compiler diagnostics on a worker thread

The first version reports no compiler diagnostics ([Scope](#scope)). This is their design.

Compiling is slow and cannot be interrupted once started. Compiler diagnostics therefore run on
one long-lived worker thread, so the loop keeps answering parser features while a compile runs:

- At most one compile runs at a time. When it finishes and the document has changed, the worker
  compiles the latest text, skipping every version in between.
- A compile starts only after the document has gone a short pause without edits, so a compile
  started mid-burst does not delay the one for the text the user stops at. Gleam's server pauses
  for 100 ms; the length is set from compile times measured on real programs.
- A result for a version that is no longer current is dropped. Parse diagnostics stay current
  while the user types, and compiler diagnostics follow at the next pause.
- Each compile runs under `catch_unwind`, so a compiler panic becomes a diagnostic. All compiles
  run on the same thread because `run_frontend` installs per-thread sessions.

With the worker, the loop waits on two channels: messages from the client, and results from the
worker. A compiler that checked for a newer edit between phases could stop a stale compile, as
rust-analyzer cancels its work, and would make the pause unnecessary.

## Documents

The server keeps each open document as its full text:

```rust
struct Document {
    text: String,
    version: i32,
    index: LineIndex,
    encoding: Encoding,
    parsed: OnceCell<ParseResult<Module>>,
}
```

The parse is made the first time a request or a publish needs it, and discarded when the text
changes. The documents live in a map keyed by the URI the editor sent, with no normalization.

- **Open** stores the text. Opening a URI that is already open replaces it, and is logged.
- **Change** carries a list of edits, each a range and its replacement text. The server applies
  them in order to `text`, rebuilding `index` after each. A change for a URI that is not open is
  logged and ignored.
- **Close** drops the document and clears its diagnostics.

An edit's positions clamp into the text as [Positions](#positions) describes, so every position
names an offset. An edit whose range starts after it ends is logged with `window/logMessage` and
skipped; the server never panics on an edit. Skipping leaves the server's text different from the
editor's until the file is reopened, so a skipped edit is a client bug to report. Ruff's server
panicked on a reversed range and on a column inside a multi-byte character (Ruff issue #26768),
and on mixed line breaks (#16342); a fuzz test covers these ([Testing](#testing)).

The edits arrive as ranges rather than whole files. The server still lexes and parses the whole
new text each time, as Ruff and rust-analyzer do: both keep the full text, apply each edit to it,
and reparse the file.

## Positions

The compiler measures everything in bytes: a `Span` holds byte offsets into the file's UTF-8
text. LSP positions are a line number and a column instead. The client and server agree on what
a column counts during `initialize`:

- UTF-8 bytes. A column is the byte offset from the start of the line.
- UTF-16 code units: one per character up to U+FFFF, two (a surrogate pair) for a character above
  it. The protocol requires every server to support UTF-16, and a client that names no encoding
  means it. It is the only encoding VS Code's client, `vscode-languageclient`, offers or accepts.
- UTF-32 code units, one per character. The server does not support it. A client that offers
  only UTF-32 gets UTF-16, which the protocol requires every client to support.

The server chooses UTF-8 when the client offers it, since spans need no conversion then, and
UTF-16 otherwise, so it serves every client. Neovim 0.11 offers UTF-8; Neovim 0.10 and VS Code
get UTF-16. The choice holds for the session, and `Document` converts every position the server
reads or writes in it. Folding needs only line numbers, which do not depend on the encoding.

`LineIndex` converts between offsets and positions. It lives in `chl-parser`, so the editor
highlight dump (`chl-parser/examples/dump_tokens.rs`) and the recovery tests use it in place of
their own `line_col` helpers; their columns stay in bytes. It records where each line starts and
whether the text is all ASCII, in which case a UTF-16 column is the byte column. Otherwise it
counts the UTF-16 units of the line up to the offset on each conversion. It follows the
protocol's rules exactly:

- A line ends at `\n`, at `\r\n`, or at a `\r` not followed by `\n`. The lexer rejects `\r`
  today, but the index must still count lines the way the editor does.
- A line past the last one means the end of the document.
- A column past the end of its line means the end of the line, before the line break.
- A column in the middle of a character means the start of that character: a byte column inside
  a multi-byte character, or a UTF-16 column between the two halves of a surrogate pair.

## Diagnostics

After every open and every change, the server sends `textDocument/publishDiagnostics` with all
of the document's errors. Each message replaces the previous set, so a fixed error disappears
when the next set omits it, and the server sends an empty set rather than nothing once the file
has no errors. Closing a document sends an empty set.

Each `ParseError` from `parse_module` becomes one diagnostic with severity Error and source
`cambra`:

- The range is the error's span.
- The message is the error's text without any location. A grammar error's text today ends with
  where it occurred as byte ranges, such as `(in statement at 0..7)`. The server moves each of
  those into related information instead.
- Related information is a list of other places the error concerns, each with a short message,
  which an editor shows as links under the error:
  - A `MismatchedClose` links to the open bracket, "this bracket is never closed"
    (`LexError::related`).
  - A grammar error links to each place in its context, such as "while parsing statement" at
    the statement that failed to parse (`ParseErrorInfo.context`).

The inspector's `Diagnostic` keeps only the main span and message, so neither link reaches it
today.

## Document symbols

`textDocument/documentSymbol` returns the file's outline as a tree. Each entry has a name, a
kind, the range of the whole item, and the range of its name, which the editor highlights when
the entry is chosen.

The outline lists:

| Statement | Entry |
|---|---|
| `def f(...)` | `f`, a Function; its children are the `def`s directly in its body |
| `x = ...`, `x: T = ...`, `x <: T = ...`, `x := ...`, `@LoadFrom(y)` then `x: T` | `x`, a Variable; a tuple target lists each name it binds |
| `param x: T = ...` | `x`, a Variable |
| `import m`, `run m` | the alias if one is given, otherwise the module path, a Module |
| `pub` before any of these | the entry for the statement it marks |

Only the file's top-level statements and the `def`s nested in other `def`s appear. Bindings
inside a function body, a loop or a branch are left out: a name rebound in a loop would appear
once per binding, and merging those needs name resolution, which the parser does not do. A name
bound twice at the top level appears twice. `x <<= ...` defines an output declared elsewhere, so
it adds no entry, and neither do the names an `import` or `run` brings in with `use`, a key write
(`m[k] := v`), or a write to another module's variable (`c::count := v`).

An entry's range is the statement's span without its trailing whitespace; a block statement's
span runs past the line break after its body. A function's name range is the span of the name
after `def`.

When `parse_module` returns no module, which happens after an error the parser does not recover
from, the outline is empty.

## Folding ranges

`textDocument/foldingRange` returns line ranges the editor can collapse. Neovim and VS Code fold
whole lines only, and keep the first line of a range visible.

- **Blocks.** Every statement body folds: a `def`, each `if`, `elif` and `else` branch, a `for`,
  each `case` of a `match`, a `with`, and the block on the right of an assignment. A range starts
  at the line holding the token just before the body, which is the header's `:`, so a header
  wrapped over several lines stays visible. It ends at the last line of the body's last
  statement that holds more than whitespace. A body on the same line as its header does not
  fold.
- **Matches.** A `match` also folds as a whole, from the line its header ends on to its last
  arm's last line. Its arms carry no spans, so the header's end is the first line break in the
  token stream after the statement starts.
- **Brackets.** A bracketed region that spans lines folds from its open bracket's line. When the
  close bracket is the first token on its line, the range ends on the line before, so the close
  bracket stays visible.
- **Comments.** Two or more consecutive lines that hold only a comment fold as one range of kind
  `comment`.

Block ranges come from the parsed module, so a file `parse_module` returns no module for folds
only its brackets and comments. Bracket ranges come from the token stream, whose brackets always
balance ([lexer recovery](../chl-parser/design-chl-parser.md#lexer-recovery)). Comment ranges come
from the text, because the lexer drops comments.

## Neovim client

`editors/nvim/lsp/cambra.lua` configures the server for Neovim 0.11's `vim.lsp.config`: the
command `cambra --lsp` and the `cambra` filetype. `vim.lsp.enable('cambra')` starts it. Folding
through the server uses `vim.lsp.foldexpr()`. `editors/README.md` describes the setup.

## VS Code client

`editors/vscode/extension.js` starts the server with `vscode-languageclient`, VS Code's LSP
client library, which offers only UTF-16 positions and fails to start against a server that
answers with any other encoding. The client runs `<cambra.server.path> --lsp` over standard input
and output for `cambra` documents with the scheme `file` or `untitled`; a selector by language
alone would also attach to the `git:` documents of diff views. Changing `cambra.server.path`, or
the command **Cambra: Restart Language Server**, stops the server and starts a new one. Restarts
run one at a time, a restart queued behind a later one is skipped, and edits to the setting take
effect 500 ms after the last one. A binary that does not start is reported with an error naming the
setting. In an untrusted workspace (Restricted Mode) the extension stays enabled, VS Code ignores
the workspace's `cambra.server.path` (`capabilities.untrustedWorkspaces` in `package.json`), and the
server runs from the user's home directory, so on Windows a bare `cambra` cannot resolve to a binary
in the workspace folder. Trusting the workspace restarts the server. `editors/README.md` describes
the setup.

## Testing

- **Batches.** Unit tests in `cambra-lsp/src/server.rs` hand one batch to the loop's batch
  handler and read what it sent: one publish per changed document, a request answered from the
  text before it, a cancelled request answered `RequestCanceled`, a close clearing diagnostics.
  Whether two messages share a batch depends on thread timing, so these tests do not go through
  a connection.
- **The protocol.** `cambra-lsp/tests/server.rs` runs the server on a thread behind
  `lsp-server`'s in-memory `Connection::memory()`. Its `TestServer` performs the handshake,
  sends requests and notifications, and waits for the diagnostics of a given version. Ending a
  session joins the server thread and fails the test on any unread message other than a
  superseded diagnostics publish. It covers the handshake and the encoding each client is given,
  shutdown and exit, an unhandled request, incremental edits, related information, and columns
  counted in UTF-16.
- **Goldens.** `cambra-lsp/tests/goldens/programs.txt` holds the diagnostics, outline and folds
  of every `.cambra` file under `tests/` and `editors/`, and `lexer_recovery.txt` those of the
  lexer recovery corpus, so files with errors are covered. `non_ascii.txt` holds those of the
  fixtures in `cambra-lsp/tests/non_ascii/` under both encodings, since the repository's programs
  hold multi-byte characters only in comments. Each diagnostic's range and each symbol's range end
  there falls after a multi-byte character, so its two columns differ. `CAMBRA_BLESS=1` rewrites
  them, as it does the repository's other goldens.
- **Encoding independence.** `features_do_not_depend_on_the_encoding` runs every file above under
  a UTF-8 and a UTF-16 session, requires each position to be canonical, maps it back to a byte
  offset, and requires the two to agree, so a feature that computed a column without the session's
  encoding fails.
- **Clients.** `./ci.sh editors` runs the server through Neovim's client
  (`editors/nvim/test/check_lsp.lua`), and `./ci.sh vscode`, in CI but outside the local full
  gate, through VS Code's (`editors/vscode/test/lsp/`). Both check the handshake, diagnostics at
  the client's columns, the outline, folds and edits on one file with a multi-byte character
  (`editors/README.md`, "Language server checks").
- **Positions.** A seeded fuzz test in `cambra-lsp/src/document.rs` (`CAMBRA_FUZZ_SEED`,
  `CAMBRA_FUZZ_N`) builds texts mixing ASCII, multi-byte characters and all three line breaks,
  and alternates the encoding between cases. It applies random edits, reversed and out-of-range
  ones included, and checks that the line index follows the text, that every character boundary
  survives a trip through a position, that each column equals the UTF-8 or UTF-16 length of its
  line up to the offset, and that every column on a line names a character boundary at or before
  it.

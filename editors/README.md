# Editor support

VS Code and Neovim support syntax highlighting, indentation, and the language server for CHL
(`.cambra`). Both use language id `cambra`; the TextMate grammar uses scope `source.cambra`.

The program inspector's source pane is a third editor. It runs the VS Code grammar in the page
([Inspector](#inspector)), and the editor highlight check checks it beside the other two.

| Directory | Contents |
| --- | --- |
| `vscode/` | A VS Code extension: the language, its comment and bracket configuration, the TextMate grammar `syntaxes/cambra.tmLanguage.json`, and the language server client `extension.js`. |
| `nvim/` | A Neovim runtime directory: filetype detection, a filetype plugin, an indent plugin, the syntax file `syntax/cambra.vim`, and the language server configuration `lsp/cambra.lua`. |

The language server runs as `cambra --lsp` and provides lex/parse diagnostics, document symbols,
and folding ranges. It supports UTF-8 and UTF-16 positions. Its protocol and scope are specified in
[the language server design](../cambra-lsp/design-cambra-lsp.md). Highlighting uses regex grammars,
not semantic tokens.

## VS Code

Build and install the server from the repository root with `cargo install --path .`. The extension
uses `cambra` on `PATH`, or the binary named by `cambra.server.path`. Install the extension's npm
dependencies, link it, and reload VS Code:

```bash
(cd editors/vscode && npm ci)
ln -s "$PWD/editors/vscode" ~/.vscode/extensions/cambra-dev.cambra-0.1.0
```

Alternatively, package and install it with Node and the `code` command available:

```bash
cd editors/vscode
npx @vscode/vsce package --skip-license
code --install-extension cambra-0.1.0.vsix
```

`--skip-license` accounts for the license file being at the repository root, outside the extension.
Open a `.cambra` file and check that the status bar shows Cambra. **Developer: Inspect Editor Tokens
and Scopes** shows the scope under the cursor.

### Language server in VS Code

Opening a `.cambra` document starts the server for disk-backed and untitled documents. Diagnostics
appear in the editor and Problems panel; a mismatched bracket links to its opening bracket.
Document symbols populate Outline, breadcrumbs, and **Go to Symbol in Editor**. Server-provided
folding ranges replace indentation-based folding.

| Setting or command | Effect |
| --- | --- |
| `cambra.server.path` | Server binary; defaults to `cambra` on `PATH`. A change restarts the server. |
| `cambra.trace.server` | `messages` or `verbose` logs protocol traffic to the **Cambra** output channel; default `off`. |
| **Cambra: Restart Language Server** | Restarts the server after a binary rebuild. |

The **Cambra** output channel also receives server logs. Startup errors name `cambra.server.path`.
Restricted Mode permits highlighting and the server, but ignores workspace values of that setting.
The user setting or `PATH` selects the binary, and it runs from the user's home directory rather
than the untrusted workspace. Trusting the workspace restarts the server with workspace settings.

### VS Code indentation limits

Typing `elif` or `else` followed by `:` dedents one level. Enter follows the shared
[indentation rules](#indentation) with these exceptions:

- A multiline bracketed header indents its body from the header's last line, not its first.
  After `def f(a,` / `      b):`, the body starts at column 8.
- A line after a multiline bracketed expression keeps the last line's indentation.
- A `return` or `pass` leaving a bracket open outdents the continuation unless the line ends in
  the opening bracket. After `    return f(a,`, the next line starts at column 0. Neovim retains
  the `return` line's indentation because it checks bracket balance first.

**Reindent Lines** uses only `indentationRules`, so an assignment's `if` body receives one level
rather than the two supplied by Enter. Enter adds one editor indentation level plus the four spaces
in the rule's `appendText`.

## Neovim

Add the runtime directory to `init.lua`:

```lua
vim.opt.runtimepath:append("/path/to/cambra/editors/nvim")
```

The filetype plugin sets `commentstring` to `# %s` and uses four-space indentation. The indent
plugin follows [Indentation](#indentation), measuring a bracketed multiline header from its first
line. It runs on Enter, `o`, `O`, and explicit reindent requests. Typing `elif` or `else` does not
dedent the line; dedent it manually.

In a `.cambra` buffer, `:set filetype?` should report `filetype=cambra`, and `:Inspect` shows the
syntax group. A headless check from the repository root is:

```bash
nvim --headless -u NONE --cmd 'set rtp^=editors/nvim' \
  -c 'filetype plugin indent on' -c 'syntax on' \
  -c 'e tests/programs/arithmetic/program.cambra' -c 'echo &ft b:current_syntax' -c 'qa!'
```

### Language server

The configuration in `lsp/cambra.lua` requires Neovim 0.11's `vim.lsp.config`. Install the server
with `cargo install --path .` from the repository root and put `cambra` on `PATH`. With the runtime
directory configured, add this to `init.lua` to enable the server and its folding ranges:

```lua
vim.lsp.enable('cambra')
vim.api.nvim_create_autocmd('FileType', {
  pattern = 'cambra',
  callback = function()
    vim.wo.foldmethod = 'expr'
    vim.wo.foldexpr = 'v:lua.vim.lsp.foldexpr()'
  end,
})
```

`:checkhealth vim.lsp` reports server attachment. Errors appear as diagnostics;
`vim.lsp.buf.document_symbol()` lists the outline, and `zc` / `zo` close and open folds.

## Highlight classes

Both grammars classify the same constructs. `highlight-classes.json` lists each class with the
construct it covers, its TextMate scope prefix, and its Vim group; `null` means the construct is not
highlighted. The lexer assigns the classes: `highlight_class` and `highlight` in
`chl-parser/src/lexer.rs`.

The keyword lists match `KEYWORDS` in `chl-parser/src/lexer.rs`. The test
`tests/it/editor_grammars.rs` reads the `keyword-control`, `keyword-other` and `constant-boolean`
rules from the TextMate grammar and the `syn keyword` lines from the Vim syntax file, and fails when
either differs from the lexer. Keep each keyword class on one rule so the test can read it.

A string literal ends on the line it starts on
([1.7 Literals](../docs/chl-spec.md#17-literals)), so both grammars end a string at the end of its
line as well as at its closing quote. An unterminated string, which the lexer reports as an error,
colors the rest of its line and nothing after it. The editor highlight check below cannot exercise
that rule, because its corpus lexes with no error (`every_repository_program_lexes_with_no_error`
in `chl-parser/tests/lexer_recovery.rs`).

A `TODO`, `FIXME` or `XXX` in a comment is a word when no ASCII letter, digit or `_` touches it, the
characters that continue an identifier. Both grammars spell this boundary out instead of using `\b`
or `syn keyword`, whose word definitions include non-ASCII letters, and in Vim emoji. A combining
mark after the word is drawn with its last letter, so Vim colors the mark as part of the todo, while
the lexer and TextMate class it as comment.

An integer directly followed by a letter, as in `1if c else 2`, lexes as two tokens, and neither
grammar colors either of them: the `\b` in the TextMate rules and Vim's word boundary both need a
non-word character between the two.

### Builtins

The builtin class covers every spelling in `SURFACE_BUILTINS` in `chl-parser/src/builtins.rs`,
including functions, `begin`, sink declarations, `stdin`, and `summon`. A row's kind determines
where the name is accepted, not whether it receives builtin highlighting.
`tests/it/editor_grammars.rs` reads the TextMate `builtin` rule and the Vim
`syn match cambraBuiltin` line, and fails when either differs from the table.

Highlighting is by spelling. A user binding that shadows a builtin, such as a parameter named
`max`, and a field or keyword argument spelled like one, such as `r.max`, are colored as the
builtin. The name after `def`, a variant tag and a decorator keep their own classes.

The Vim group links to `Function`, as `python.vim` links Python's builtins. It is the group the name
after `def` links to, so the two share a color in Vim, and the Vim half of the editor highlight
check cannot tell a builtin from a function name; the TextMate half can.

### Type annotations

Capitalized names are types wherever they appear, so an annotation's named types are colored in
every position. The one other spelling a type can have is the hole `_`, and it is colored as a type
only directly after `:`, `<:`, `=>` or `{`. Elsewhere `_` is a pattern binder (`` `some(_) ``) or a
refinement's subject (`{Int where _ > 0}`), and a regex cannot tell the hole in `List(_)` or
`{Int, _}` from the binder in `` `some(_) `` without parsing the enclosing construct. A `=>` whose
`=` directly follows an operator character, as in `a ==> _` or `b <=> _`, is that operator and `>`,
so the `_` after it is not a type. Two spellings disagree with the lexer:

- A one-line `match` arm in a refinement whose body is the subject, as in `` case `some(x): _ ``,
  colors the subject as a type.
- `a ===> _` lexes as `==` and `=>`, so its `_` is a type, and neither grammar colors it.

The rest of an annotation keeps the class it has outside one. The `:`, `<:` and `=>` that introduce
a type are punctuation and operators. Brackets are not colored anywhere, including the `(…)` of a
type application and the `{…}` of a type literal. A record type's field names are identifiers, as a
record value's are. A refinement's predicate after `where` is a term, and is highlighted as one.

## Indentation

Both editors indent a new line from the line above it:

- After a line ending in `:`, ignoring a trailing comment, one level in.
- After a line ending in an open bracket (`(`, `[` or `{`), ignoring a trailing comment, one level
  in.
- After a header whose `if` is the right-hand side of an assignment (`label = if c:`), two levels
  in. The `elif` and `else` chain sits one level in from the statement and the bodies one level
  further ([4.3 Assignment forms](../docs/chl-spec.md#43-assignment-forms)); a body one level in
  leaves no column for the chain. A `match` on the right needs one level, since its `case` arms are
  the chain.
- After a `return` or `pass` line, one level out.
- Inside an unclosed bracket, at the previous line's level.
- Otherwise, at the same level.

A bracketed expression that spans several lines counts as the line it starts on, and a `:`,
bracket or `#` inside a string or comment counts for nothing. VS Code falls short of these rules
in the cases listed under [VS Code indentation limits](#vs-code-indentation-limits).
`indent-cases.json` holds a case for each rule
([Indentation tests](#indentation-tests)).

## Running the checks

Run these commands from the repository root. The `editors` shell gate requires Bash 4 or later
for `mapfile`; macOS's bundled Bash 3 cannot run it. Put a suitable Bash on `PATH` before invoking
`./ci.sh editors`.

| Command | Coverage | Requirements |
| --- | --- | --- |
| `cargo test editor_grammars` | Keyword/builtin lists, class coverage, sample parsing, and indentation-case parsing | Rust toolchain |
| `./ci.sh editors` | TextMate, Vim and inspector highlighting, both indentation checkers, Neovim language client | Rust toolchain, Node/npm, and Neovim 0.11 |
| `./ci.sh vscode` | VS Code extension and language client | Rust toolchain and Node/npm; downloads VS Code unless `CAMBRA_VSCODE` names an installed executable |

`./ci.sh editors` skips unavailable editor dependencies locally with a diagnostic; missing
dependencies fail under CI. It installs npm packages from `vscode/package-lock.json` when
`vscode/node_modules` is absent, and the inspector's into `web/node_modules`. `./ci.sh vscode` runs `npm ci` on each invocation.

The local full gate includes `editors`, but not `vscode`; `fast` includes neither. GitHub's
`editors` job runs both. The VS Code download occupies about 1 GB unpacked in
`vscode/.vscode-test/`.
`ci_vscode` pins the version; `CAMBRA_VSCODE_VERSION` overrides it. The test uses a fresh profile
with only this extension. Linux uses Chromium's headless Ozone platform unless
`CAMBRA_VSCODE_SHOW=1` requests a window.

## Editor highlight check

`./ci.sh editors` compares every `.cambra` file under `tests/`, `editors/`, and `stdlib/` against
`chl-parser/examples/dump_tokens.rs`. That example emits lexer highlight spans as JSON lines,
splitting strings into string/escape spans and comments into comment/todo spans. Newline tokens
have no span. Input lex errors fail the dump.

All three checkers validate every byte of each span against `highlight-classes.json`:

- `vscode/test/check-grammar.mjs` uses `vscode-textmate` and `vscode-oniguruma`. A relevant scope
  must equal the expected `textmate` prefix or extend it with `.`. Delimiter scopes
  (`punctuation.definition.*`) inherit the enclosing construct's scope, except when directly
  inside `source.cambra`. A `null` expectation requires only the root scope.
- `nvim/test/check_syntax.lua` loads the file with `syntax sync fromstart`. It follows highlight
  links until the group name leaves the `cambra` namespace, then compares it with the expected
  `vim` group. Following standard-group links further would conflate `Boolean` and `Number` as
  `Constant`. A `null` expectation requires no syntax item.
- `web/scripts/check-highlight.ts` classifies each file as the inspector's source pane does
  ([Inspector](#inspector)). Every byte must get the span's class, or no class when the class's
  `textmate` prefix is `null`. This is exact where the TextMate check takes a prefix: a
  `keyword-other` span scoped `keyword.other.mutation` passes the TextMate check and fails here,
  because the pane colors it as `mutation`.

A span containing a newline byte fails. Each checker rejects an empty span set, and the shell gate
rejects an empty file corpus.

Two sets of tests keep the corpus complete. `tests/it/editor_grammars.rs` requires
`highlight-classes.json` to name exactly `HighlightClass::ALL`, and `sample.cambra` to parse and to
produce every class. The tests in `chl-parser/src/lexer.rs` require `sample.cambra` to contain every
escape in `ESCAPES` and the spelling of every keyword and operator or punctuation `Token` variant.
They sit in `chl-parser` because only its own tests see the `strum::EnumIter` derive that lists the
variants. A new operator therefore fails `cargo test` until the sample uses it, and then fails
`./ci.sh editors` until both grammars highlight it. `sample-lexes-only.cambra` holds the inputs that
must lex but cannot parse.

The web bundle `web/dist/index.html` embeds the TextMate grammar and `highlight-classes.json`, so a
change to either fails `ci_web`'s bundle comparison until `(cd web && npm run build)` regenerates
it.

### Adding a class

1. Add the variant to `HighlightClass`, to `HighlightClass::ALL` and to `HighlightClass::name`, and
   return it from `highlight_class` or `highlight`.
2. Add its entry to `highlight-classes.json`.
3. Add a construct of that class to `sample.cambra`.
4. Add the rule to both grammars.
5. If its `vim` group is new, add a `.cm-cambra-<Group>` rule to `web/src/style.css`; a test in
   `web/src/cambraSyntax.test.ts` fails until the palette has one.
6. Rebuild the web bundle: `(cd web && npm run build)`.

### When it fails

Each mismatch prints as `file:line:col: "text" is class; TextMate gave scope, expected prefix` or
the Vim equivalent, and every mismatching span is reported. Decide which side is wrong:

- The grammar is wrong when its rule disagrees with how the lexer tokenizes the text. Fix the
  rule. Inspect a scope in VS Code with **Developer: Inspect Editor Tokens and Scopes**, and a group
  in Neovim with `:Inspect`. In the inspector, a token's element carries the class as
  `cm-cambra-<class>`.
- The inspector alone fails when its regex engine reads a pattern differently from Oniguruma
  ([Inspector](#inspector)). Rewrite the pattern in the syntax both engines read the same way.
- The class is wrong when the lexer change was intended to highlight differently. Change
  `highlight_class` or `highlight-classes.json`.

To inspect one sample without running the full corpus:

```bash
mkdir -p target/editor-check
cargo run -q -p chl-parser --example dump_tokens -- editors/sample.cambra > target/editor-check/spans.jsonl
node editors/vscode/test/check-grammar.mjs target/editor-check/spans.jsonl editors/highlight-classes.json
nvim --headless -u NONE -i NONE -n --cmd 'set rtp^=editors/nvim' \
  -l editors/nvim/test/check_syntax.lua target/editor-check/spans.jsonl editors/highlight-classes.json
web/node_modules/.bin/vite-node --root web web/scripts/check-highlight.ts target/editor-check/spans.jsonl
```

## Indentation tests

`indent-cases.json` specifies the text above the cursor (`lines`) and the expected indentation of
the line Enter opens (`indent`). The cursor is at the end of the last supplied line. Both checkers
run under `./ci.sh editors` and reject an empty case set.

- `nvim/test/check_indent.lua` loads the indent plugin in headless Neovim, fills a buffer with the
  case's lines and one empty line, and calls `cambra_indent` on the empty line. It does not reindent
  the buffer with `=`, because the plugin leaves dedenting `elif` and `else` to the user.
- `vscode/test/check-indent.mjs` models Enter using `language-configuration.json` and TextMate
  tokens, with `editor.autoIndent: full`, `tabSize: 4`, and `insertSpaces` enabled. It applies
  `onEnterRules` in order, then the open-bracket rule, then indentation inheritance. Tabs advance
  to the next tab stop; outdent returns to the previous stop. This is a model, not a VS Code UI
  test. It does not test typing on the new line or **Reindent Lines**, so it does not exercise
  `decreaseIndentPattern` with nonempty text after the cursor.

A case an editor gets wrong carries that editor's name in `expected_failures`, with what it does
instead. The checker fails when such a case gets `indent`, so a fixed limit loses its marker. Every
Enter limit listed under [VS Code indentation limits](#vs-code-indentation-limits) has a case
marked `vscode`; no case is marked `nvim`.

`next` is the text of the line Enter opens and `rest` the lines after it.
`tests/it/editor_grammars.rs` requires each case's `lines`, `next` at `indent`, and `rest` to form a
program `parse_module` accepts.

## Inspector

The program inspector's source pane ([docs/inspector.md](../docs/inspector.md)) highlights with
`web/src/cambraSyntax.ts`. It imports `vscode/syntaxes/cambra.tmLanguage.json` and
`highlight-classes.json` into the bundle and restates no keyword, builtin or operator:

- `vscode-textmate`, the tokenizer VS Code runs, tokenizes each line in the page, so the pane
  re-highlights text as it changes.
- A token's class is the class whose `textmate` prefix is the longest one its relevant scope starts
  with, the relevant scope being the one [Editor highlight check](#editor-highlight-check) defines.
  The prefix of `mutation`, `keyword.other.mutation`, extends that of `keyword-other`, and the
  longer one wins.
- The token's element carries `cm-cambra-<class>` and `cm-cambra-<Group>`, the class's `vim` group.
  `web/src/style.css` colors the groups, so the pane draws the families Neovim draws.

VS Code runs the grammar's regular expressions under Oniguruma, compiled to WebAssembly. The pane
compiles them as JavaScript `RegExp`s with the `m` flag, so `^` and `$` match at line ends as in
Oniguruma, and keeps the WebAssembly out of the bundle. Where the two engines read a pattern
differently:

- `\b` and `\w` are ASCII in a `RegExp` without the `u` flag and Unicode in Oniguruma. They
  disagree only where a non-ASCII letter touches a word outside a string or comment, which the lexer
  reports as an error.
- The pane refuses a pattern holding `\A`, `\G`, `\z`, `\Z`, `\h`, `\H`, `\K`, `\R`, `\X`,
  `\O`, `\p`, `\P` or a POSIX bracket such as `[[:alpha:]]`, which a `RegExp` would read as
  something else.
- Possessive quantifiers, atomic groups and the other Oniguruma-only constructs fail to compile as a
  `RegExp`.

`web/src/cambraSyntax.test.ts` compiles every pattern in the grammar, so a pattern the pane cannot
run fails `./ci.sh fast` before it reaches the corpus check.

## Language server checks

The Neovim (`nvim/test/check_lsp.lua`) and VS Code (`vscode/test/lsp/suite.js`) checks use the same
four-line fixture:

```text
x = f(1]
y = "😀" $
def g(a):
    a
```

Both require:

- The client starts and attaches.
- Both lex errors arrive at the correct positions: `]` at line 1, column 8, and `$` at line 2,
  byte column 12 in Neovim or UTF-16 column 10 in VS Code. These are one-based columns.
- The outline lists `x` and `g`.
- The body of `g` folds.
- Replacing `]` with `)` leaves one diagnostic, and deleting the ` $` after `😀` leaves none.

The VS Code check also requires the related link from `]` to its `(`, the ranges of `g`'s outline
entry, and the extension's activation.

Neovim loads `lsp/cambra.lua` in a headless process. `vscode/test/lsp/run.mjs` launches the VS Code
suite through `@vscode/test-electron`. Both CI commands build the `cambra` binary before starting
the client; see [Running the checks](#running-the-checks) for dependencies and launch options.

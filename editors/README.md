# Editor support

Regex-based syntax highlighting for CHL source files (`.cambra`) in VS Code and Neovim. The
language id is `cambra` in both editors, and the TextMate scope is `source.cambra`.

| Directory | Contents |
| --- | --- |
| `vscode/` | A VS Code extension with no code: the language, its comment and bracket configuration, and the TextMate grammar `syntaxes/cambra.tmLanguage.json`. |
| `nvim/` | A Neovim runtime directory: filetype detection, a filetype plugin, an indent plugin, and the syntax file `syntax/cambra.vim`. |

A language server, run as `cambra --lsp`, is planned. It will add semantic tokens on top of these
grammars rather than replace them.

## Highlight classes

Both grammars classify the same constructs. `highlight-classes.json` lists each class with the
construct it covers, its TextMate scope prefix, and its Vim group; `null` means the construct is not
highlighted. The lexer assigns the classes: `highlight_class` and `highlight` in
`chl-parser/src/lexer.rs`.

The keyword lists match `KEYWORDS` in `chl-parser/src/lexer.rs`. The test
`tests/editor_grammars.rs` reads the `keyword-control`, `keyword-other` and `constant-boolean`
rules from the TextMate grammar and the `syn keyword` lines from the Vim syntax file, and fails when
either differs from the lexer. Keep each keyword class on one rule so the test can read it.

A string literal ends on the line it starts on
([1.7 Literals](../docs/chl-spec.md#17-literals)), so both grammars end a string at the end of its
line as well as at its closing quote. An unterminated string, which the lexer rejects, colors the
rest of its line and nothing after it. The editor highlight check below cannot exercise that rule,
because a file holding an unterminated string does not lex.

A `TODO`, `FIXME` or `XXX` in a comment is a word when no ASCII letter, digit or `_` touches it, the
characters that continue an identifier. Both grammars spell this boundary out instead of using `\b`
or `syn keyword`, whose word definitions include non-ASCII letters, and in Vim emoji. A combining
mark after the word is drawn with its last letter, so Vim colors the mark as part of the todo, while
the lexer and TextMate class it as comment.

An integer directly followed by a letter, as in `1if c else 2`, lexes as two tokens, and neither
grammar colors either of them: the `\b` in the TextMate rules and Vim's word boundary both need a
non-word character between the two.

### Builtins

The builtin names are the spellings in `SURFACE_BUILTINS` in `chl-parser/src/builtins.rs`, every
row of it: the functions, the transaction marker `begin`, the sink declarations `http_serve` and
`test_sink`, and the source `stdin`. Each is a name the compiler resolves by its spelling, which is
what the class marks; a row's kind says where the name is accepted, not whether it is a builtin.
`tests/editor_grammars.rs` reads the TextMate `builtin` rule and the Vim `syn match cambraBuiltin`
line, and fails when either differs from the table.

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
in the cases listed under [VS Code](#vs-code); `indent-cases.json` holds a case for each rule
([Indentation tests](#indentation-tests)).

## Editor highlight check

`./ci.sh editors` checks both grammars against the lexer over every `.cambra` file under `tests/`
and `editors/`. It needs Node and npm for the TextMate grammar and Neovim 0.11 for the Vim syntax
file. Without one, it skips that grammar and prints a line saying so; under CI it fails instead.
The first run installs `vscode-textmate` and `vscode-oniguruma` into `vscode/node_modules` from
`vscode/package-lock.json`.

The check has three parts:

1. `chl-parser/examples/dump_tokens.rs` prints the lexer's highlight spans as JSON lines: one span
   per logos token except `Newline`, a string literal split into string and escape runs, and a
   comment split into comment and todo runs. No span contains a newline, so a grammar rule that
   carries a string or comment onto the next line fails the check. Each checker fails a span that
   contains a newline byte.
2. `vscode/test/check-grammar.mjs` tokenizes each file with `vscode-textmate`. Every byte of a span
   must have a relevant scope equal to the class's `textmate` prefix or starting with it followed
   by `.`. The relevant scope is the innermost scope that is not `punctuation.definition.*`, so a
   string's quotes count as the string. A `punctuation.definition.*` scope directly inside
   `source.cambra` delimits nothing and is the relevant scope itself. A `null` prefix requires
   `source.cambra` alone.
3. `nvim/test/check_syntax.lua` opens each file in headless Neovim with `syntax sync fromstart`.
   Every byte of a span must resolve to the class's `vim` group. The group is found by following
   `hi link` from the syntax item's group until the name no longer starts with `cambra`. Following
   the standard groups' default links as well, as `synIDtrans` does, would make `Boolean` and
   `Number` both `Constant`. A `null` group requires no syntax item.

A checker that finds no span to check fails, and so does `./ci.sh editors` when it finds no
`.cambra` file.

Two sets of tests keep the corpus complete. `tests/editor_grammars.rs` requires
`highlight-classes.json` to name exactly `HighlightClass::ALL`, and `sample.cambra` to parse and to
produce every class. The tests in `chl-parser/src/lexer.rs` require `sample.cambra` to contain every
escape in `ESCAPES` and the spelling of every keyword and operator or punctuation `Token` variant.
They sit in `chl-parser` because only its own tests see the `strum::EnumIter` derive that lists the
variants. A new operator therefore fails `cargo test` until the sample uses it, and then fails
`./ci.sh editors` until both grammars highlight it. `sample-lexes-only.cambra` holds the inputs that
must lex but cannot parse.

### Adding a class

1. Add the variant to `HighlightClass`, to `HighlightClass::ALL`, to `HighlightClass::name`, and to
   the list in the `highlight_class_all_lists_every_variant` test, and return it from
   `highlight_class` or `highlight`.
2. Add its entry to `highlight-classes.json`.
3. Add a construct of that class to `sample.cambra`.
4. Add the rule to both grammars.

### When it fails

Each mismatch prints as `file:line:col: "text" is class; TextMate gave scope, expected prefix` or
the Vim equivalent, and every mismatching span is reported. Decide which side is wrong:

- The grammar is wrong when its rule disagrees with how the lexer tokenizes the text. Fix the
  rule. Inspect a scope in VS Code with **Developer: Inspect Editor Tokens and Scopes**, and a group
  in Neovim with `:Inspect`.
- The class is wrong when the lexer change was intended to highlight differently. Change
  `highlight_class` or `highlight-classes.json`.

To run one checker by hand, write the spans to a file first:

```bash
cargo run -q -p chl-parser --example dump_tokens -- $(find tests editors -name '*.cambra') > /tmp/spans.jsonl
node editors/vscode/test/check-grammar.mjs /tmp/spans.jsonl editors/highlight-classes.json
nvim --headless -u NONE -i NONE -n --cmd 'set rtp^=editors/nvim' \
  -l editors/nvim/test/check_syntax.lua /tmp/spans.jsonl editors/highlight-classes.json
```

## Indentation tests

`./ci.sh editors` also checks each editor's indentation against `indent-cases.json`. A case holds
`lines`, the text above the cursor, which sits at the end of the last line, and `indent`, the
column of the line Enter opens there. Each checker fails when it reads no case.

- `nvim/test/check_indent.lua` loads the indent plugin in headless Neovim, fills a buffer with the
  case's lines and one empty line, and calls `cambra_indent` on the empty line. It does not reindent
  the buffer with `=`, because the plugin leaves dedenting `elif` and `else` to the user.
- `vscode/test/check-indent.mjs` computes what VS Code's Enter does with
  `language-configuration.json`, with `editor.autoIndent` at `full`, `tabSize` 4 and `insertSpaces`
  on. It follows `getEnterAction` and `getIndentForEnter` in VS Code's
  `src/vs/editor/common/languages/`:
  1. Tokenize each line with the TextMate grammar, and delete the configured brackets from its
     comment, string and regex tokens.
  2. Take the action of the first `onEnterRules` entry whose `beforeText` matches the last line and
     whose `previousLineText`, if it has one, matches the line above. An `afterText` is matched
     against the empty string.
  3. With no entry matched, indent when the last line ends in an open bracket.
  4. With neither, take the last non-blank line's indent, one level more when that line matches
     `increaseIndentPattern`.

  `indent` adds a tab plus the entry's `appendText`, and the tab reaches the next tab stop.
  `outdent` moves back to the previous tab stop. The model does not cover typing on the new line, so
  `decreaseIndentPattern` and **Reindent Lines** are not checked.

A case an editor gets wrong carries that editor's name in `expected_failures`, with what it does
instead. The checker fails when such a case gets `indent`, so a fixed limit loses its marker. Every
Enter limit listed under [VS Code](#vs-code) has a case marked `vscode`; no case is marked `nvim`.

`next` is the text of the line Enter opens and `rest` the lines after it. `tests/editor_grammars.rs`
requires each case's `lines`, `next` at `indent`, and `rest` to form a program `parse_module`
accepts.

## VS Code

Link the extension into the extensions directory and reload the window:

```bash
ln -s "$PWD/editors/vscode" ~/.vscode/extensions/cambra-dev.cambra-0.1.0
```

Or package and install it, which needs Node:

```bash
cd editors/vscode
npx @vscode/vsce package --skip-license
code --install-extension cambra-0.1.0.vsix
```

`--skip-license` is needed because the license file is at the repository root, not in the
extension directory.

To check it, open a `.cambra` file such as `tests/programs/http_counter/program.cambra`. The status
bar shows the language as Cambra. **Developer: Inspect Editor Tokens and Scopes** shows the scope
under the cursor, which ends in `.cambra`.

Indentation follows [Indentation](#indentation). Typing `elif` or `else` and its `:` dedents the
line one level, which lands it on its chain's level when the body above it sits at the level Enter
gave it. These cases are out of reach of `language-configuration.json`'s regular expressions:

- A line after a multi-line bracketed header indents from the header's last line rather than its
  first, so the body of `def f(a,` / `      b):` lands at column 8, one tab stop past the last
  line's indent.
- After a multi-line bracketed expression, the next line keeps the indent of the expression's last
  line rather than its first.
- A line ending in an open bracket indents the next line one level, where Neovim keeps the line's
  own level.
- A `#` inside a string reads as a comment, so `if s == "#":` does not indent the next line.
- A `return` or `pass` line that leaves a bracket open outdents the continuation line, so after
  `    return f(a,` the next line starts at column 0, one level left of `return`. The outdent rule's
  lookahead exempts only a line that ends in an open bracket. Neovim indents it at the `return`
  line's level, because it checks the bracket balance before the dedent rule.
- **Reindent Lines** reads only `indentationRules`, which indent once after any header, so it
  places an assignment's `if` bodies one level short of where Enter places them.

Enter's two levels after an assignment's `if` are the editor's indent plus four spaces, the rule's
`appendText`.

## Neovim

Add the runtime directory to `runtimepath` in `init.lua`:

```lua
vim.opt.runtimepath:append("/path/to/cambra/editors/nvim")
```

The filetype plugin sets `commentstring` to `# %s` and indents with 4 spaces. The indent plugin,
`indent/cambra.lua`, follows [Indentation](#indentation), and measures from the first line of a
header that spans several lines inside brackets. It reindents only on Enter, `o`, `O` and an
explicit request, so typing `elif` or `else` does not move the line; dedent it by hand.

To check it, open a `.cambra` file and run `:set filetype?`, which prints `filetype=cambra`.
`:Inspect` shows the syntax group under the cursor. The same check runs headless:

```bash
nvim --headless -u NONE --cmd 'set rtp^=editors/nvim' \
  -c 'filetype plugin indent on' -c 'syntax on' \
  -c 'e tests/programs/arithmetic/program.cambra' -c 'echo &ft b:current_syntax' -c 'qa!'
```

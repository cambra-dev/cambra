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

Both grammars classify the same constructs.

| Construct | TextMate scope | Vim group |
| --- | --- | --- |
| `#` comment | `comment.line.number-sign` | `Comment` |
| `TODO`, `FIXME`, `XXX` as a word inside a comment | `keyword.other.todo` | `Todo` |
| `"…"`, `'…'` string, ending at the closing quote or the end of the line | `string.quoted.double`, `string.quoted.single` | `String` |
| Escape `\n \t \r \\ \" \' \0` | `constant.character.escape` | `SpecialChar` |
| Decimal integer | `constant.numeric.integer.decimal` | `Number` |
| `True`, `False` | `constant.language.boolean` | `Boolean` |
| `if elif else for in return yield match case pass with` | `keyword.control` | `Statement` |
| `def where and or not` | `keyword.other` | `Keyword` |
| Name after `def` | `entity.name.function` | `Function` |
| Builtin name, a spelling in `SURFACE_BUILTINS` | `support.function.builtin` | `Function` |
| Capitalized identifier (a type) | `entity.name.type` | `Type` |
| Type hole `_` directly after `:`, `<:`, `=>` or `{` | `entity.name.type` | `Type` |
| Variant tag `` `name `` | `variable.other.enummember` | `Constant` |
| Decorator `@Name` | `entity.name.function.decorator` | `PreProc` |
| Lambda `\` | `storage.type.function.lambda` | `Special` |
| Mutation `:=`, feed `<<`, define `<<=` | `keyword.other.mutation`, `keyword.other.feed`, `keyword.other.define` | `Special` |
| Other operators | `keyword.operator.*` | `Operator` |

The keyword lists match `KEYWORDS` in `chl-parser/src/lexer.rs`. The test
`tests/editor_grammars.rs` reads the `keyword-control`, `keyword-other` and `constant-boolean`
rules from the TextMate grammar and the `syn keyword` lines from the Vim syntax file, and fails when
either differs from the lexer. Keep each keyword class on one rule so the test can read it.

A string literal ends on the line it starts on
([1.7 Literals](../docs/chl-spec.md#17-literals)), so both grammars end a string at the end of its
line as well as at its closing quote. An unterminated string, which the lexer rejects, colors the
rest of its line and nothing after it.

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
after `def` links to, so the two share a color in Vim.

### Type annotations

Capitalized names are types wherever they appear, so an annotation's named types are colored in
every position. The one other spelling a type can have is the hole `_`, and it is colored as a type
only directly after `:`, `<:`, `=>` or `{`. Elsewhere `_` is a pattern binder (`` `some(_) ``) or a
refinement's subject (`{Int where _ > 0}`), and a regex cannot tell the hole in `List(_)` or
`{Int, _}` from the binder in `` `some(_) `` without parsing the enclosing construct. The one
position the rule colors wrongly is a one-line `match` arm in a refinement whose body starts with
the subject, as in `` case `some(x): _ ``.

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
- Otherwise, at the same level.

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
gave it. Three cases are out of reach of `language-configuration.json`'s regular expressions:

- A line after a multi-line bracketed header indents from the header's last line rather than its
  first, so the body of `def f(a,` / `      b):` lands at column 8, one tab stop past the last
  line's indent.
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

# CHL Parser Design

`chl-parser` converts source text into a span-bearing AST. Its recovery aims to report every
problem in a file in one pass: it returns diagnostics and, when recovery succeeds, a partial AST.
The limits on that are under [Error recovery](#error-recovery).

## Stack: logos + chumsky

The crate uses Logos `0.14` for tokenization and Chumsky `1.0.0-alpha.8` for parsing, as declared
in `Cargo.toml`. Ariadne renders the structured diagnostics. Dependency declarations, rather than
this reference, own version requirements.

## Architecture

```text
source → Logos tokens → layout tokens → Chumsky grammar → CHL AST → CCL lowering
```

The layout pass emits `Newline`, `Indent` and `Dedent` tokens. The grammar consumes those
tokens rather than computing indentation. AST types live in `ast.rs`; error conversion and
rendering live in `parser/error.rs`.

### Stage 1 — Lexer (`lexer.rs`)

`tokenize` runs Logos, validates tag adjacency with `check_tags`, then resolves layout. It never
fails: [Lexer recovery](#lexer-recovery) specifies the stream and errors it returns for a source
with lexical errors. This section describes a source with none.
Logos produces span-bearing keywords, identifiers, literals, punctuation and physical newlines.
It skips comments and horizontal whitespace. The source-level layout rules are owned by
[Indentation](../docs/chl-spec.md#13-indentation-off-side-rule); the implementation uses two
level forms:

- `Fixed(column)` records an established indentation width. Increasing indentation emits
  `Indent`; closing the level emits `Dedent`. A dedent that reaches no compatible level
  produces `InconsistentIndent`.
- `Pending { min }` records the assignment column when a block starts within a logical line.
  Entering this level emits no `Indent`. A branch body opens a `Fixed` level above it; the first
  line that dedents back into it, the `elif` or `else`, fixes its column. A line at or below
  `min` closes it. The parser's `block_value` consumes the extra closing `Dedent` after parsing
  the `if` or `match` statement.

The stack starts with `Fixed(0)`. `block_value_open` requests a pending level when a logical
line ends in `:` but did not start with a block-opening keyword. The floor comes from the
logical statement's first line, not a later physical line containing the colon. Blank and
comment-only lines do not consume the pending request or change the stack.

A stack of open brackets suppresses physical newlines and indentation processing while it is
nonempty. Every open bracket belongs to the current logical line. A close bracket must match the
innermost open bracket's kind.

The token stream ends with a `Newline` and enough `Dedent`s to close the stack.
Ordinary blocks balance `Indent` and `Dedent`; each pending assignment-side level contributes
one extra `Dedent`. Tests include `block_right_hand_side_opens_a_level_of_its_own`,
`a_wrapped_header_floors_the_level_at_the_statement`,
`the_chain_column_is_fixed_by_its_first_line` and
`a_match_right_hand_side_closes_its_level_unpinned`.

A string literal ends at its closing quote on the same line. A backtick is immediately followed
by an identifier. `raw_tokens` runs Logos and these two checks once for both `tokenize` and
`highlight`.

`KEYWORDS` lists every keyword spelling with its token. The editor grammars under `editors/` list
the same spellings, and `tests/it/editor_grammars.rs` fails when they differ
([editors/README.md](../editors/README.md#highlight-classes)).

`highlight` maps source to highlight spans: each logos token's `HighlightClass` from
`highlight_class`, with string escapes, comments and the `TODO_WORDS` inside comments as spans of
their own. An identifier that `SurfaceBuiltin::from_name` resolves is a `Builtin`. A `Token::Error`
gets no span. It never fails, and returns the errors `raw_tokens` found beside the spans.
`./ci.sh editors` checks both editor grammars against it
([editors/README.md](../editors/README.md#editor-highlight-check)).

A statement opens a block either from its head keyword (`if`, `def`, …) or from
an assignment's right-hand side, and the layout pass tells them apart by the
line's first token. On a line that begins with `pub`, the second token is the
statement's head, so `pub def f():` opens its body as `def f():` does.

### Stage 2 — Parser (`parser.rs`)

A chumsky combinator parser consumes the layout-resolved token stream and
produces the AST defined in [`ast.rs`](#stage-3--ast-astrs). The public interface includes:

- `parse_module(FileId, &str)` — a sequence of top-level statements.
- `parse_expression(FileId, &str)` — a single expression (used by the lowering
  tests that build expressions in isolation).
- `ParseError` — a uniform error type wrapping either a `LexError` or a
  structured chumsky error (`ParseErrorInfo`) carrying its span, found token, and
  categorised expected set. The diagnostics types (`ParseError`, `ParseErrorInfo`,
  `ParseResult`, `CATEGORIES`) live in the `parser/error.rs` submodule, re-exported
  from `parser.rs`.

Binary-operator productions follow
[Expression precedence](../docs/chl-spec.md#23-expression-precedence).
Most levels build from the next tighter level. Exponentiation and unary minus share a recursive
production because `**` binds more tightly than unary minus on its left and less tightly on
its right.

Bracket-enclosed expression positions use `bracketed_expr`, the choice between a one-line
`match` and an ordinary expression. The closing delimiter bounds the arm list; ordinary
expression positions do not admit that form. The surface rule is
[The one-line form](../docs/chl-spec.md#the-one-line-form).

The grammar does not accept every token in operator position. For example, `in` is a keyword
consumed by iteration clauses, not an implemented membership operator. `>>` is two `Gt`
tokens, and `is` is an identifier. `/`, `%` and `~` start no token and lex as `Token::Error`.
`operators_absent_from_chl` covers the lexical cases.
Experimental `^+` and `^=` tokens are accepted but omitted from the language reference.

### Stage 3 — AST (`ast.rs`)

Key shape choices:

- **Every node carries a span** via `Spanned<T>`, so diagnostics for any
  sub-expression have precise location info. A `Span` is a `FileId` and a byte
  range of that file; the `FileId` indexes the compilation's `SourceMap`
  (`source_map.rs`), which diagnostics render against. The map also records the
  module path of each file that has one. The parser receives the
  `FileId` as chumsky's span context, and chumsky builds every span it derives
  from the end-of-input span's context, so each node's span names the file the
  entry point was given.
- Operators use `BinOp`, `CmpOp`, `BoolOp`, `UnaryOp` and `AugOp` variants. Lowering can
  match those enums exhaustively; their presence in the AST does not guarantee that every
  operand type is supported.
- `Stmt::If` stores one `IfBranch` per `if`/`elif` and an optional `else_body`. It does
  not nest an `if` statement inside an `else` to represent the chain.
- `Expr::Block` wraps an `if` or `match` statement in value position. Assignment-side
  blocks and one-line `match` therefore reach the same lowering entry, `lower_final_stmt`.
  `match_arms` parameterizes the arm-body production; `assign_tail` parameterizes the
  right-hand side for all six assignment forms.
- `Expr::Record` represents a record value. `BraceRecord`, `BraceGroup` and
  `BraceRefinement` retain type syntax for lowering to interpret. The distinction between
  `{T,}`, `{T}`, `{}` and refinements is specified under
  [Atoms](../docs/chl-spec.md#24-atoms) and
  [Refinement syntax](../docs/chl-spec.md#64-refinement-syntax).
  Bracketed predicates also use `bracketed_expr`.
- `Expr::FunctionType` represents right-associative `=>` below feed precedence.
  Its operands are expressions; lowering validates their use as types.
  A `def` return annotation consumes its delimiter before this production runs, so its
  return type may itself contain `=>`.
- `k -> v` constructs `Expr::Tuple`, the same node as `(k, v)`. No map-literal node is
  introduced. Pair-arrow precedence places `k -> v if c else w` around the conditional
  value, and `m << k -> v` feeds the pair. Chaining `->` reports a custom error.
- `Expr::Feed` and `Stmt::Define` directly represent `<<` and `<<=`. They are not
  shift-operator variants requiring later reclassification.
- **Type parameters are split out of the parameter list.** A capitalized `def` parameter is a
  type parameter ([docs/chl-spec.md](../docs/chl-spec.md), "Type parameters"), so
  `Stmt::FunctionDef` carries `type_params: Vec<TypeParam>` beside `params`, and `params` alone
  is the arity. The split happens as the list is parsed (`split_params`), which rejects a type
  parameter after a value parameter. A type parameter's annotation is a `KindAnnotation`: its kind
  `T: K` or its bound `T <: U`. `ast::is_type_name` is the capitalization test; the lexer,
  parser and lowering all call it.
- **A `def`'s name carries its own span.** `Stmt::FunctionDef.name` is a `Spanned<SmolStr>`
  covering the identifier after `def`, as `Stmt::Param.name` covers its name. The statement's span
  starts at `def`, so a consumer pointing at the name, such as a language server's symbol
  selection range, cannot derive it from the statement.
- **A polymorphic type has its own variant.** `forall (T, U <: B) V requires …` parses to
  `Expr::Forall`, whose binder list holds only type parameters. The `)` closing the list ends the
  last kind, so the body follows with no separator.
- **A `requires` clause ends a signature.** `requires_clause` parses
  `requires Addable(A, B, Output=O), Transaction` into `Vec<Spanned<Requirement>>`, operands
  first and associated types by name after them. It follows a `def`'s `=>` result and a
  `forall`'s body. A clause after a nested `forall`'s body belongs to the innermost one.
- **Module statements have their own variants.** `Stmt::Import`, `Stmt::Run`,
  `Stmt::Param` and `Stmt::Discard` carry the statements of
  [docs/chl-spec.md](../docs/chl-spec.md), "9. Modules". `Stmt::Pub`
  wraps the statement `pub` marks rather than being a field of each statement
  that can introduce a member, so one rule (`pub_refusal`) refuses `pub` on every
  statement that introduces none, `import` and `run` among them. It carries the
  keyword's span, because on a `@LoadFrom` declaration `pub` stands on the line
  below the decorator, where the statement does not start. A renamed run is a
  `Stmt::Run` whose `renamed_from` names the predecessor's run, since the
  decorator changes only which run it pairs with.
-  **A module path is written, then resolved.** `ast::WrittenPath` is a path as
  a statement writes it, each segment with its span. `module_path::ModulePath`
  is the path itself: segments shared behind an `Arc`, ordered by spelling, the
  identity loading keys modules by and the `SourceMap` records per file.
  `module_path::segment_error` holds the segment rule of
  [docs/chl-spec.md](../docs/chl-spec.md), "9.15 Module files", which the parser
  applies to a written path and loading applies to a root file's name.
- **One production spells a `::` path.** `qualified_name` parses a name and its
  qualifier in every position that names a member: a reference
  (`Expr::Qualified`), a field access's label (`Expr::Attribute`'s
  `attr_qualifier`), and a record field's label (`RecordField::qualifier`). An
  empty qualifier is the current module's label. A tag's qualifier precedes its
  backtick, `` mod2::`some ``, and `tag_name` parses it for a constructor, a
  variant type's arm, and a `case` pattern alike. Lowering refuses every module
  construct before it lowers anything (`src/ccl/lower/module_syntax.rs`).

## Surface builtins

`builtins.rs` lists the names a CHL call recognizes as builtins in `SURFACE_BUILTINS`. Each row
holds a spelling, its `SurfaceBuiltin` variant, an arity, and a kind. The parser does not read the
table: a builtin call parses as an ordinary `Expr::Call`. The table lives in this crate because
both of its consumers depend on this crate, and `chl-interp` depends on nothing else.

A consumer resolves a called name with `SurfaceBuiltin::from_name` and matches on the variant. The
table records names and call shapes, not meaning. Each consumer keeps three decisions:

- **What the builtin denotes.** Lowering and evaluation bodies stay with their consumer.
- **A call of the wrong arity.** Lowering refuses it. The interpreter treats it as an unknown
  function.
- **Shadowing.** Lowering resolves a `Function`-kind builtin before consulting scope, so a user
  `def` of the same name does not shadow it. A builtin of another kind called in expression
  position lowers as an ordinary call, where a user `def` does win, and a registered source wins
  over a user binding
  ([src/ccl/design/lowering.md, "Builtin calls"](../src/ccl/design/lowering.md#builtin-calls)).
  The interpreter lets the nearest binding win
  ([chl-spec.md, "3.2 Names"](../docs/chl-spec.md#32-names)).
  `a_user_function_named_like_a_builtin_is_ignored` in `tests/it/differential_interp.rs` pins the
  difference.

The kind says which construct recognizes the call:

| Kind | Position | Lowering's recognizer |
|---|---|---|
| `Function` | a call in expression position | `lower_call` |
| `TransactionMarker` | the context of `with begin():` | `validate_begin_context` |
| `SinkDeclaration` | the right-hand side of an assignment that declares a sink | `sink_declaration` |
| `Source` | a call to a registered data source | `LoweringContext::sources` |

A source resolves by its registration, not by the table, so a host can register a source the table
does not list. The table lists the sources every `GlobalContext` registers, and
`default_sources_are_the_listed_sources` in `src/ccl/context.rs` holds the two sets equal. Lowering
does not check a source call's argument count against the table.

`test_sink` is listed unconditionally. Lowering recognizes it only under `cfg(test)` or the
`test-helpers` feature, and the interpreter recognizes it always. Gating the row would need a
feature on this crate that only one of its consumers enables.

### Rows that differ from the spec

[chl-spec.md, "7. Built-in functions and sources"](../docs/chl-spec.md#7-built-in-functions-and-sources)
is the specification for most rows. Five rows are specified in other sections:

- `set`, `map`, and `empty_map` in
  [chl-spec.md, "3.11 List, tuple, record literals"](../docs/chl-spec.md#311-list-tuple-record-literals).
- `begin` and `await_final` in
  [chl-spec.md, "8. Mutability, transactions, and feeds"](../docs/chl-spec.md#8-mutability-transactions-and-feeds).

These rows and the spec disagree:

- `test_sink` has no entry in the spec.
- `http_serve` is a source and a sink in the spec, and its kind here is `SinkDeclaration` alone,
  because lowering recognizes it by `sink_declaration`.
- The spec's planned aggregates (`count`, `avg`, `len`) and tentative builtins (`str`,
  `open`, `stdout`, `restrict`) have no row.

## Error recovery

The grammar installs bracket and statement recovery through `recover_with(via_parser(...))`.
Successful recovery records the original error and returns an error node spanning the skipped
region. Callers must inspect diagnostics even when an AST is available.

### Bracket-level recovery

The atom parser installs `nested_delimiters` recovery for parentheses, brackets and braces,
recognizing the other two delimiter kinds while seeking the matching closer.
A recovered region becomes `Expr::Error`. In `x = (1 +) + 2`, recovery replaces the
parenthesized subexpression and allows parsing the enclosing assignment.

This mechanism requires a recoverable delimiter region. It does not handle every expression
failure. It relies on the lexer's stream having balanced brackets
([Lexer recovery](#lexer-recovery)).

### Statement-level recovery

`skip_to_newline` consumes at least one token other than `Newline` or `Dedent`, followed
by an optional `Newline`. If an `Indent` follows, `skip_indented_block` consumes its
balanced block. The result is `Stmt::Error` over the skipped region. Discarding an attached
body prevents a malformed header from leaving orphan block tokens in the enclosing parser.

Recovery stops before `Dedent` rather than scanning through it. Its `at_least(1)` requirement
makes it decline at `Newline`, `Dedent` and EOF when no token has been consumed. This prevents
a zero-progress success inside `repeated()` and lets an enclosing block consume its own
`Dedent` without an additional diagnostic.
`nested_block_recovery_reports_one_error_per_mistake` covers that boundary behavior.

A semicolon terminates a valid simple statement, but is not a synchronization token for this
recovery parser. Recovery can therefore discard later semicolon-separated text on the same
logical line. It does not promise one error per source-level mistake.

### Lexer recovery

`tokenize` accepts every input. It returns `Lexed { tokens, errors }`: a token stream the grammar
can parse, and every lexical error found, in source order. A source with no lexical error yields
no errors and the token stream described under [Stage 1](#stage-1--lexer-lexerrs). The rules
below decide what the stream holds where the source is wrong.

Two invariants hold for every input:

- **Brackets in the stream balance.** Every `(`, `[` and `{` has a closer of its own kind, nested
  correctly. Bracket-level recovery seeks the matching closer, so an unbalanced stream would send
  it to the wrong token or to the end of the file. The lexer drops a closer that matches nothing
  and inserts a zero-width closer, a closer whose span is empty and covers no source text, for an
  opener the source never closes.
- **Layout has its usual shape.** The stream ends with a `Newline` and the `Dedent`s that close
  the indentation stack, as on valid input.

#### Characters no token matches

A maximal run of characters that start no token becomes one `Token::Error` and one
`InvalidToken`. No grammar rule accepts `Token::Error`, so statement-level recovery skips the
rest of the line.

```text
x = a $$ b        →  x = a <Error> b       InvalidToken at `$$`
```

#### Unterminated strings

A string literal ends at its line's end when it has no closing quote. Its token is a `String`
holding the text after the quote, and `UnterminatedString` points at the opening quote. The
newline after it remains a token, so the next line starts a statement.

```text
x = "abc          →  x = String("abc")     UnterminatedString at `"`
y = 1                y = 1
```

#### Detached backticks

A backtick not immediately followed by an identifier is dropped from the stream, with
`DetachedBacktick` at the backtick.

#### Close brackets

A close bracket is compared with the open brackets on the stack:

- **It matches the innermost.** The pair closes.
- **It matches an outer one.** Each open bracket inside that one gets a zero-width closer just
  before the close bracket. The innermost gets one `MismatchedClose` at the close bracket, naming
  both; the others get an `UnclosedBracket` at their openers. The close bracket then closes the
  outer one. CPython reports the same pair ("closing parenthesis ']' does not match opening
  parenthesis '('"), and rustc labels both brackets.

  ```text
  xs = [f(a]      →  xs = [ f ( a ) ]       MismatchedClose: `]` does not match `(`
  ```

  When a line that ends the outer bracket's statement came before the close bracket, the outer
  bracket was most likely the one left open, and it closes at that line instead
  ([Unclosed brackets](#unclosed-brackets)).

- **It matches none.** It is dropped, and the innermost open bracket, if any, keeps going. Which
  error it reports waits until that open bracket closes, because either bracket can be the
  mistake: a `]` typed for `)`, or a stray `]`. If the open bracket closes later, the close
  bracket was stray and gets `UnmatchedClose`. If it never closes, one `MismatchedClose` at the
  close bracket names both, and the open bracket gets no `UnclosedBracket` of its own.
  Either way the open bracket closes no later than the first line that ends its statement
  ([Unclosed brackets](#unclosed-brackets)).

  ```text
  x = f(a))       →  x = f ( a )            UnmatchedClose at the second `)`

  x = f(a]        →  x = f ( a )            UnmatchedClose at `]`
      + b)               + b )

  x = f(a]        →  x = f ( a )            MismatchedClose: `]` does not match `(`
  y = 2              y = 2
  ```

  Neither error commits to one reading, and neither does the token stream: the open bracket
  closes where layout says it does. CPython reports the third case the same way ("closing
  parenthesis ']' does not match opening parenthesis '('"), and stops. rustc labels both brackets
  in the third case. In the second, it reports the enclosing function's final `}` as an unexpected
  closing delimiter, and labels both `]` and `)` as missing an open bracket.

#### Unclosed brackets

Inside brackets the layout pass drops physical newlines and skips indentation, so an open
bracket that is never closed turns every later line into part of one logical line. At the end of
input each open bracket gets a zero-width closer and an `UnclosedBracket` at its opener.

That alone leaves the rest of the file inside the bracket. A physical line inside brackets ends
their statement when it starts at or left of the indentation of the line the statement began on,
with a token other than a close bracket. A close bracket on its own line, flush with its
statement, ends the bracketed list and not the statement:

```text
xs = [
    1,
]
```

An open bracket closes before the first line that ends its statement in three cases:

- A close bracket of another kind met it while it was innermost
  ([Close brackets](#close-brackets)). The first layout pass closes it there.
- The first layout pass ended with it open. `tokenize` runs layout a second time, in which it
  closes there.
- The first layout pass closed it with a close bracket of its kind, after a line that ended its
  statement, and closed brackets inside it with zero-width closers on the way. The second layout
  pass closes it at that line, and the close bracket is then compared with the brackets open in
  the second pass.

```text
x = f(a, b        →  x = f ( a , b )        UnclosedBracket at `(`
y = 2                y = 2

x = f(a           →  x = f ( a )            UnclosedBracket at `(`
y = [1, 2)           y = [ 1 , 2 ]          MismatchedClose: `)` does not match `[`
z = 3                z = 3
```

CPython 3.14 reports the `)` in the second example with the same message, and stops there.

Each case needs a lexical error, so a source with none is laid out once and keeps the tokens it
had before recovery existed. Layout runs at most twice: the second pass closes the brackets the
first found, and its own findings are not acted on.

The rule closes too early where an unclosed bracket's own continuation lines start at the
statement's indentation. `b,` and `c` become statements of their own rather than elements:

```text
ys = (a,          →  ys = ( a , )           UnclosedBracket at `(`
b,                   b ,
c                    c
```

The rule does not test the line's first token for a statement keyword. Most statements start
with a name (`y = 2`, `out = stdout()`), so a keyword condition would leave every such line
inside the bracket.

#### Inconsistent indentation

A line whose indentation matches no enclosing level gets `InconsistentIndent` at its first token
and belongs to the deepest enclosing level left of it. No `Indent` is emitted for it.

```text
if c:
    x = 1
  y = 2           →  y = 2 is a statement after the `if`      InconsistentIndent at `y`
```

#### One diagnostic per lexical error

`parse_module` and `parse_expression` report the lexer's errors first, then parse the stream. A
grammar error whose found token is a `Token::Error` or a zero-width closer is dropped from the
result, because the lexical error at that place already reports it. Each zero-width closer comes
with exactly one `UnclosedBracket` or `MismatchedClose`, which `tokenize` asserts in debug builds.

The dropped error can be a second mistake at the same place. In `x = f(a if`, the parser expects
an expression at the zero-width `)`, and only the `UnclosedBracket` is reported.

Only its empty span marks a zero-width closer. A consumer that needs to know a bracket is
synthesized, such as a formatter or an AST span, has nothing else to read.

#### Later: parser-driven recovery for unclosed brackets

The second layout pass decides where a bracket should have closed from indentation alone. An
indented line after the opener stays inside the bracket, so here the bracket closes before
`def g` and the grammar reports `return` as well:

```text
def f(x:          →  def f ( x : return x )      UnclosedBracket at `(`
    return x                                     grammar error at `return`
def g():             def g ( ) : …
```

The parser knows more: the point at which a bracketed list cannot continue, here `return`. Ruff's
Python parser uses that point. It pulls tokens from its lexer one at a time, and when a bracketed
list fails it asks the lexer to re-read the last newline inside the bracket as a statement boundary
and lex onward from there.

Chumsky parses a token slice built before parsing begins (`parse_module`), and it backtracks, so
the grammar has no point at which to ask the lexer for different tokens. Two designs keep the
idea without that:

- **Re-parse.** Parse; when the first grammar error falls inside a bracket the lexer reported
  unclosed, lex again with that bracket closed before the error's line, and parse again. At most
  one round per unclosed bracket.
- **A pull parser.** Replace the Chumsky grammar with a hand-written parser that pulls tokens, as
  Ruff's does.

A third design fixes the diagnostics and leaves the tokens alone. On a grammar error, CPython's
`_PyPegen_tokenize_full_source_to_check_for_errors` (`Parser/pegen_errors.c`) tokenizes the rest
of the source. If the tokenizer fails, at the end of input included, while a bracket opened on a
line before the grammar error's line is open, it replaces the grammar error with "'(' was never
closed" at that bracket. Here the analogue drops a grammar error that falls between an
`UnclosedBracket` and its zero-width closer, on a later line than the bracket. In the example
above it removes the error at `return`, and `return x` stays inside `f`'s parameter list.

None is implemented. A recovery corpus case where the second layout pass closes a bracket at the
wrong line is the evidence for the first two. A grammar error inside an unclosed bracket that a
corpus golden reports is the evidence for the third.

### Recovery API

Both public parse functions return `ParseResult<T>`:

```rust
pub struct ParseResult<T> {
    pub value: Option<T>,
    pub errors: Vec<ParseError>,
}
```

`value` and `errors` are independent outputs. Lexical errors come first in `errors`, and parsing
runs after them. An unrecovered grammar failure returns no AST. Recovery can return an AST
containing `Expr::Error` or `Stmt::Error`. A `validate` rule can instead report a custom error while
retaining an ordinary node; a nonempty error list does not imply that the AST contains a hole.

For example, `parse_expression(file, "1 +")` has no AST, whereas
`parse_expression(file, "1 -> 2 -> 3")`
retains a pair node and reports that the pair arrow does not chain.
`is_ok()` requires both a value and no errors. `into_result()` rejects any recorded error;
if both outputs are empty, it synthesizes a parse error at `0..0`.

### Threading partial ASTs through to lowering

`run_frontend` in `src/ccl/context.rs` accumulates parse errors before examining the AST.
If no module is available, it returns those errors. An empty module gets an empty-program
diagnostic. Otherwise it invokes `lower_stmts` even when parsing reported errors, lexical errors
included, allowing independent lowering errors to appear in the same response. Lowering sees the
token stream [Lexer recovery](#lexer-recovery) leaves, so a call the lexer closed with a
zero-width closer lowers as an ordinary call.

Lowering maps recovered error nodes to `TypedExprNode::Error` without reporting the same
parse failure again. `LoweringResult` also carries an optional value and errors.
The frontend appends lowering errors and returns if no CCL value is available or if either
stage reported an error. Inference and later phases do not run on that result.
This guard applies to diagnostics from validation as well as explicit AST holes.

The returned `Vec<CompileError>` contains stage-tagged errors, not an assertion that all
possible errors were discovered. Regressions include `multiple_parse_errors_all_surface`,
`lex_and_parse_errors_both_surface` and `multiple_lowering_errors_all_surface` in
`src/ccl/context.rs`.

### Error message quality

`ParseErrorInfo` owns source-independent diagnostic data: a primary span, optional custom
message, found token, categorized expected entries, and context labels with spans.
Four mechanisms construct that information:

1. `Token::Display` supplies source-like token names, such as `(` or `integer literal`,
   rather than enum debug names.
2. `labelled` names a production's expected input when it fails at the start.
   `as_context` also records an enclosing production after partial progress.
3. `rich_to_info` collapses complete expected-token categories from `CATEGORIES`.
4. A validation rule can emit `Rich::custom`. Its message replaces the derived
   found/expected text in both single-line and source-context rendering.

The labeled productions include atoms and the outer expression choice (`expression`),
attribute/lambda names (`identifier`), function and parameter names, the block opener
(`indented block`), and the statement choice (`statement`).
The outer expression and statement labels also contribute contexts.

Category conversion sorts and deduplicates tokens and labels first. It replaces a category
only when every listed member is present; a partial category remains a list of tokens.
The final ordering is labels, categories in table order, remaining tokens, then end-of-input
and other-pattern entries. The category table is not an exhaustive operator list: for example,
`**` is not a member of the current binary-operator category.

Custom messages must be retained independently of the expected set. Otherwise a rule such as
the rejection of `{Int}` could lose its explanation and render only "found end of input".
`custom_grammar_errors_keep_their_message` and
`custom_grammar_errors_render_with_source_context` cover both rendering paths.

### Rendering with `ariadne`

`ParseResult<T>` exposes two output methods:

- `.render_errors(&SourceMap) -> String` — ariadne output with colour disabled
  (for tests, log files, snapshot rendering).
- `.eprint_errors(&SourceMap)` — colour output to stderr (for interactive
  use).

Both build one `Report` per `ParseError`, with a red primary label at
the failure span and one yellow secondary label per `.as_context()`
entry. Lex errors get a single-label report.

Every label span goes through `label_span`, which clamps `end` up to `start`.
ariadne panics on an inverted range, and chumsky produces one for the
`.as_context()` spans of a custom error raised inside a `validate`: the context
records where its labelled parser opened, while the error's own offset has not
advanced past it, so an outer context can arrive as `3..2`. An inverted span
carries a position but no extent, so collapsing it to empty keeps the
"while parsing …" note pointing at the right place instead of aborting the
report.

Example rendering:

```
Error: parse error
   ╭─[input:1:5]
   │
 1 │ if x
   │ ──┬┬┬
   │   ╰──── while parsing statement
   │    ││
   │    ╰─── while parsing expression
   │     │
   │     ╰── found 'newline', expected binary operator, comparison
   │         operator, boolean operator, postfix operation,
   │         'if', '<<', or ':'
───╯
```

The structured `ParseErrorInfo` preserves everything ariadne needs
(primary span, found token, categorised expected set, context spans),
so callers building their own diagnostic UI can render without going
through ariadne.

## Gotchas

Grammar constructors are generic over `I: ValueInput<'src, Token = Token, Span = Span>`.
This avoids naming the mapped token-stream input and recursive parser closure types at each
entry. Productions match typed tokens with `just` rather than parsing string keywords.

Boxed precedence productions replace nested concrete combinator types with a uniform `Boxed`
type. Re-entering a recursive expression parser then does not clone a concrete type containing
every intervening combinator layer. This limits representation-related stack costs; it does
not establish a fixed nesting limit or prove that arbitrary nesting cannot exhaust the stack.

Keep boxes at the established recursive/precedence boundaries. Without them, four levels of
nested calls (`f(f(f(f(1))))`) overflowed a 2 MiB test thread stack.
The grammar does not specify a portable maximum nesting depth.

## Testing

- **Unit tests** in `lexer.rs` and `parser.rs` cover individual grammar
  productions and the layout pass; `parser/module_tests.rs` covers the module
  syntax.
- **Lexer recovery** has three suites in `chl-parser/tests/lexer_recovery.rs`:
  - Each source with lexical errors under `chl-parser/tests/lexer_recovery/` has a `.tokens`
    golden holding its tokens, its lexical errors, the errors `parse_module` reports, and its
    statements' kinds. `CAMBRA_BLESS=1` rewrites the goldens.
  - Every `.cambra` file under the repository's `tests/` and `editors/` lexes with no error.
  - A seeded mutation fuzzer (`CAMBRA_FUZZ_SEED`, `CAMBRA_FUZZ_N`) checks the invariants under
    [Lexer recovery](#lexer-recovery) on mutated sources, and that `parse_module` reports the
    lexer's errors first.
- **Integration tests** in `tests/it/chl_parser_roundtrip.rs` parse
  representative CHL programs (joined comprehensions, defer/feed patterns,
  function definitions with `yield`, multi-line bracketed expressions, …) and
  assert the AST shape only at the level required to catch regressions.

Run with `cargo test -p chl-parser` for the unit tests and
`cargo test --test it chl_parser_roundtrip::` for the integration tests.

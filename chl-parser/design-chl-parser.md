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

`tokenize` runs Logos, validates tag adjacency with `check_tags`, then resolves layout.
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

Bracket depth suppresses physical newlines and indentation processing while nonzero. The
counter does not match opening and closing bracket kinds; the parser checks the required
closing token. A closer at depth zero gives `UnmatchedClose`; nonzero depth at EOF gives
`UnclosedBracket`.

The successful token stream ends with a `Newline` and enough `Dedent`s to close the stack.
Ordinary blocks balance `Indent` and `Dedent`; each pending assignment-side level contributes
one extra `Dedent`. Tests include `block_right_hand_side_opens_a_level_of_its_own`,
`a_wrapped_header_floors_the_level_at_the_statement`,
`the_chain_column_is_fixed_by_its_first_line` and
`a_match_right_hand_side_closes_its_level_unpinned`.

An unescaped physical newline before a string's closing quote gives `UnterminatedString`
at the opening quote. A backtick not immediately followed by an identifier gives
`DetachedBacktick` at the backtick. Both failures precede layout processing.

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
tokens, and `is` is an identifier. `/`, `%` and `~` fail tokenization.
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
  `T: K` or its bound `T <: U`.
- **A polymorphic type has its own variant.** `forall (T, U <: B) V requires …` parses to
  `Expr::Forall`, whose binder list holds only type parameters. The `)` closing the list ends the
  last kind, so the body follows with no separator.
- **A `requires` clause ends a signature.** `requires_clause` parses
  `requires Addable(A, B, Output=O), Transaction` into `Vec<Spanned<Requirement>>`, operands
  first and associated types by name after them. It follows a `def`'s `=>` result and a
  `forall`'s body. A clause after a nested `forall`'s body belongs to the innermost one.
- **Module statements have their own variants.** `Stmt::Import`, `Stmt::Run`,
  `Stmt::Param` and `Stmt::Discard` carry the statements of
  [docs/chl-spec.md](../docs/chl-spec.md), "9. Modules [Decided]". `Stmt::Pub`
  wraps the statement `pub` marks rather than being a field of each statement
  that can introduce a member, so one rule (`pub_refusal`) refuses `pub` on every
  statement that introduces none. It carries the keyword's span, because on a
  `@LoadFrom` declaration or a `@RenamedFrom` run `pub` stands on the line below
  the decorator, where the statement does not start. A renamed run is a
  `Stmt::Run` whose `renamed_from` names the predecessor's run, since the
  decorator changes only which run it pairs with.
- **A module path has two types.** `ast::ModulePath` is a path as written, each
  segment with its span. `module_path::ModulePath` is the path itself: interned
  segments, ordered by spelling, the identity loading keys modules by and the
  `SourceMap` records per file. `module_path::segment_error` holds the segment
  rule of [docs/chl-spec.md](../docs/chl-spec.md), "9.15 Module files", which
  the parser applies to a written path and loading applies to a root file's
  name.
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
  `a_user_function_named_like_a_builtin_is_ignored` in `tests/differential_interp.rs` pins the
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
- The spec's planned aggregates (`min`, `count`, `avg`, `len`) and tentative builtins (`str`,
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
failure or repair an unclosed bracket rejected by the lexer.

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

### Lexer-level: unclosed brackets at EOF

Bracket depth suppresses layout newlines until the bracketed region closes. At EOF with nonzero
depth, tokenization returns `LexError::UnclosedBracket`; parsing does not begin. Without that
check, a following physical line could have no token marking a statement boundary.
The layout mechanism is specified under [Stage 1](#stage-1--lexer-lexerrs).

### Recovery API

Both public parse functions return `ParseResult<T>`:

```rust
pub struct ParseResult<T> {
    pub value: Option<T>,
    pub errors: Vec<ParseError>,
}
```

`value` and `errors` are independent outputs. A lexical failure returns no AST and one error.
An unrecovered grammar failure can also return no AST. Recovery can return an AST containing
`Expr::Error` or `Stmt::Error`. A `validate` rule can instead report a custom error while
retaining an ordinary node; a nonempty error list does not imply that the AST contains a hole.

For example, `parse_expression(file, "1 +")` has no AST, whereas
`parse_expression(file, "1 -> 2 -> 3")`
retains a pair node and reports that the pair arrow does not chain.
`is_ok()` requires both a value and no errors. `into_result()` rejects any recorded error;
if both outputs are empty, it synthesizes a parse error at `0..0`.

### Threading partial ASTs through to lowering

`run_frontend` in `src/ccl/context.rs` accumulates parse errors before examining the AST.
If no module is available, it returns those errors. An empty module gets an empty-program
diagnostic. Otherwise it invokes `lower_stmts` even when parsing reported errors, allowing
independent lowering errors to appear in the same response.

Lowering maps recovered error nodes to `TypedExprNode::Error` without reporting the same
parse failure again. `LoweringResult` also carries an optional value and errors.
The frontend appends lowering errors and returns if no CCL value is available or if either
stage reported an error. Inference and later phases do not run on that result.
This guard applies to diagnostics from validation as well as explicit AST holes.

The returned `Vec<CompileError>` contains stage-tagged errors, not an assertion that all
possible errors were discovered. Regressions include `multiple_parse_errors_all_surface`
and `multiple_lowering_errors_all_surface` in `src/ccl/context.rs`.

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
- **Integration tests** in `tests/chl_parser_roundtrip.rs` parse
  representative CHL programs (joined comprehensions, defer/feed patterns,
  function definitions with `yield`, multi-line bracketed expressions, …) and
  assert the AST shape only at the level required to catch regressions.

Run with `cargo test -p chl-parser` for the unit tests and
`cargo test --test chl_parser_roundtrip` for the integration tests.

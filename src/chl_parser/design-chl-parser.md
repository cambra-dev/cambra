# CHL Parser Design

This document describes the design of the Cambra High-Level Language (CHL)
parser in `src/chl_parser/`.

Two properties shape it: **error recovery** — parsing continues past a local
syntax error and reports *all* problems in a file, for an interactive UX — and
an **AST shaped to match what lowering consumes**, so lowering does no
re-classification.

## Stack: logos + chumsky

| Need | Choice | Reason |
|---|---|---|
| Lexer | [`logos`](https://crates.io/crates/logos) `0.14` | DFA-based, extremely fast, declarative token attributes, well-maintained, the de-facto Rust lexer-generator |
| Parser | [`chumsky`](https://crates.io/crates/chumsky) `1.0.0-alpha.8` | Combinator-style grammar, **first-class error recovery via `recover_with`/`nested_delimiters`**, active development |

Chumsky 1.0-alpha was preferred over 0.9.x because the 0.9 line is
unmaintained and the 1.0 alpha API (despite some lifetime ergonomics warts —
see [Gotchas](#gotchas)) is what new chumsky users adopt.

## Architecture

```
CHL source  ── logos lexer ──▶  raw token stream
                              ──┐
                                ▼
                            layout post-pass
                              (off-side rule)
                              ──┐
                                ▼
                          NEWLINE / INDENT / DEDENT-aware
                          token stream
                              ──┐
                                ▼
                          chumsky parser
                              ──┐
                                ▼
                            CHL AST  ⇒  CCL lowering
```

The pipeline is two distinct stages, both inside `src/chl_parser/`:

### Stage 1 — Lexer (`lexer.rs`)

Logos tokenises the source into a flat `(Token, Span)` stream. Tokens cover
keywords, identifiers, integer and string literals (both `"…"` and `'…'`),
all CHL operators and punctuation, plus a physical `Newline` token.
Comments (`# …`) and inline whitespace (`' '`, `'\t'`) are skipped.

A layout post-pass then walks that stream and:

- tracks bracket depth (`(`, `[`, `{`) and **suppresses newlines inside
  brackets** (Python's implicit line continuation);
- at each new line, computes the byte-count of leading whitespace and
  compares it to an indent stack initialised to `[0]`;
- emits `Indent` / `Dedent` tokens to bracket each new indentation level,
  exactly as CPython does;
- skips blank lines and comment-only lines (they do not affect indentation);
- guarantees the stream ends with a `Newline` followed by enough `Dedent`s
  to return the stack to depth zero, so the parser sees a uniform shape.

`InconsistentIndent` is a hard error: dedenting to an indent level that
never appeared on the stack (e.g. `0 → 4 → 2`) is rejected at lex time.

### Stage 2 — Parser (`parser.rs`)

A chumsky combinator parser consumes the layout-resolved token stream and
produces the AST defined in [`ast.rs`](#stage-3--ast-astrs). Three
public entry points:

- `parse_module(&str)` — a sequence of top-level statements.
- `parse_expression(&str)` — a single expression (used by the lowering
  tests that build expressions in isolation).
- `ParseError` — a uniform error type wrapping either a `LexError` or a
  structured chumsky error (`ParseErrorInfo`) carrying its span, found token, and
  categorised expected set. The diagnostics types (`ParseError`, `ParseErrorInfo`,
  `ParseResult`, `CATEGORIES`) live in the `parser/error.rs` submodule, re-exported
  from `parser.rs`.

The grammar is precedence-climbed for binary operators. From lowest to
highest precedence:

1. `\x -> …` (lambda) / `yield`
2. `<<` (feed)
3. ternary `a if b else c`
4. `or`
5. `and`
6. `not`
7. chained comparison (`==` `!=` `<` `<=` `>` `>=`)
8. `|`
9. `^`
10. `&`
11. `++`
12. `+`, `-`
13. `*`, `//`
14. unary `-`
15. postfix: call `f(…)`, subscript `x[…]`, attribute `x.name` / `x.0`
16. atom: literal, name, parenthesised, list, dict/record, comprehension

Notably absent vs. Python: `/` (true division), `%` (modulo), `**`
(power), `>>` (right shift), `~` (bitwise not), `is`, `in`, `not in`,
`is not`. The lowering pass has never supported these, and the parser
refuses them at the syntactic level rather than parsing-then-erroring.

### Stage 3 — AST (`ast.rs`)

Key shape choices:

- **Every node carries a span** via `Spanned<T>`, so diagnostics for any
  sub-expression have precise location info.
- **Operators are typed enums.** `BinOp`, `CmpOp`, `BoolOp`, `UnaryOp`,
  `AugOp` enumerate exactly what CHL accepts. Lowering can match
  exhaustively without an "unsupported operator" arm per variant.
- **`if`/`elif` chains flatten.** `Stmt::If` carries a `Vec<IfBranch>` (one
  per `if`/`elif`) plus an optional `else_body`, rather than nesting an
  `If` inside an `Else`. This matches the `Case` shape in CCL.
- **Records are parens; braces are types.** A record *value* `(x=1)` parses
  as `Expr::Record`; brace literals are type syntax — `{x: T}` is
  `Expr::BraceRecord`, `{T, U}` is `Expr::BraceGroup`, `{"name": v}` is
  `Expr::Dict`. Lowering reads the brace forms as types and rejects them as
  values. Because braces are always a *product* in type position and never
  grouping, the brace parser captures the trailing comma rather than merely
  allowing it: `{T,}` is the one-element product and a comma-free `{T}` is a
  parse error, while the empty `{}` is the **unit type**, which lowering reads as
  `Unit` (see [docs/chl-spec.md](../../docs/chl-spec.md),
  "6.6 The empty product is unit"). A `where` clause after a single colon-free
  base turns the brace into a refinement type `{T where p}` (`Expr::BraceRefinement`,
  [docs/chl-spec.md](../../docs/chl-spec.md), "6.4 Refinement syntax"); the
  clause gates off the one-element `{T}` diagnostic, and its predicate `p` — an
  ordinary expression whose subject `_` lowering maps to the refinement binder —
  is parsed with the same `expr` as everything else.
- **Feed / Define have their own variants.** `Expr::Feed` and `Stmt::Define`
  capture `<<` and `<<=` directly, rather than appearing as `BinOp(LShift)`
  and `AugAssign(LShift)` that lowering must special-case.

## Error recovery

There are two complementary recovery layers, both implemented with
chumsky's `recover_with(via_parser(…))`:

### Bracket-level recovery

`recover_with(via_parser(nested_delimiters('(', ')', […], |span| Expr::Error)))`,
plus the symmetric ones for `[…]` and `{…}`. If parsing fails inside a balanced
bracketed region, the parser jumps to the matching close-delimiter and
inserts an `Expr::Error` placeholder. This means `x = (1 +) + 2` reports
the inner error and still parses the whole assignment.

### Statement-level recovery

`recover_with(via_parser(skip_to_newline.then(skip_indented_block)))` —
when an entire statement fails to parse:

1. Consume tokens up to (and including) the next `Newline` at the current
   bracket depth.
2. If the next token is `Indent`, also swallow the balanced
   `Indent…Dedent` block. This is what stops a bad header line
   (`def 1(x):`) from leaving its attached body as orphan tokens for the
   outer module parser to choke on.

The recovered statement is a `Stmt::Error` placeholder; the original
chumsky error is preserved in the returned error list. Recovery doesn't
hide diagnostics — it just lets parsing continue past them so multiple
errors come out in one pass.

**Load-bearing detail:** the `skip_to_newline` parser uses
`.at_least(1)`. Without that, recovery would succeed by matching zero
tokens at positions like `Dedent`/EOF, which would loop the enclosing
`statement().repeated()` forever (chumsky panics with a "Collect making no
progress" diagnostic). With `.at_least(1)`, recovery cleanly declines at
those positions and the outer `repeated()` terminates normally.

**Load-bearing detail #2:** every precedence layer inside `expression()`
(`product`, `sum`, `collection_union`, `bitand`, `bitxor`, `bitor`, `bool_not`,
`bool_and`, `bool_or`, `ternary`, `feed`, plus `atom`, `postfix`, `unary`)
ends in `.boxed()`. Without that, the 15-layer precedence chain
monomorphises into nested generic combinator types, and each `expr.clone()`
re-entry walks all 15 layers' frames on the stack. Just 4 levels of nested
function calls (`f(f(f(f(1))))`) was enough to overflow a 2 MiB test
thread stack. Boxing collapses the type at each layer to a uniform
`Boxed<…>` with predictable, small frame size, restoring well-bounded
stack usage for nested expressions.

### Lexer-level: unclosed brackets at EOF

A subtle interaction: the layout pass suppresses `Newline` tokens while
inside `(`, `[`, or `{` (Python's implicit line continuation). If a
bracket is never closed, the lexer would silently swallow every following
newline, leaving the parser with a flat token stream and no way to find
statement boundaries. The lexer therefore returns
`LexError::UnclosedBracket` if EOF is reached with bracket depth > 0, so
the failure is reported at the source of the problem rather than
manifesting as a confusing far-from-cause parse error.

### Recovery API

`parse_module` and `parse_expression` both return a `ParseResult<T>` struct
carrying *both* the (possibly partial) AST and the list of errors:

```rust
pub struct ParseResult<T> {
    pub value: Option<T>,        // partial AST with Error holes, or None
    pub errors: Vec<ParseError>, // possibly multiple, from recovery
}
```

This is what makes recovery useful: a caller that just wants Result-style
"all or nothing" can use `result.into_result()`, while a caller that
wants to surface diagnostics on a partial parse can use both fields
directly.

### Threading partial ASTs through to lowering

[`compile_program`](../ccl/context.rs) now runs the **lowering** stage even
when the parser reported errors, so users see parse + lowering diagnostics
in one pass instead of having to fix parse errors before any lowering
problem becomes visible.

The handshake is:

- `parse_module` returns a `ParseResult` that may carry an `Expr::Error` /
  `Stmt::Error` placeholder for each region that hit recovery.
- [`crate::ccl::lower`] silently maps those placeholders to the analogous
  `TypedExprNode::Error` in CCL (no second error is reported for a parse
  hole — it's already in the user's diagnostic list).
- `lower_stmts` itself returns a `LoweringResult { value, errors }` shaped
  like `ParseResult`. Statement-level recovery means an unsupported
  construct in one top-level statement doesn't shadow lowering errors in
  other statements.
- [`compile_program`] returns `Result<_, Vec<CompileError>>`. Each
  `CompileError` is single-stage (`Parse(ParseError)`, `Lower(LoweringError)`,
  …); the `Vec` is the union of every error collected before bailing.
- Inference and downstream stages **do not run** if any parse or lowering
  error was recorded, because the CCL tree may contain `Error`
  placeholders. Every pass past lowering panics via
  `unexpected_error_node!()` if it ever encounters one, which makes a
  forgotten-guard regression loud rather than producing silent corruption.

### Error message quality

Four layers, each independent and each pulling its weight:

**1. `Display` for `Token` and `Span`.** Defined in `lexer.rs` and `ast.rs`.
`Token::LParen` displays as `(`, `Token::EqEq` as `==`,
`Token::Int(_)` as `integer literal`, etc. So errors say
`found '('` instead of `found 'LParen'`, with no other parser changes.

**2. Targeted `.labelled(…)` annotations.** A handful of high-leverage
productions carry labels so failure-at-start cases collapse to a single
named expectation:

| Production | Label | Where it helps |
|---|---|---|
| `atom` (literal / name / `(…)` / list / dict) | `expression` | "expected expression" instead of 5 alternatives |
| `ident_only` in expression context | `identifier` | postfix `.name`, lambda params |
| `select! { Ident }` in `def_stmt` name slot | `function name` | `def 1(x):` says "expected function name" |
| `select! { Ident }` in `def_stmt` param slot | `parameter name` | `def f(1):` says "expected parameter name" |
| top-level `expression` choice | `expression` + `.as_context()` | "while parsing expression" secondary span |
| `block` opener (`Newline Indent`) | `indented block` | missing block after `if x:` |
| top-level `statement` choice | `statement` + `.as_context()` | "while parsing statement" secondary span |

`.labelled(...)` only replaces the expected set when the labeled parser
fails *at its start position*. `.as_context()` is the complementary
behaviour: when the labeled parser fails *mid-parse* (after consuming
input), the label is recorded as context with the partially-matched
span, so ariadne renders it as a secondary underline like
`while parsing expression` pointing back at the in-progress text.

**3. Category collapsing in `collect_errors`.** Errors that survive label
processing can still list 20+ tokens as valid continuations (e.g. every
binary operator after `if x` where a `:` was expected). The
`CATEGORIES` table in `parser/error.rs` defines disjoint operator buckets
(`binary operator`, `comparison operator`, `boolean operator`,
`postfix operation`, `augmented-assignment operator`). When the
"expected" set contains *every* member of a category, those members are
removed and one category entry takes their place. So
`if x\n` reports

```
expected binary operator, comparison operator, boolean operator,
         postfix operation, 'if', '<<', or ':'
```

(seven items) instead of the 22-token list.

**4. Rule-raised messages.** The three layers above all shape a *derived*
expectation — "found X, expected Y" — which only says something when the
failure was a token that didn't match. A rule that parses a well-formed token
sequence and then rejects what it means has nothing to derive from: `{Int}` is
a perfectly good brace group that is not a valid type. Those rules raise their
own message with `Rich::custom` from a `validate`, it rides
`ParseErrorInfo::custom`, and it *replaces* the derived text at both rendering
sites. The field is load-bearing rather than cosmetic: `found`/`expected` are both
empty for a custom error, so without it the whole diagnostic degrades to a bare
`found end of input`.

### Rendering with `ariadne`

`ParseResult<T>` exposes two output methods:

- `.render_errors(src_name, src) -> String` — ariadne output with colour disabled
  (for tests, log files, snapshot rendering).
- `.eprint_errors(src_name, src)` — colour output to stderr (for interactive
  use).

Both build one `Report` per `ParseError`, with a red primary label at
the failure span and one yellow secondary label per `.as_context()`
entry. Lex errors get a single-label report.

Every label span goes through `label_range`, which clamps `end` up to `start`.
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

Two non-obvious chumsky 1.0-alpha lifetime pitfalls — both surface as the
unhelpful `'src must outlive 'static` error — were hit during development:

1. **Recursive parsers force `'static` by default.** `recursive(|expr| …)`
   needs the closure parameter typed explicitly *only* if the surrounding
   function uses a concrete input type. The fix used in this module is to
   make every parser function generic over `I: ValueInput<'src, Token =
   Token, Span = Span>`, which lets chumsky's inference figure out the
   recursive type without an explicit `Recursive<dyn Parser<…> + 'src>`
   annotation. This mirrors the pattern in chumsky's own `nano_rust`
   example.

2. **`text::ascii::keyword(…)` won't compose with a recursive parser.** Its
   `Str` parameter forces a `'static` bound. CHL's parser uses
   `just(Token::Foo)` against the typed token stream, sidestepping the
   issue.

## Testing

- **Unit tests** in `lexer.rs` and `parser.rs` cover individual grammar
  productions and the layout pass.
- **Integration tests** in `tests/chl_parser_roundtrip.rs` parse
  representative CHL programs (joined comprehensions, defer/feed patterns,
  function definitions with `yield`, multi-line bracketed expressions, …) and
  assert the AST shape only at the level required to catch regressions.

Run with `cargo test chl_parser` for the unit tests and
`cargo test --test chl_parser_roundtrip` for the integration tests.

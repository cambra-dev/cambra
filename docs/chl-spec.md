# CHL Language Specification (Draft)

This is the working specification of the **Cambra High-Level Language
(CHL)** — the surface language a Cambra programmer writes. The
specification describes CHL directly: what each construct *denotes*
(the value it computes) and, where applicable, what *effects* its
evaluation has on the program's deferred outputs.

Compilation lowers CHL to the Cambra Core Language (CCL), where the
program is type-checked and run as producer/consumer dataflow. This
document mentions the lowering only when it makes a behavioural rule
easier to understand or pins down a corner case; the lowering itself
is specified in [src/ccl/design/lowering.md](../src/ccl/design/lowering.md)
and the operational semantics in [docs/operational-semantics/](operational-semantics/).

CHL today **looks** like Python, but it is not Python. Several Python
tokens are re-purposed (`<<`, `<<=`, `&`, `|`, `^`), one is new (`++`),
and Python features that don't fit the dataflow model (mutable identity,
exceptions, classes, true division, etc.) are absent. Where CHL diverges
from Python, this document states the divergence explicitly.

The Python resemblance itself is transitional: CHL is **converging away
from Python-compatible surface syntax** toward its own syntax, designed
around two constraints — keep term and type syntax cleanly separated,
and keep data/control flow statically visible. The direction is recorded
in [brainstorm/2026-06-29-syntax-convergence.md](brainstorm/2026-06-29-syntax-convergence.md)
and embodied by the north-star programs in
[`tests/programs/`](../tests/programs/) (`reachability`, `fanout`,
`txn_kv`), which are written in the *target* syntax and pinned as
compile-errors until the language catches up. This spec folds those
decisions in as **Direction** notes on the affected sections.

**Cambra has no undefined behaviour.** This is a foundational
principle, not a pending decision: no construct, present or future,
gives an implementation license to do anything it likes. Where this
document says an expression "is not defined", it marks semantics that
are *not yet decided* (see *Partiality*, §3) — a gap that will be
closed by a real decision (a runtime trap, divergence, static
exclusion via refinement types, …), never by C-style UB. Every program
the compiler accepts has a defined meaning.

## How to read this document (status markers)

The unmarked body text of each section describes **what the compiler
implements today** and should hold when you run the current toolchain.
Everything else carries one of these markers:

- **[Planned]** — the parser already recognises the construct (or the
  current design admits it) but lowering rejects it today; near-term
  roadmap work, tracked in [docs/plan.md](plan.md).
- **[Decided]** — a design decision that has been made and recorded (the
  marker or its context cites where) but **not implemented**. Decided ≠
  immutable: until code and tests pin it down, a decision can and should
  be revisited if implementing it surfaces a problem. Follow the
  citation for the rationale before either relying on it or overturning
  it.
- **[Tentative]** — a working sketch: it appears in a brainstorm or a
  north-star example, but the details have not been worked through to a
  decision. Expect it to change. Do **not** treat tentative material as
  a constraint on new design work — it is an input to it.
- **[Open]** — a known question with no answer yet.

If you are writing CHL that must compile, read only the unmarked text.
If you are evolving the language, the markers tell you how much weight
each statement bears — and where pushing back is cheap (anything short
of implemented) versus expensive (implemented behaviour with tests
pinning it).

---

## 1. Lexical structure

### 1.1 Source encoding

CHL source is UTF-8 text. Spans are byte offsets into that source.

### 1.2 Whitespace, comments, line structure

- **Inline whitespace** (`' '`, `'\t'`) separates tokens and is otherwise
  insignificant.
- **Comments** start with `#` and extend to the end of the line.
- **Physical newlines** terminate *logical* lines, except when suppressed
  by an unclosed bracket (see Implicit line continuation, below).
- **Blank lines and comment-only lines** do not affect indentation.

### 1.3 Indentation (off-side rule)

CHL uses Python-style significant indentation. At the start of each
logical line, the byte count of leading whitespace is compared to an
indent stack initialised to `[0]`:

- *greater than top* → push, emit `INDENT`
- *less than top* → pop until equal, emitting one `DEDENT` per pop;
  failure to find an equal level is a **hard `InconsistentIndent` error**
- *equal to top* → no layout token

At EOF, the stack is unwound to `[0]` and a synthetic final `NEWLINE`
plus the requisite `DEDENT`s are emitted, so every `INDENT` is paired.

### 1.4 Implicit line continuation

Inside `(...)`, `[...]`, or `{...}` (any depth, any combination), newlines
and indentation are **ignored**. Multi-line list, tuple, dict, record,
and call expressions are written naturally:

```python
xs = [
    1,
    2,
    3,
]
```

An unclosed bracket at EOF is a hard lexical error (`UnclosedBracket`).
There is no explicit line-continuation backslash.

### 1.5 Identifiers

```
ident ::= [A-Za-z_] [A-Za-z0-9_]*
```

Identifiers are case-sensitive. Identifiers that match a keyword are
lexed as keywords (keyword regexes win ties against the identifier
regex).

### 1.6 Keywords

```
True   False  None
and    or     not
if     elif   else
for    in
def    lambda return yield
pass
```

`while`, `class`, `import`, `try`, `except`, `with`, `as`, `global`,
`nonlocal`, `del`, `assert`, `raise`, `is` are **not** keywords in CHL
today. Some are reserved for future use.

> **Direction.** The convergence syntax adds binder/keyword vocabulary
> that is not lexed today: `rec` (recursive binding — §4.3, **[Decided]**),
> `with`, `given`, `requires`, `summon` (transactions / contextual
> parameters — §8, **[Decided]**), and `match` / `case` (pattern
> matching, **[Tentative]** — it appears in the north-star `txn_kv`
> program but has no design writeup). Avoid taking these names for other
> purposes.

### 1.7 Literals

| Form | Token | Notes |
|---|---|---|
| `0`, `42`, `1234` | `Int(i64)` | Decimal only; no `_` separators, no hex/bin/oct, no negation in the token (`-3` is `UnaryOp(Neg, 3)`). |
| `"hello\n"`, `'world'` | `String` | Double- or single-quoted. Escapes: `\n \t \r \\ \" \' \0`. Unknown escapes are preserved verbatim (the `\` is kept). No multi-line `"""..."""`, no f-strings, no raw `r"..."`. |
| `True`, `False` | `Bool` | |
| `None` | `Unit` | CHL's unit value. (Direction: unit becomes `()`, and lowercase `none` is the `Option` constructor — see §3.1.) |

There are no floating-point literals — CHL has no `f64` type at the
surface level.

### 1.8 Operators and punctuation

```
+  -  *  //  ++
&  |  ^
== != <  <= >  >=
=  += -= *= //=
<<  <<=
(  )  [  ]  {  }  ,  :  .  ;
```

**Notably absent vs. Python** at the lexical level: `/`, `%`, `**`, `>>`,
`~`, `@` (no matmul, no decorators), `:=`, walrus expressions, `...`.
The parser refuses these at the syntactic level rather than
parsing-then-erroring.

`++` is not a Python token at all: it is CHL's collection-union operator
(§3.3). There is no increment operator — `++` is always binary.

> **Direction.** The convergence syntax adds tokens that are not lexed
> today **[Decided]**: `λ` and `→` for lambdas, with ASCII fallbacks `\`
> and `->` (§3.10), and `:=` for mutation (§4.3). Note that the future
> `:=` is *not* Python's walrus operator — it is the Algol-tradition
> assignment statement, and there is still no assignment-as-expression.

### 1.9 Semicolons

`;` is a statement separator on a single line: `x = 1; y = 2` is two
statements. A trailing `;` before a newline is allowed. Multiple
statements per line are legal but conventionally discouraged.

---

## 2. Grammar

The grammar is given in EBNF over the token stream produced by §1.
`NEWLINE`, `INDENT`, and `DEDENT` are layout tokens synthesised by the
lexer (§1.3).

### 2.1 Top-level block

```ebnf
top_block  ::= ( statement )* EOF
```

A source file is one **top-level block**: a sequence of statements
sharing a single lexical scope. There is deliberately no "module"
concept in this spec — CHL has no imports or namespaces (§12), and
semantically the top level behaves exactly like any nested block
(§4). (The parser's root AST node is still named `Module`, after
Python's `ast.Module`; the name is historical.)

### 2.2 Statements

```ebnf
statement       ::= simple_stmt NEWLINE
                 |  compound_stmt

simple_stmt     ::= return_stmt
                 |  pass_stmt
                 |  assign_stmt
                 |  ann_assign_stmt
                 |  aug_assign_stmt
                 |  define_stmt
                 |  expr_stmt

return_stmt     ::= "return" [ expression ]
pass_stmt       ::= "pass"

assign_stmt     ::= assign_target "=" expression
ann_assign_stmt ::= assign_target ":" expression "=" expression
aug_assign_stmt ::= assign_target aug_op expression
define_stmt     ::= assign_target "<<=" expression
expr_stmt       ::= expression

aug_op          ::= "+=" | "-=" | "*=" | "//="

assign_target   ::= ident
                 |  "(" assign_target ( "," assign_target )* [ "," ] ")"
                 |  assign_target ( "," assign_target )+ [ "," ]

compound_stmt   ::= if_stmt | for_stmt | def_stmt

if_stmt         ::= "if" expression ":" block
                    ( "elif" expression ":" block )*
                    [ "else" ":" block ]

for_stmt        ::= "for" assign_target "in" expression ":" block

def_stmt        ::= "def" ident "(" [ param ( "," param )* [ "," ] ] ")" ":" block
param           ::= ident [ ":" expression ]

block           ::= NEWLINE INDENT statement+ DEDENT
```

`assign_target` is a bare name or a nested tuple of names — **no
subscript or attribute targets** (`xs[0] = x` and `obj.f = x` are not
valid). Every binding LHS is therefore a static pattern: which names a
statement introduces is decidable from the syntax alone, without any
runtime evaluation.

> **Direction.** The convergence syntax adds statement forms that are
> not in today's grammar: `x := e` mutation statements (**[Decided]**,
> §4.3), `rec x = e` recursive bindings (**[Decided]**, §4.3),
> annotation-only forward declarations such as `h: Feed(_)` with no
> initialiser (**[Decided]**, §3.7 — today an annotation *requires* a
> value), and out-of-line collection definition through a subscript
> target, `c[i] = v` (**[Tentative]**, §6.3 — this would relax the
> no-subscript-target rule above).

### 2.3 Expression precedence

From lowest to highest; all binary operators are left-associative unless
noted:

| Level | Operator(s) | Notes |
|---:|---|---|
| 1 | `lambda`, `yield` | prefix forms; non-associative |
| 2 | `<<` | feed operator (right-associative is not meaningful — see §3.7) |
| 3 | `e₁ if cond else e₂` | ternary; *right*-associative |
| 4 | `or` | short-circuit; n-ary flattening |
| 5 | `and` | short-circuit; n-ary flattening |
| 6 | `not` | prefix |
| 7 | `==` `!=` `<` `<=` `>` `>=` | chained, *not* left-fold (see §3.4) |
| 8 | `\|` | logical or |
| 9 | `^` | logical xor |
| 10 | `&` | logical and |
| 11 | `++` | collection union |
| 12 | `+` `-` | additive |
| 13 | `*` `//` | multiplicative |
| 14 | unary `-` | prefix |
| 15 | postfix: `f(args)`, `x[i]`, `x.attr` | left-fold |
| 16 | atom | literal, name, `(...)`, `[...]`, `{...}`, comprehension |

```ebnf
expression ::= lambda_expr | yield_expr | feed_expr
             | ternary | bool_or | bool_and | bool_not
             | comparison | log_or | log_xor | log_and | collection_union
             | sum_expr | product | unary | postfix | atom
```

### 2.4 Atoms

```ebnf
atom ::= literal
       | ident
       | "(" expression ")"                  -- parenthesised
       | "(" ")"                              -- empty tuple (target: the unit value, §3.1; [Open] whether it equals None today)
       | "(" expression "," ")"              -- one-tuple
       | "(" expression ( "," expression )+ [ "," ] ")"   -- tuple
       | "[" [ expression ( "," expression )* [ "," ] ] "]"   -- list
       | "[" expression comp_for ( comp_for | comp_if )* "]"  -- collection comprehension
       | "(" expression comp_for ( comp_for | comp_if )* ")"  -- collection comprehension (paren form)
       | "{" [ record_field ( "," record_field )* [ "," ] ] "}"   -- record (bare-identifier keys)
       | "{" dict_entry ( "," dict_entry )* [ "," ] "}"           -- dict (expression keys)

record_field ::= ident ":" expression
dict_entry   ::= expression ":" expression
comp_for     ::= "for" assign_target "in" expression
comp_if      ::= "if" expression
```

A `{...}` literal is classified by its keys: if **every** key is a bare
identifier it is a **record** (`{x: 1, y: 2}`); otherwise (string keys,
computed keys) it is a **dict** (`{"name": "alice"}`). `{}` is the empty
record. Dicts currently parse but are rejected at lowering.

`(e)` (no trailing comma) is parenthesised `e`, **not** a one-tuple. A
one-tuple is written `(e,)`.

> **Direction — term-level delimiters [Decided].** The convergence
> syntax splits the three delimiters by role
> ([2026-06-29 §1](brainstorm/2026-06-29-syntax-convergence.md)):
>
> | Delimiter | Role | Examples |
> | --- | --- | --- |
> | `( … )` | product **terms** | tuple `(1, 2, 3)`, record `(f1=1, f2=2)` |
> | `[ … ]` | **collections** — definition *and* lookup | list `[1, 2, 3]`, map `[k=v, …]`, indexing `counts[word]`, `xs[0]` |
> | `{ … }` | structural **types** | tuple type `{T, U}`, record type `{f: T}`, refinement `{x: T \| p(x)}` |
>
> Under that scheme `{…}` never appears at the term level: today's
> `{name: e}` records become `(name=e, …)`, and dicts become map
> literals `[k=v, …]`. (An earlier sketch had dicts moving to
> `[k: v, …]`; that is superseded — `:` is settling on annotation/type
> duty, `=` on definition.) Still **[Open]**: the spelling of an
> *empty* map under the new scheme. The record-syntax /
> call-argument interaction is resolved by the
> functions-take-one-product-argument direction (§3.8): `f(x=1)` *is*
> `f` applied to a record — keyword arguments and record arguments are
> the same thing.

---

## 3. Expression semantics

Each CHL expression denotes a value, and in two cases also performs an
**effect** when evaluated:

- **Feed `<<`** (§3.7) writes its right-hand-side into a deferred
  collection.
- **`yield`** (§3.13) writes its operand into the deferred collection
  that the enclosing generator function will return.

Every other expression form is *pure*: it depends only on its inputs,
has no observable side effects, and is safe to evaluate zero, one, or
many times. Mutation at the source level is a property of *statements*
(loop-carried reassignment in a `for` body — §4.6) rather than of
expressions.

> **Direction.** This two-effect inventory is a property of *today's*
> language, not a permanent invariant. Under the mutability direction
> (**[Decided]** — §4.3, §6.2, §8) a function can take `Mut(…)`
> parameters or mutate transactional state
> (`def put(…) requires Transaction: store[key] := value` in the
> north-star `txn_kv`), so a *call* to such a function is itself an
> effecting expression — and "safe to evaluate zero, one, or many
> times" no longer follows from the expression's form alone. How the
> temporal-mutation model reconciles those effects with the
> unordered, data-dependency-only evaluation story below (time-domain
> ordering, transactions over write-regions) is worked through in
> [2026-04-06-mutability.md](brainstorm/2026-04-06-mutability.md) and
> [2026-06-29 §6](brainstorm/2026-06-29-syntax-convergence.md); this
> section will need a rewrite when that lands.

### Collections are unordered

A pervasive property of CHL semantics is that **collections are
unordered**. A list literal, a comprehension result, a generator's
yields, a feed stream — all denote *bags* (finite multisets) of
elements. Two collections with the same elements (with the same
multiplicities) are indistinguishable.

The consequence at the operational level: a `for` loop's iterations
may run in **any order, including in parallel**. A program has no way
to rely on iteration order — the denotation is the same bag whichever
order the implementation picks.

Regardless of ordering, collections are all indexed by some type.
This type is generally not visible to users, but can be used to impose
ordering or to match up data between coupled source/sink pairs like
`http_serve`.

The single way to introduce inter-iteration ordering is a
**loop-carried accumulator** (§4.6): rebinding an outer-scope name
inside a `for` body creates a data dependency from one iteration to
the next, forcing those iterations to run sequentially in the order
the dependency requires. No other construct sequences iterations.

Lists do retain an integer-indexed *addressing* structure (a list is
a finite function from `[0, n)` to values, so `xs[i]` is well-defined
— §3.9); but the order of *iteration* over a list is not the order of
its indices, and a comprehension over `xs` does not promise any order
on its output.

> **Direction [Tentative].** The target model is more nuanced than
> "all collections are bags". In the collections model (§6.3), `List`
> and `Array` are *ordered* — their positional structure is part of
> the value, not just an addressing convention — while `Set`, `Map`,
> and `Collection` are unordered. Order-dependent operations over the
> unordered types are expected too, with the ordering supplied
> explicitly as a **given** instance (the contextual-parameter
> mechanism of §8) rather than baked into the type. This nuance is
> recorded here only (2026-07-07, no brainstorm writeup yet); today's
> compiler treats every collection as a bag, exactly as this section
> describes.

### Evaluation order is unspecified

CHL expressions are *pure* (today's language — see the Direction note
above): the only side-effecting expression forms are `<<` and `yield`,
and both of those contribute to bag-valued deferred collections — bag
contributions commute. Consequently, the order in which
sub-expressions of a compound expression evaluate is **not specified**
by this document. Argument evaluation order in a
call, operand order in a binary operator, the relative order of two
independent feeds in the same loop body — none of these are
sequenced.

The only constraints on execution order are **data dependencies**:
if expression `A` produces a value that expression `B` consumes,
the implementation must evaluate `A` before `B`. The mechanisms that
introduce such dependencies are:

- ordinary name binding (after `x = e`, any use of `x` — say `f(x)` —
  consumes the value of `e`, so `e` evaluates before that use),
- loop-carried accumulators (§4.6), which sequence iterations of a
  `for` loop along the accumulator's update chain,
- short-circuit `and` / `or` (§3.5) and ternary `if`/`else` (§3.6),
  which select which sub-expressions contribute to the result,
- sink contracts (e.g. `http_serve`'s response-paired-with-request
  rule — §7.4), which fix ordering at the boundary between the
  program and the outside world.

A consequence worth highlighting: a program may not rely on the
order in which two independent feed expressions execute, even if
they appear on consecutive source lines.

### Partiality is not yet defined [Open]

Some expressions are *partial*: an out-of-range list index, a missing
dict key, division by zero, integer overflow. Where this document says
such an expression "is not defined", it stops there deliberately: CHL
has **no defined divergence semantics yet**. Whether a partial
expression traps at runtime, diverges, is statically excluded by
refinement types (§6), or something else, is **[Open]** — do not read
a runtime-trap model into this spec; it is an undecided question, not
an implicit decision.

One resolution is ruled out in advance: C-style undefined behaviour —
**Cambra has no UB**, a foundational principle stated at the top of
this document. The gap here is also distinct from the *deliberate*
nondeterminism elsewhere in §3: unordered collections and unspecified
evaluation order are decided semantics (order simply is not
observable), not gaps.

What the semantic rules in this document *do* rely on is only the
notion of definedness itself: short-circuit `and`/`or` (§3.5), the
ternary (§3.6), and `if`/`elif` (§4.5) guarantee that a non-selected
operand being undefined does not make the selecting construct
undefined. Those guarantees hold under any resolution of the question
above. (The Option-returning-lookup direction in §3.9 is one way part
of the partiality disappears entirely.)

### 3.1 Literals

`Int`, `String`, `Bool`, `None` denote themselves. `None` is CHL's unit
value: a single inhabitant of the unit type. (In the lowering, `None`
becomes the CCL `Unit` literal.)

> **Direction.** `None` is a Python spelling that collides with the
> decided term/type capitalization rule (**[Decided]**, §6.1: lowercase
> heads are terms; `Caps` means *type*, without exception). In the
> target syntax the unit **value** is the empty product `()`, and
> `none` (lowercase — a data constructor, hence a term) is *not* unit:
> it is the empty case of `Option(_)`, paired with `some(v)` (§3.9).
> At the type level, the empty structural product `{}` plays the
> unit-type role (as in `Set(K) = Map(K, {})`, §6.3). `True`/`False`
> sit under the same capitalization anomaly — presumably they become
> `true`/`false`, matching the CCL symbolic rendering, but that
> spelling is **[Open]**. The `()`-is-unit and `none`-is-`Option`
> points are recorded here only (2026-07-07, no brainstorm writeup
> yet).

### 3.2 Names

A name refers to the value bound by the nearest enclosing scope
(parameter, lambda parameter, assignment, or function definition).
Name resolution is purely static — there is no dynamic lookup, no
introspection of the binding environment.

Forward references are not allowed: a name must be in scope at the
point of use. Mutual recursion between top-level functions is
**[Planned]** — see
[docs/brainstorm/2026-03-05-recursion.md](brainstorm/2026-03-05-recursion.md).

### 3.3 Arithmetic and logical operators

| Operator | Semantics |
|---|---|
| `a + b`, `a - b`, `a * b` | Integer arithmetic. Overflow is not defined (see *Partiality*, §3). |
| `a // b` | Integer floor division. Division by zero is not defined (see *Partiality*, §3). |
| `-a` | Integer negation. |
| `a & b`, `a \| b`, `a ^ b` | **Logical** and / or / xor. Both sides must be `Bool`. (CHL re-uses Python's bitwise tokens for logical operators; there is no separate bitwise operator family.) |
| `not a` | Boolean negation. |
| `a and b`, `a or b` | Boolean conjunction / disjunction with short-circuit semantics — the right operand need not be defined when the left settles the result. See §3.5. |
| `a ++ b` | Collection union (multiset sum) of two collections of the same element type. Since collections are unordered (§3), this is not "concatenation"; it is the bag union. |

Operators absent on purpose: `/` (no fractional type), `%`, `**`, `>>`,
`~`, `@`. Attempting to use these in source is a parse error.

### 3.4 Comparisons

Comparisons chain Python-style: `a < b < c` denotes `a < b and b < c`.
General form: `a op₀ b op₁ c op₂ d` denotes
`a op₀ b and b op₁ c and c op₂ d` — a conjunction of adjacent pairwise
comparisons, not a left-fold.

Supported comparators: `==`, `!=`, `<`, `<=`, `>`, `>=`. `is`, `is not`,
`in`, `not in` are **not** supported (no identity, no membership
operator). Membership over a collection is written as a comprehension
with a guard or as an aggregate.

Comparing values of incompatible types is a compile-time type error,
not a runtime error.

> **Direction [Decided].** The convergence syntax adds membership
> *expressions*: `e in s` tests set membership, `k in m` tests for a key
> in a map ([2026-06-29 §2](brainstorm/2026-06-29-syntax-convergence.md)).
> `in` as the iteration keyword (`for x in xs`) is unchanged; the
> expression form is what's new.

### 3.5 Short-circuit `not`, `and`, `or`

`not e` is unary boolean negation.

`and` and `or` are short-circuiting n-ary boolean operators:

- `and(a₀, a₁, …, aₙ₋₁)` is `True` iff every `aᵢ` is `True`.
- `or(a₀, a₁, …, aₙ₋₁)` is `True` iff some `aᵢ` is `True`.

The short-circuit property is **semantic**, not an operational
constraint: the result is determined as soon as some prefix of the
operands settles the answer, so the remaining operands need not be
defined for the whole expression to be defined. For example,
`xs == [] or xs[0] > 0` is well-defined when `xs` is empty even
though `xs[0]` is not defined there (see *Partiality*, §3); the `or`
result is fixed by the first operand and the second is never
required.

CHL `and`/`or` always return `Bool`. There is no "return the truthy
operand" coercion (Python's `a or default` idiom). All operands of
`and` / `or` must be `Bool`-typed.

### 3.6 Ternary

```
then_expr if cond else else_expr
```

The result is `then_expr` when `cond` is `True`, and `else_expr`
when `cond` is `False`. Like short-circuit `and`/`or` (§3.5), this
is a semantic property: the non-taken branch contributes nothing to
the result, so it need not be defined (it could index an empty list,
look up a missing key, etc. — see *Partiality*, §3) without making
the ternary itself ill-defined. If the non-taken branch contains a feed
or yield, that effect does not occur.

Right-associative: `x if a else y if b else z` parses as
`x if a else (y if b else z)`.

### 3.7 Feed operator `<<`

```
target << value
```

`<<` is the one expression-level **effect** in CHL. Evaluating
`target << value` appends `value` to the stream that `target`
denotes. The expression itself returns the unit value `None`; its
purpose is the append.

`target` must be a **deferred collection**: a value created by
`defer()`, by an `<<=` define-statement (§4.4), or by a sink-producing
builtin such as `http_serve` (§7.4). Feeding a non-deferred value is a
compile-time error.

Feeds against a given target are visible to anything that consumes
that target: a downstream comprehension iterating the stream, a sink
that dispatches the stream to an HTTP response, etc. The stream's
element type is the type of `value` (or the union of all feed-value
types if multiple feeds target the same defer).

The deferred collection a target accumulates is, like any CHL
collection, **unordered** (§3): multiple `<<` statements — across
different iterations of a `for` loop, or across multiple feed sites
in the same body — contribute their values to the bag without
promising any ordering between contributions. This is true even of
two feeds on consecutive lines of the same loop body: with no data
dependency between them, the implementation may run them in any
order or in parallel. Ordering only becomes observable when
something else in the program forces sequencing (a loop-carried
accumulator, or a sink whose own contract pairs feed-values with
their triggering inputs — e.g. `http_serve` pairs each response
with its request).

`<<` is **not** a bitwise-shift operator (CHL has no bitwise shifts).
Despite the token reuse, this is its only meaning.

> **Direction — `Feed(V)` [Decided].** Feed-ability becomes a property
> of the *type*, not of how the value was introduced: a feedable
> collection has type `Feed(V)`, and a feed target is forward-declared
> with an annotation-only binding `h: Feed(_)` (no initialiser) instead
> of a `defer()` call
> ([2026-06-29 §5](brainstorm/2026-06-29-syntax-convergence.md); the
> north-star `fanout` program is the worked example). This vocabulary
> supersedes the `deferred`-introducer sketch in
> [2026-04-23-sink-operators.md](brainstorm/2026-04-23-sink-operators.md).
> **[Tentative]**: `<<` additionally becoming the general append
> operator for lists/sets/collections (2026-06-29 §2). **[Open]**:
> whether the `<<=` define-statement (§4.4) survives alongside this
> vocabulary — the new sketch never mentions it.

### 3.8 Function calls

```
f(arg₀, arg₁, …, argₙ₋₁)
```

The call denotes `f` applied to the tuple `(arg₀, …, argₙ₋₁)`: the
result is the function's return value on those arguments. The order
in which `f` and the arguments are themselves evaluated is
unspecified (§3 — *Evaluation order*).

CHL functions are **uncurried**: a function declared with `n`
parameters consumes all `n` arguments together. There is no implicit
currying — `f(a)` for an `n>1`-arity `f` is a compile-time error, not
a partial application.

**No keyword arguments**, **no default values**, **no `*args`/`**kwargs`**,
**no positional-only / keyword-only markers**. The function-call grammar
is exactly a parenthesised, comma-separated list of expressions.

> **Direction [Decided].** Every function takes exactly **one**
> argument, and the argument's product structure is what "arity" is: a
> higher-arity function is a function on a *tuple*, and a
> keyword-argument function is a function on a *record* with named
> fields. Under the term-level delimiter direction (§2.4) the call
> parentheses simply *are* the product constructor — `f(a, b)` applies
> `f` to the tuple `(a, b)`, and `f(x=1, y=2)` applies `f` to the
> record `(x=1, y=2)`. "Keyword arguments" and "a record argument" are
> the same thing, which dissolves the record-vs-call ambiguity flagged
> in §2.4. Whether one call can mix positional and named components (a
> product with both anonymous and named fields) is **[Open]**.
> Recorded here only (2026-07-07, no brainstorm writeup yet).

A *zero-argument* call is valid only against a name registered as a
**data source** — `stdin()`, `http_serve(...)`, or any source
pre-registered by the host (§7.4) — or against the builtin `defer()`
(§7.3). A zero-argument call against any other name is a compile-time
error.

### 3.9 Subscript and attribute access

```
target[index]    -- subscript: list element or dict lookup
target.attr      -- attribute: record field access
```

- **Subscript** on a list with integer index `i` denotes the i-th
  element (0-based). An out-of-range subscript is a compile-time type
  error when statically known; otherwise the expression is not
  defined (see *Partiality*, §3).
- **Subscript** on a dict with key `k` denotes the value associated
  with `k`. Looking up a missing key is not defined (see *Partiality*,
  §3).
- **Attribute** on a record denotes the value of the named field. The
  field must exist; missing fields are a compile-time type error.

Lists, dicts, and records all denote *finite functions* from their
respective index domains (`UInt`, `K`, field-name) to their element /
value type — so subscript and attribute access are uniformly
"evaluate the finite function at a point," just spelt differently.

> **Direction [Tentative].** The collections sketch
> ([2026-06-29 §2](brainstorm/2026-06-29-syntax-convergence.md), §6.3
> below) makes partial lookup total by returning an option: `lst[i]`
> and `map[k]` have type `Option(T)` (matched with `some(v)` / `none`,
> as in the north-star `txn_kv`), while `Array` lookup stays direct
> (`arr[i]: T`) because its bounds are statically checked. That would
> eliminate the not-defined lookup cases above (see *Partiality*, §3).

### 3.10 Lambda

```
lambda x: body
lambda x, y, z: body
lambda x: T, y: U: body          -- typed parameters [Planned]
lambda: body                     -- zero-arity
```

A lambda denotes an anonymous function value. Applying the lambda to
a tuple of argument values gives the value of `body` in an environment
where each parameter is bound to its corresponding argument
positionally.

Like `def`-defined functions (§4.1), lambdas are uncurried: an n-arg
lambda consumes all n arguments at once and is invoked through an
n-arg call.

Annotated lambda parameters mirror `def` parameters (§4.1). Refinement
annotations are not yet writable in the surface syntax; some built-ins
(e.g. `groupby`, §7.2) produce refined lambdas internally.

> **Direction — `λ x → body` [Decided].** The convergence syntax
> retires Python's `lambda x: body` in favour of `λ x → body`, with
> ASCII fallback `\x -> body`
> ([2026-06-29 §1](brainstorm/2026-06-29-syntax-convergence.md)). This
> makes the surface lambda match the CCL symbolic form exactly, so
> surface and core read alike — e.g. `groupby(sales, λ r → r.region)` —
> and frees `:` in a lambda head for its annotation role
> (`λ x : T → body`).

### 3.11 List, tuple, record, dict literals

| Form | Denotes |
|---|---|
| `[]`, `[e₀, e₁, …]` | A finite list — an indexed bag of elements. The element at integer index `i` is `eᵢ`, but iteration order is unspecified (§3). Element types must unify. |
| `(e,)`, `(e₀, e₁, …)`, `e₀, e₁, …` | An anonymous heterogeneous product (tuple). Element types may differ. Tuples are positional, not unordered: `(1, 2)` and `(2, 1)` are distinct values. |
| `{}`, `{name: e, …}` | A record (named-field product). Field names are bare identifiers; field types may differ. |
| `{k₀: v₀, …}` (any non-identifier key) | A dict (finite map). Key types must unify; value types must unify. Parses today, but rejected at lowering. |

A trailing comma is allowed in every form (and required to disambiguate
`(e,)` from `(e)`).

**Record vs. dict.** The parser classifies a `{...}` literal by its
keys (§2.4): all-bare-identifier keys make a record, anything else
makes a dict. The two are different constructs despite sharing a
delimiter — a record is a product with statically-known fields, a dict
is a finite map over dynamic keys. Both the shared delimiter and the
look-at-the-keys rule are transitional (see the Direction note below).

**Empty forms.** `{}` is the empty record. `[]` is the empty list.
There is no empty-dict literal today.

> **Direction [Decided].** The literal forms migrate with the
> delimiter split (§2.4) and the collections model (§6.3), form by
> form:
>
> | Today | Target |
> | --- | --- |
> | `(1, 2)` — tuple | unchanged: `( … )` is the product constructor |
> | `{name: e, …}` — record | `(name=e, …)` — a record is a product with named fields (and a call's keyword arguments are exactly such a record — §3.8) |
> | `{"k": v, …}` — dict | `[k=v, …]` — a map literal; `[ … ]` is the collection delimiter |
> | `[1, 2, 3]` — list | same spelling, but shared across collection types: the literal can denote an `Array`, `List`, or `Set`, disambiguated by annotation or usage, with `list([…])` / `set([…])` constructors for explicitness (**[Tentative]** — §6.3) |
> | `{}` — empty record | the empty product `()`: records and tuples are both products (§3.8), so the empty record, the empty tuple, and the unit value coincide (§3.1) |
> | `[]` — empty list | same spelling; the empty-**map** spelling is **[Open]** (§2.4) |
>
> `{ … }` itself moves wholesale to the type level (§2.4, §6.1); no
> term-level literal keeps braces.

### 3.12 Comprehensions

```python
[ element  for x in xs  if cond  for y in ys  ... ]
( element  for x in xs  if cond  ... )
```

The square-bracket and parenthesised forms are **equivalent**: same
denotation, same evaluation semantics, same streaming behaviour. Pick
whichever reads more naturally at the call site (the parenthesised
form often reads better as a function argument: `sum(x * x for x in xs)`).

Comprehensions are the **primary collection-level construct** in CHL —
they replace what would be SQL `SELECT … FROM … WHERE …` or LINQ in
other languages.

**Semantics.** A comprehension denotes the bag of `element`
evaluations taken over the cross-product of its `for` clauses,
filtered by each `if` guard. Concretely, for a comprehension with
clauses `for x₁ in xs₁ ⟨guards…⟩ for x₂ in xs₂ ⟨guards…⟩ … for xₙ in
xsₙ ⟨guards…⟩`, the result contains one `element` value for each tuple
`(x₁, …, xₙ) ∈ xs₁ × xs₂ × … × xsₙ` such that every interspersed `if`
guard holds. The output is **unordered** (§3) — like any CHL
collection, it is a bag, and downstream consumers must not rely on
the order in which the tuples were enumerated.

A guard depending only on outer iteration variables (e.g. `if c(x₁)`
sitting between `for x₁` and `for x₂`) acts as a *prune* on the outer
loop: when the guard fails for a given `x₁`, no `(x₁, x₂, …)` tuple
involving that `x₁` is produced. This is a semantic property, not
just an optimisation — the compiler is required to skip the inner
product, not merely allowed to.

Comprehensions are **finite** when each source is finite; over an
infinite source (e.g. `stdin()`) they remain streaming and produce
elements as inputs arrive.

> **Implementation note.** The compiler recognises several
> comprehension shapes and emits specialised dataflow for them:
> - `for x in xs for y in ys if x.k == y.k` is compiled as a hash
>   join rather than a nested loop.
> - `for g in groupby(c, key)` produces a keyed aggregate dispatch.
>
> These rewrites preserve the semantics described above; users should
> not need to reason about which strategy the compiler picked.

### 3.13 `yield`

```
yield expression
```

`yield` is valid only inside the body of a `def` function. A function
containing any `yield` is a **generator function** (§4.2); `yield`
outside a `def` is a compile-time error.

Evaluating `yield e` adds `e` as one element of the deferred
collection that the enclosing generator function returns. The
collection is, like any CHL collection, an **unordered bag** (§3);
the relative order of values from distinct `yield` evaluations
(whether from different iterations of a `for`, or from sequential
`yield`s in straight-line code) is unspecified unless a loop-carried
accumulator forces sequencing. The expression itself returns `None`;
its purpose is the contribution.

`yield from`, `yield`-as-expression-with-value, async `yield`, etc., are
not in CHL.

### 3.14 Recovery placeholders

The parser may produce `Expr::Error` and `Stmt::Error` placeholders
during error recovery (see [src/chl_parser/design-chl-parser.md](../src/chl_parser/design-chl-parser.md)).
These appear only when the `ParseResult.errors` list is non-empty;
they carry no runtime semantics — a program containing one cannot be
compiled. Tools that consume a partial AST (LSP, editor diagnostics)
treat them as "an expression / statement was intended here, but its
text didn't parse."

---

## 4. Statement semantics

A CHL **program** is its top-level block (§2.1): a sequence of
statements. Each non-terminal statement either introduces a binding
visible to the remainder of the block, or performs an effect (a feed
into a deferred output). The block's *value* is the value of its final
expression statement; if the program registers any sinks (e.g.
`http_serve`), the program value is implicitly a record of those sinks
instead.

Equivalently — and this is the model to keep in mind when reading
nested blocks — a sequence

```python
x = e₁
y = e₂
e₃
```

denotes `e₃` evaluated in an environment where `x` is bound to `e₁`
and `y` is bound to `e₂`. Bindings are introduced for the remainder
of their enclosing scope and may not be forward-referenced; the
execution order of the bound expressions themselves is constrained
only by data dependencies (§3 — *Evaluation order*), so two
independent bindings may be evaluated in any order. Statement-level
scoping is always introduction-then-rest, never two-pass.

### 4.1 `def` — function definition

```python
def name(p₀, p₁, …, pₙ₋₁):
    body
```

A function definition introduces a name bound to a function value with
the listed parameters and body. Each parameter may carry an optional
type annotation:

```python
def f(x: Int, y):
    return x + y
```

Annotations are arbitrary expressions evaluated in the surrounding
scope; they refine the inferred parameter type. Annotations on the
function's *return type* are not yet supported.

A function whose body contains a `yield` expression anywhere is a
**generator function** — see §4.2 for its semantics. The rules in the
rest of this section apply to **non-generator** functions, whose body
must produce a value explicitly.

The body of a non-generator function is a non-empty block of
statements whose last statement yields a value — i.e. one of:

- a bare expression statement (its value is the function's result),
- a `return e` statement,
- an `if`/`elif`/`else` chain whose every branch ends in one of the
  above (the branch's value is the function's result for that case).

A function value captures the values of free names in its surrounding
scope at definition time (lexical capture). Captured names are
read-only: a function cannot mutate a name from an outer scope.
Recursion through self-reference is **[Planned]**; for now each
function must be definable without referring to its own name.

> **Direction.** The read-only-capture rule is scoped to today's
> language: under the mutability direction (**[Decided]** — §6.2, §8)
> a function can mutate captured state whose type carries the wrapper,
> as the north-star `txn_kv`'s `put` does to the top-level
> `store: Mut(Map(…), Txn)`. What stays true is that the capability is
> visible in the types at the binder, not smuggled in.

### 4.2 `def` — generator function

A function whose body contains a `yield` expression anywhere — at any
nesting depth, inside any `for` / `if` / sequence of statements — is a
**generator function**:

```python
def positives(xs):
    for x in xs:
        if x > 0:
            yield x
```

When called, a generator function returns a collection
whose elements are the values contributed by each `yield e` evaluated
during the body's execution. Like any CHL collection (§3), this is an
unordered bag — the order in which `yield`s ran is not preserved
unless a loop-carried accumulator inside the body sequences them.

The body is otherwise an ordinary statement block: assignments
introduce bindings, `for` loops iterate, `if`/`elif`/`else` selects a
branch, and so on. The function has no explicit return value — its
result is the bag of yields. (A bare `return` with no operand
is permitted as an early exit; `return e` with a value is rejected
inside a generator.)

The returned collection participates in any downstream comprehension,
aggregate, or feed just like a list literal would. The key difference
is that a generator's elements are produced lazily as the body
executes, so it can be the source of an unbounded stream (e.g. when
`xs` itself is `stdin()`).

> **Currently supported shape.** Today the compiler only handles a
> generator body that is exactly one top-level `for` loop (with
> arbitrary nested `if`/`elif`/`else` and assignment statements inside
> that loop). The following shapes are recognised as generator
> functions by the parser and rejected during compilation today
> ([Planned]):
>
> - `yield` at the top level of the body (no enclosing `for`).
> - Two or more sequential `for` loops in the body.
> - Nested `for` loops where the inner loop yields.
> - Statements after the `for` loop.
>
> The *semantics* described above is what each of these shapes will
> denote once support lands; the current restriction is an
> implementation limitation, not a semantic distinction.

### 4.3 Assignment forms

| Form | Semantics |
|---|---|
| `target = value` | Evaluate `value`, bind it to `target` for the rest of the enclosing scope. |
| `target: T = value` | Same as above, additionally checking that `value` has type `T`. |
| `target op= value` | Equivalent to `target = target op value`: the binding is **replaced**, the old value is shadowed. Not in-place mutation. |
| `target <<= value` | Resolves a previously-deferred name to `value` (§4.4). |

`target` is an `AssignTarget`: a bare name or a (nested) tuple of bare
names. Tuple destructuring:

```python
a, b = pair
(x, (y, z)), w = nested
```

is supported at any nesting depth.

**No assignment-as-expression** (no walrus `:=`). **No multi-target
chained assignment** (`a = b = c` is not in the grammar).

Annotated assignment **requires** a value (`x: T` alone is a parse error,
unlike Python's bare type-only declarations).

Augmented assignment `x += 1` is a **rebinding**, not a mutation: the
name `x` now refers to a new value, but no other reference to the
previous value is affected. The previous binding is shadowed for the
rest of the scope.

Reassignment *inside a `for` body* of a name introduced in an outer
scope has different semantics: it is a **loop-carried accumulator**
update, described in §4.6. See
[docs/brainstorm/2026-04-06-mutability.md](brainstorm/2026-04-06-mutability.md)
for the temporal-functional-mutation model that motivates this
treatment.

> **Direction — `=`, `:=`, `rec` [Decided].** In the target binding
> model ([2026-06-29 §3](brainstorm/2026-06-29-syntax-convergence.md)),
> `=` is reserved for *timeless equations* — `x = e` asserts `x ≡ e`
> with no before/after — and a binding departs from it along two
> independent axes:
>
> - **Time → `:=`.** A mutable's value at the current moment is written
>   `x := e`, covering both initialisation and update (`+=` and friends
>   become sugar over `:=`). An initialising `:=` is itself enough to
>   mark the variable mutable; a `Mut(_)` annotation (§6.2) is
>   mandatory only where there is no initialiser, e.g. parameters.
>   Today's loop-carried accumulator (§4.6) is this model's motivating
>   case: under the target syntax its updates are written with `:=`,
>   and the current "rebinding inside a `for` body" encoding goes away.
> - **Self-reference → `rec`.** A self-referential *value* binding must
>   be marked: `rec reach: Set({src: Int, dst: Int}) = … reach …`
>   solves the equation as a least fixpoint (see the north-star
>   `reachability`). `rec` stays in the timeless `=` world — a fixpoint
>   is a value, not a mutation. Unmarked value self-reference is a
>   compile error; `def` self-reference and recursive types need no
>   marker.
>
> **[Open]**: whether same-scope *shadowing* (`x = 1` then `x = 2`,
> legal today per §5) survives once `=` reads as a timeless equation —
> two equations for one name in one scope contradict the reading, but
> the brainstorm doesn't address it.

### 4.4 Define statement `<<=`

```python
result <<= computation
```

`<<=` resolves a deferred output by giving it a value. Semantics:

- The name on the LHS must have previously been introduced as a
  deferred-collection placeholder — either explicitly via `defer()`
  (§7.3) or implicitly via a sink-producing call like `http_serve`
  (§7.4).
- `<<=` ties the placeholder to the RHS: from this point on, every
  consumer of the deferred name sees the value computed by `computation`.
- It is a compile-time error to `<<=` a name that wasn't introduced as
  a defer, or to `<<=` the same defer twice.

`<<` and `<<=` are the two halves of the deferred-output protocol:
`<<` *feeds* elements into a deferred collection during a streaming
computation; `<<=` *defines* the deferred collection outright as a
specific value. A single defer is closed by exactly one of these
forms.

`<<=` is **not** an augmented assignment — the grammar recognises it
as its own statement form.

> **Direction.** The 2026-06-29 Feed vocabulary (§3.7) replaces
> `defer()` with `Feed(_)` forward declarations and keeps `<<`; it does
> not mention `<<=`. Whether the define-outright half of the protocol
> survives, and under what spelling, is **[Open]**.

### 4.5 `if` / `elif` / `else`

```python
if cond₀:
    block₀
elif cond₁:
    block₁
else:
    block_else
```

`if`/`elif`/`else` is a *statement*; for an expression form use the
ternary (§3.6).

The branches are tried in source-text priority: the value of the
statement is the value of the block under the first guard that holds,
and the blocks under later guards do not contribute. If no guard
holds and an `else` is present, `block_else` is the chosen block;
if no guard holds and no `else` is present, the `if` statement
produces no value and contributes no binding to the enclosing scope.
As with short-circuit `and`/`or` (§3.5), this is a semantic
property — guards beyond the winning one need not be defined, and
non-winning blocks contribute no effects.

Each branch's block is itself a statement block. When the `if` chain
occurs in a position that requires a value (function body, program
value), every branch — including `else` — must end in a value-yielding
statement, and the missing-`else` case is rejected as "if used as an
expression, all branches must produce a value."

### 4.6 `for` — iteration

```python
for target in iter:
    body
```

`target` is an `AssignTarget`; `iter` is any expression denoting a
collection. The body executes once per element of `iter`, with
`target` bound to the current element.

**Iterations are unordered and may run in parallel** (§3): unless the
body introduces a data dependency from one iteration to the next, the
implementation is free to evaluate the iterations in any order and
concurrently. The single way to sequence iterations is a loop-carried
accumulator (below).

A bare `for` loop in a non-generator context is an **effect
statement**: its purpose is to feed values into deferred outputs as it
iterates. The body must contain at least one `<<` feed expression;
otherwise the loop would be inert (produces no value, has no effects)
and is rejected. The canonical effect-for-loop is the `http_greeter`
request handler:

```python
for req in greet_reqs:
    greet_resps << prefix + "stranger!\n"
```

Inside a generator function (§4.2) the body uses `yield` instead of
`<<` — `yield` plays the same role as `<<` but feeds into the
generator's implicit result collection.

**Loop-carried accumulators.** A for-loop body may also rebind names
introduced in an outer scope (function arguments, pre-loop lets, or
any binding from an enclosing frame). Such a rebinding is *not* a
new per-iteration shadow; it is an **accumulator update**, and it
introduces an inter-iteration data dependency that **forces the loop
to run sequentially** in the order dictated by that dependency:

- Before the loop, the name has its outer value.
- At each iteration, the body computes a new value for the name from
  the previous-iteration's value and the current element.
- After the loop, the name holds the value at the last iteration
  (or, if the source was empty, the outer pre-loop value).

In other words: loops are parallel by default, and the presence of an
accumulator is what serialises them. A loop with multiple
accumulators is still a single sequential loop — the dependencies are
shared across all of the accumulators in lockstep with the iteration.

```python
acc = 0
for i in [1, 2, 3, 4, 5]:
    acc = acc + i
acc                              # 15
```

Multiple accumulators are supported (one per rebound outer name);
their updates within an iteration are ordered by their data
dependencies, so a later accumulator's update may freely refer to an
earlier accumulator's just-computed value. The same rule covers
generator functions with loop-carried state
(`total = 0; for x in xs: total += x; yield total`).

Assignments inside a for-loop body whose target is a **fresh** name
(not introduced in an outer frame) are ordinary per-iteration
bindings: in scope for the rest of the iteration, gone at the next
one.

> **Direction.** Under the `:=` mutation model (§4.3, **[Decided]**)
> accumulator updates are written `acc := acc + i`, making the
> loop-carried dependency explicit at the update site instead of being
> inferred from "rebinding of an outer name". The sequencing semantics
> described here are unchanged by the notation.

*Currently unsupported* (see §12): nested for-loops with mutable
variables, and `while` loops.

### 4.7 `pass`

No-op statement that holds a place where a block is required:

```python
def todo(x):
    pass    # placeholder body
```

A `pass` body is only valid where a block of statements is required and
no value is expected. A function body of `pass` is rejected because the
function body must yield a value.

### 4.8 `return`

```python
return                -- equivalent to `return None`
return expression
```

`return` produces the enclosing function's result. CHL has no early
exit: `return e` is only meaningful as the **last** statement of a
function body, or as the last statement of each branch of a terminal
`if`/`else`. A `return` followed by further statements is rejected —
the "return early, fall through otherwise" idiom must be written
explicitly as `if cond: return e\nelse: <rest>`.

### 4.9 Expression statement

A bare expression `e` is a statement. The expression is evaluated; if
it appears as the **last statement** of a block, its value is the
block's value, and if it appears elsewhere, it must be a feed
expression (`target << value`) — otherwise the statement is inert and
is rejected.

This rules out Python's "expression for its side-effect" idiom for
anything except `<<`. CHL has no implicit-effect functions.

> **Direction.** Under the mutability direction (**[Decided]** — the
> *purity* note in §3, §6.2, §8) effecting functions exist: a function
> can take `Mut(…)` parameters or declare `requires Transaction`, and
> a bare call to one — `put(req.body.key, req.body.value)` in the
> north-star `txn_kv` — is a legitimate expression statement evaluated
> for its effect. The rule above then generalises from "must be a
> feed" to "must have an effect". What survives unchanged is the
> second sentence: there are still no ***implicit***-effect functions —
> a function's effects are always visible in its signature, so an
> inert statement remains detectable, and remains rejected.

---

## 5. Scoping and binding

CHL is **lexically scoped**. The scopes are:

1. **Top-level scope** — the top-level block (§2.1) of a `.cambra`
   file.
2. **Function scope** — the parameters and body of a `def`.
3. **Lambda scope** — the parameter(s) and body of a `lambda`.
4. **Comprehension scope** — each `for x in …` clause of a
   comprehension introduces `x` into the comprehension's scope, visible
   to subsequent clauses, guards, and the element expression.
5. **`for`-loop scope** — the loop variable (`target` in
   `for target in iter:`) is in scope only inside the loop body. After
   the loop, the name is **not** in scope — there is no "value at the
   last iteration" to bind it to, because iterations are unordered and
   may run in parallel (§3, §4.6). This is a deliberate divergence from
   Python's leaky-loop-variable behaviour. Any value the loop needs to
   produce for downstream code must be carried out via a loop-carried
   accumulator (§4.6) or yielded into a deferred collection.

A binding form (`=`, annotated `x: T = e`, `<<=`, `for`, `def`,
`lambda`, comprehension `for`) introduces a name for the rest of its
enclosing scope. Re-binding the same name in the same scope
**shadows**; previous values are not recoverable. (Whether shadowing
survives the timeless reading of `=` is **[Open]** — see §4.3.)

There is no `global` / `nonlocal` mechanism — closure capture is the
only way for a function to refer to outer names, and capture is
read-only.

---

## 6. Types (informal sketch)

This section is a sketch. The authoritative type system lives in
[`src/ccl/infer/`](../src/ccl/infer/) — see
[src/ccl/design/type-inference.md](../src/ccl/design/type-inference.md).
CHL types are inferred; user-written annotations refine the inferred
type.

Built-in surface types. (The names below are this spec's vocabulary
for talking about the checker; annotations are writable today only on
`def` parameters and `x: T = e` bindings, and the checker recognises
only a subset of these types in annotation position.)

- `Int` — signed 64-bit integer.
- `Bool` — `True` or `False`.
- `String` — UTF-8 string.
- `None` — unit type, one inhabitant.
- `List(T)` — finite collection of `T`-values, indexed by `[0, n)`.
  The index → element mapping is part of the value (so `xs[i]` is
  well-defined); iteration order, however, is unspecified (§3).
- `{T₀, T₁, …}` — tuple type (structural `{…}` type syntax — §6.1).
- `{name: T, …}` — record type. Two records are the same type iff they
  have the same field names with the same field types.
- `Dict(K, V)` — finite-map type.
- `{T₀, T₁, …} ⇒ U` — function type. A function takes exactly one
  argument (§3.8): an n-parameter function's domain is the
  corresponding tuple type, and a keyword-argument function's domain
  is a record type — `{x: T, y: U} ⇒ V`. Surface syntax for function
  types in annotations is **[Planned]**.

CHL also supports **refinement types**: a value of the refined type is
a value of the base type for which a predicate holds. Refinements are
inferred internally by built-ins like `groupby` (§7.2); the decided
surface form is `{x: T | p(x)}` (§6.1), not writable yet.

The underlying type system additionally tracks unions, source types,
and inference variables; see
[docs/operational-semantics/](operational-semantics/) for the formal
treatment.

### 6.1 Direction: term/type syntax split [Decided]

([2026-06-29 §1](brainstorm/2026-06-29-syntax-convergence.md).)

**Capitalization distinguishes term from type.** Lowercase heads are
terms; capitalized heads are types. Data *constructors* build values,
so they are lowercase — `some`/`none`, `ok`/`err` — and only the type
(`Option(T)`) is capitalized. `Caps` means *type*, without exception
(unlike ML and Rust, which capitalize constructors).

**Application is shared across levels.** `f(args)` is application
whether `f` is a value or a type constructor: `split(line)` and `ok(v)`
at the term level; `List(T)`, `Map(K, V)`, `Set(T)`, `Mut(V)` at the
type level. The head's case tells you which. Since Cambra is
dependently typed, a type constructor can take a *term* argument —
`Default(0, Nat)` — with no special bracket rule; in particular `[…]`
is **not** generic-argument syntax (it belongs to collections, §2.4).

**`{…}` is structural-type syntax** (§2.4): tuple type `{T, U}`, record
type `{f: T}`, refinement `{x: T | p(x)}`.

### 6.2 Direction: non-purity as type wrappers [Decided]

([2026-06-29 §4](brainstorm/2026-06-29-syntax-convergence.md).)

Whether a value is mutable / feedable / transactional is a property of
its **type**, expressed as a wrapper: `Mut(V)`, `Feed(V)`,
`Mut(V, Txn)`. Wrappers have to appear in function signatures and
inside data structures regardless (a function taking a mutable map, a
map *of* feeds), so they are types rather than introducer keywords.

Two supporting rules:

- **Impure types are annotated at binders.** The wrapper must be
  written at the binding that introduces it — a bare
  `def add_one(x): x += 1` is rejected without `x: Mut(_)`.
- **`_` means "infer the rest."** A partial-inference type hole:
  `def add_one(x: Mut(_)): …` infers `Mut(Int)`; likewise
  `Map(String, _)`, `List(_)`.

For ergonomics, an initialising `:=` alone marks a variable mutable
(`total := 0`); `Mut(_)` annotations are mandatory only where there is
no initialiser (§4.3).

### 6.3 Direction: collections as functions [Tentative]

The **organizing idea is decided**
([2026-06-29 §2](brainstorm/2026-06-29-syntax-convergence.md)), and
already shows through in §3.9: a collection *is* a function
`Domain ⇒ Value`, and the collection types are variations of that one
shape. The specific encodings below are a working sketch — expect the
details to change:

- `Array(n, T)` — `Fin(n) ⇒ T`: known size and order; statically
  bounds-checked lookup `arr[i]: T`.
- `List(T)` — `{len: Nat, data: Fin(len) ⇒ T}`: an array "boxed" with
  its length when the length isn't statically known; `lst[i]: Option(T)`.
- `Set(K)` — `Map(K, {})`: the domain is the payload; membership via
  `e in s` (§3.4).
- `Map(K, V)` — `{is_key: K ⇒ Bool, data: {K | is_key} ⇒ V}`; lookup
  `m[k]: Option(V)`, membership `k in m`.
- `Collection(T)` — `{Dom: Type, data: Dom ⇒ T}`: the domain rides
  along in the value.

Sketched at the same **[Tentative]** level:

- Ordering splits by type: `Array` and `List` are *ordered*; `Set`,
  `Map`, and `Collection` are unordered, with order-dependent
  operations over them expected to take their ordering explicitly as
  a given instance (§8, and the Direction note in §3).
- Arrays, lists, and sets share literal syntax; the type comes from
  annotation or usage, with `list([…])` / `set([…])` constructors for
  explicitness (the north-star `reachability` uses `set(…)`).
- Out-of-line definition of immutable collections: element-wise
  dereference-definition `c[i] = v` — with the compiler checking that
  multiple out-of-line definitions of the same collection don't
  overlap — and append via the feed operator `c << v`; `c[i] := v` for
  mutable collections.
- Immutable collections as the encouraged default; mutable ones get
  the standard mutation operations.

---

## 7. Built-in functions and sources

CHL programs interact with the outside world through **data sources**
(streaming inputs) and **sinks** (streaming outputs), plus a small set
of built-in functions.

### 7.1 Aggregates

| Call | Result |
|---|---|
| `sum(xs)` | Sum of the elements of `xs`. Operates on integer collections. |
| `max(xs)` | Maximum element of `xs`. Element type must support `<`. |

Both are unary and take a collection-typed argument. Other aggregates
(`min`, `count`, `avg`, `len`) are **[Planned]** but not yet recognised.

The north-star programs additionally assume non-aggregate built-ins —
`str`, `open`, `stdout`, and a stream-restriction combinator
`restrict` — all **[Tentative]**: they exist only as usage sketches in
[`tests/programs/`](../tests/programs/), with no design writeup.

### 7.2 `groupby`

```
groupby(collection, key_fn) : K ⇒ Collection
```

`groupby(c, k)` denotes a function from key values to sub-collections:
applied to a key `v`, it returns the elements of `c` for which
`k(elem) == v`. Iterating `groupby(c, k)` yields one element per
distinct key, where each element is itself the group of `c`-elements
sharing that key.

```python
[ sum([s.amount for s in g]) for g in groupby(sales, lambda r: r.region) ]
```

The standard pattern (above) — group, then aggregate per group — is
what `groupby` is primarily designed to support.

### 7.3 `defer`

`defer()` (zero arguments) creates a deferred collection placeholder.
It is rarely written explicitly — most users get a defer implicitly
from `http_serve` or from generator functions. When written, the
defer must be tied off later with `<<=` or fed via `<<`.

> **Direction [Decided].** `defer()` is superseded by the `Feed` type
> wrapper: a feed target is introduced by an annotation-only forward
> declaration `h: Feed(_)` rather than by a call (§3.7, §6.2).

### 7.4 Sources

Sources are built-in functions registered at compile time. A source
call denotes the entire stream the source will produce.

| Call | Source | Domain |
|---|---|---|
| `stdin()` | Process standard input | One element per line of UTF-8 text. |
| `http_serve(port, method, path)` | HTTP server | Returns a `(requests, responses)` 2-tuple. The requests stream yields request bodies; the responses are a deferred collection to feed. Must be assigned at top level via tuple destructuring (see below). |

Additional sources may be pre-registered by the host embedding (testing,
demos, etc.).

`http_serve` has a special-cased statement form:

```python
reqs, resps = http_serve(port, method, path)
```

This pattern (`identifier-tuple = http_serve(string, string, string)`)
must appear in the top-level block. It binds two names:

- the `reqs` side is a streaming source: each element is the
  body of one incoming request to `(method, path)` on `port`.
- the `resps` side is a deferred output: feeds into it
  (via `<<` from a request-handler `for` loop, or via `<<=` once)
  become the response bodies. The sink pairs each response with its
  triggering request — the request that was bound to the loop
  variable in the iteration that produced the response.

Multiple `http_serve` calls in the same program that share a `port`
share an HTTP listener; the `(port, method, path)` triple must be
unique across the program.

> **Direction [Open].** The HTTP module design is deliberately parked
> ([2026-06-29, Open/deferred](brainstorm/2026-06-29-syntax-convergence.md)):
> how responses carry status codes (`ok(…)`, `not_found(…)`), the
> structured-request surface (`req.body`, `req.query`, `req.time`,
> headers), response pairing via feed-at-index (`resps[req.id] = …`, as
> the north-star `txn_kv` writes it), and multi-endpoint multiplexing
> are all sketches, not decisions. The `(requests, responses)`
> tuple-destructuring form above is what's implemented today.

---

## 8. Transactions and contextual parameters [Decided]

Nothing in this section is implemented — none of its keywords even lex
today (§1.6). It is specified here because the design is decided
([2026-06-29 §6](brainstorm/2026-06-29-syntax-convergence.md)) and the
north-star `txn_kv` program exercises it end to end.

Transactions use a **contextual-parameter** mechanism modeled on
Scala 3's `given`/`using`/`summon`:

- `def put(…) requires Transaction:` — the function declares that it
  needs a transaction from context.
- `with begin():` — opens a transaction and puts it in the given
  context for the block. **Commit is implicit on normal block exit**;
  `abort()` rolls back.
- `with begin() as txn:` — same, and additionally binds the transaction
  so its methods are callable (e.g. `txn.current_time()`).
- `given txn` — injects an existing transaction into the context.
- `summon(Transaction)` — manifests the contextual transaction as a
  value.

Shared mutable state accessed by concurrent handlers **must** be
transactional — `store: Mut(Map(K, V), Txn)` — and every access runs
inside a `with begin():` block; this is what makes a read-modify-write
atomic in the presence of concurrent `http_serve` handlers.

Supporting decisions (same source):

- **Discharged by the typeclass/given solver, *not* algebraic
  effects.** Cambra compiles to static dataflow; handler-based effects
  make control flow non-local and data flow handler-dependent — exactly
  what the dataflow compiler cannot see through. `requires Transaction`
  is ordinary dictionary passing, resolved by the same solver that will
  serve general typeclasses.
- **Locally-scoped givens, not global coherence.** A fresh transaction
  is minted per `with begin()` block; many exist over a program's life.
- **Domains as a type index.** `Transaction(dom)`, created with
  `with dom.begin()`, restores per-domain coherence while allowing
  fresh transactions across scopes. Start with one global domain and
  make `dom` itself a given, so the common case omits it.
- **Commit/abort are data operations on a time-region**, not control
  effects: block exit merges the region forward (commit), `abort()`
  drops it (rollback) — a structured early-exit, not exception
  unwinding.
- **Terminology:** type `Transaction`; variable abbreviation `txn`
  (never `tx`, which collides with "transmit"); operations `begin()` /
  `abort()`; commit is implicit.
- **Implicit *parameters* only — never implicit conversions**; given
  visibility stays explicit and resolution inspectable (hence
  `summon`).

## 9. Sinks

Sinks can be declared anywhere in the program, but all external side
effects are lifted to the boundary of the program.  The program returns
a Record of collections that need to be bound to each sink.

Sinks may observe the indices of collections passed to them if needed.

## 10. Errors and recovery

### 10.1 Lex errors

The lexer reports four error kinds and stops emitting tokens at the
first one:

- **`InvalidToken`** — no token rule matched at the position.
- **`UnmatchedClose`** — `)`, `]`, or `}` with no matching open.
- **`UnclosedBracket`** — EOF reached with at least one open `(`/`[`/`{`.
- **`InconsistentIndent`** — dedented to a level not on the indent
  stack.

### 10.2 Parse errors and recovery

The parser uses chumsky's error-recovery infrastructure to produce
multiple diagnostics per file. Two recovery layers:

- **Bracket-level recovery** — a failure inside `(…)`, `[…]`, or `{…}`
  produces an `Expr::Error` placeholder spanning the bracketed region.
- **Statement-level recovery** — a failure at the statement level
  skips tokens to the next `NEWLINE` (and any following balanced
  `INDENT…DEDENT` block) and produces a `Stmt::Error` placeholder.

A parse always returns a `ParseResult<T>` carrying *both* a partial AST
(possibly containing recovery placeholders) and a list of errors. See
[src/chl_parser/design-chl-parser.md](../src/chl_parser/design-chl-parser.md)
for the recovery design and error-rendering details.

### 10.3 Semantic errors

If the parse succeeds, the compiler may still reject the program for
semantic reasons:

- Use of an unsupported construct (e.g. `yield` outside a generator
  function, `while` loops, `http_serve` not at top level).
- Use of an unknown name as a zero-argument call.
- Type mismatches (e.g. comparing values of incompatible types,
  feeding a non-deferred name).
- Unsupported operator combination that the current planner can't
  emit dataflow for.

Semantic errors are reported with the source span of the offending
expression or statement.

---

## 11. Examples

The canonical examples live in [`tests/programs/`](../tests/programs/)
— one directory per program, each with its `program.cambra` source and
a test pinning its behaviour. [docs/demo-programs.md](demo-programs.md)
is the human-facing gallery: per-program status, the features each one
exercises, and its blockers. This spec deliberately does not inline
them — the gallery is the single source of truth.

The gallery holds two kinds of program. Most compile today and
illustrate implemented features. The **north-star** programs —
`reachability`, `fanout`, `txn_kv` — are instead written in the
*target* syntax of the convergence decisions (`rec`, `:=`, `(f=…)`
records, `λ`-lambdas, `Feed`/`Mut` wrappers, transactions) and are
pinned as expected compile-errors that go red one by one as the
direction lands; read them as the direction's worked examples, with
the same status caveats as the Direction notes they exercise.

---

## 12. Reserved for future work

The following are deliberately omitted from CHL today, in some cases
with parser-level support that lowering rejects:

- **`while` loops** — currently a parse error (the `while` keyword is
  not yet recognised). Tracked by
  [plan.md → Mutability → "while loop lowering"](plan.md).
- **Nested `for` loops with mutable variables** — a single-level
  for-loop accumulator works (§4.6), but mutation inside a nested loop
  is not yet lowered.
- **Generator body shapes** — a `def` containing any `yield` is a
  generator function semantically (§4.2), but today the compiler only
  accepts bodies that are exactly one top-level `for`. Top-level
  `yield`s, multiple sequential `for` loops, nested `for`s where the
  inner loop yields, and post-loop statements are all rejected
  pending support.
- **First-class functions in arbitrary positions** — see
  [docs/brainstorm/2026-03-05-first-class-functions.md](brainstorm/2026-03-05-first-class-functions.md).
- **Recursion** — self-reference in `def` is not yet wired through;
  self-referential *value* bindings get the explicit `rec` form
  (**[Decided]**, §4.3).
- **Imports / multiple files** — CHL is single-file today. If
  multi-file support lands, a real *module* concept (imports,
  namespaces) arrives with it — that is when the word "module" earns
  a place in this spec (§2.1 deliberately avoids it now).
- **Classes / `try`** — not in the language. `with` is not a keyword
  today but is claimed by the transaction design (**[Decided]**, §8) —
  it will not carry Python's general context-manager meaning.
- **Float arithmetic** — no `f64` type at the surface.
- **String operations** beyond `+` concatenation.
- **Surface refinement type syntax** — refinement types (§6) are
  inferred today only via built-ins like `groupby`; the decided
  surface form is `{x: T | p(x)}` (**[Decided]**, §6.1), not yet in
  the grammar.
- **Pattern matching** beyond tuple destructuring on assignment
  targets — a `match`/`case` form appears in the north-star `txn_kv`
  (**[Tentative]**, §1.6) but has no design writeup.
- **The term-level delimiter migration** — records `(f=1, …)`, maps
  `[k=v, …]`, `{…}` reserved for types (**[Decided]**, §2.4). Today
  the parser still classifies `{…}` by its keys (record vs. dict) and
  dict lowering is `Unsupported`; an earlier plan to move dicts to
  `[k: v, …]` is superseded by the map-literal decision.
- **Map/dict comprehensions** — not in the grammar; their surface form
  follows the map-literal decision above (**[Open]**).
- **The syntax convergence at large** — every **Direction** note in
  this spec (λ-lambdas §3.10, `:=`/`rec` §4.3, membership `in` §3.4,
  type wrappers §6.2, transactions §8, …) is unimplemented; the
  north-star programs pin the target and
  [docs/plan.md](plan.md) tracks the sequencing.

When each lands, this spec will be updated alongside the lowering and
the demo programs.

---

## See also

- [docs/design.md](design.md) — overall Cambra architecture.
- [brainstorm/2026-06-29-syntax-convergence.md](brainstorm/2026-06-29-syntax-convergence.md)
  — the syntax-convergence decisions folded into the Direction notes
  above.
- [src/chl_parser/design-chl-parser.md](../src/chl_parser/design-chl-parser.md) — the parser implementation.
- [src/ccl/design/](../src/ccl/design/README.md) — the CCL IR and the
  lowering/inference/optimization passes.
- [docs/operational-semantics/summary.md](operational-semantics/summary.md) — CCL's operational semantics.
- [docs/demo-programs.md](demo-programs.md) — runnable examples and their status.
- [docs/plan.md](plan.md) — roadmap for the planned features called out above.

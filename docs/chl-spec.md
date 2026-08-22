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
and keep data/control flow statically visible. The direction was recorded
in an internal design note (2026-06-29) and is embodied by the north-star programs in
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
  roadmap work.
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
and indentation are **ignored**. Multi-line list, tuple, record,
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
True   False
and    or     not
if     elif   else
for    in
def    return yield
with
match  case
pass
where
```

`where` is the refinement predicate separator (§6.4). It is lexed so the name is
**reserved** — refinements are not parsed yet, so every use is a parse error
today.

`with` is a keyword: it introduces a transaction block, `with begin():`
(§8.2). It does **not** carry Python's general context-manager meaning.

A lambda is written `\x -> body` (§3.10); `\` and `->` are punctuation
(§1.8), not keywords, so `lambda` is an ordinary identifier — it, along with
`while`, `class`, `import`, `try`, `except`, `as`, `global`, `nonlocal`,
`del`, `assert`, `raise`, `is`, are **not** keywords in CHL today. Some are
reserved for future use.

`match` and `case` introduce tag dispatch over a variant (§4.10).

> **Direction.** Planned binder/keyword vocabulary, not lexed today:
> `rec` (recursive binding — §4.3, **[Decided]**), `given`, `requires`,
> `summon` (the transactions-as-contextual-parameters layer — §8.7,
> **[Decided]**), `import` (built-in modules — the `http` module surface,
> **[Decided]**; general modules remain future work, §9), and `assert` and its
> `static assert` form (function contracts — §6, **[Decided]** as the
> surface, **[Open]** as to what `static` demands). Avoid taking these names
> for other purposes. (`with`, `:=`, `match`, `case` and `where` are
> **already** lexed — the first two carry today's transactions and mutation,
> §8, `match`/`case` carry tag dispatch, §4.10, and `where` is reserved ahead
> of the refinement syntax that will use it, §6.4 — so they are not in this
> list.)

### 1.7 Literals

| Form | Token | Notes |
|---|---|---|
| `0`, `42`, `1234` | `Int(i64)` | Decimal only; no `_` separators, no hex/bin/oct, no negation in the token (`-3` is `UnaryOp(Neg, 3)`). |
| `"hello\n"`, `'world'` | `String` | Double- or single-quoted. Escapes: `\n \t \r \\ \" \' \0`. Unknown escapes are preserved verbatim (the `\` is kept). No multi-line `"""..."""`, no f-strings, no raw `r"..."`. |
| `True`, `False` | `Bool` | |

There are no floating-point literals — CHL has no `f64` type at the
surface level.

### 1.8 Operators and punctuation

```
+  -  *  //  ++  ->  =>
&  |  ^
== != <  <= >  >=
=  += -= *= //=
:=
<<  <<=
(  )  [  ]  {  }  ,  :  .  ;  \  `
```

`:=` is the **mutation** operator (§4.3, §8.1) — it introduces and writes
a mutable variable. It is *not* Python's walrus operator: it is an
Algol-tradition assignment **statement**, and there is still no
assignment-as-expression.

**Notably absent vs. Python** at the lexical level: `/`, `%`, `**`, `>>`,
`~`, `@` (no matmul, no decorators), walrus assignment-*expressions*, and
`...`. The parser refuses these at the syntactic level rather than
parsing-then-erroring.

`++` is not a Python token at all: it is CHL's collection-union operator
(§3.3). There is no increment operator — `++` is always binary.

`\` introduces a lambda binder and `->` separates it from the body —
`\x -> body` (§3.10).

`=>` is the function-type arrow. It separates a `def`'s parameter list
from its return-type annotation — `def f(x: Int) => Int:` (§4.1), which
type inference checks against the body's value. It is also a general type
operator inside an expression: `T => U` is a function type, writable in
any annotation position (§6).

> **Direction.** `->` additionally becomes the pair / map-entry arrow
> (`a -> b` for a two-tuple, `[k -> v, …]` for a map literal — §2.4,
> **[Decided]**); the token is lexed today but that *use* is not yet
> parsed.

`` ` `` (backtick) prefixes a **variant tag**, in every position — type, term,
and pattern: `` `none ``, `` `some(1) ``, ``{ `some{Int} | `none }`` (§3.15,
§6.5). A tag is `` ` `` immediately followed by an identifier with no
intervening whitespace; tag names are lowercase, since a tag builds a *value*
and `Caps` means type (§6.1).

`|` is the logical-or operator in term position (§3.3) and additionally
separates the arms of a variant **type** (§6.5). The two never meet: a variant
type's arms are `` ` ``-tagged, and a refinement predicate — the one place a
term appears inside `{…}` — is introduced by `where` (§6.4), which is exactly
why the refinement separator moved off `|`.

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
                 |  mut_assign_stmt
                 |  aug_assign_stmt
                 |  define_stmt
                 |  expr_stmt

return_stmt     ::= "return" [ expression ]
pass_stmt       ::= "pass"

assign_stmt     ::= assign_target "=" expression
ann_assign_stmt ::= assign_target ":" expression "=" expression
mut_assign_stmt ::= assign_target [ ":" expression ] ":=" expression
aug_assign_stmt ::= assign_target aug_op expression
define_stmt     ::= assign_target "<<=" expression
expr_stmt       ::= expression

aug_op          ::= "+=" | "-=" | "*=" | "//="

assign_target   ::= ident
                 |  "(" assign_target ( "," assign_target )* [ "," ] ")"
                 |  assign_target ( "," assign_target )+ [ "," ]

compound_stmt   ::= if_stmt | for_stmt | with_stmt | def_stmt

if_stmt         ::= "if" expression ":" block
                    ( "elif" expression ":" block )*
                    [ "else" ":" block ]

for_stmt        ::= "for" assign_target "in" expression ":" block

with_stmt       ::= "with" [ ident "=" ] expression ":" block

def_stmt        ::= "def" ident "(" [ param ( "," param )* [ "," ] ] ")" [ "=>" expression ] ":" block
param           ::= ident [ ":" expression ]

block           ::= NEWLINE INDENT statement+ DEDENT
```

`assign_target` is a bare name or a nested tuple of names — **no
subscript or attribute targets** (`xs[0] = x` and `obj.f = x` are not
valid). Every binding LHS is therefore a static pattern: which names a
statement introduces is decidable from the syntax alone, without any
runtime evaluation.

`mut_assign_stmt` is the `:=` **mutation** statement (§4.3, §8.1),
introducing or writing a mutable variable, in bare (`x := e`) or annotated
(`x: T := e`) form; the annotation is the same position as
`ann_assign_stmt`, with `:=` in place of `=` selecting mutation. `+=` and
friends (`aug_assign_stmt`) are compound mutations and require a mutable
target — the mutability check is semantic (§8.1), not grammatical, so the
production is shared with pre-`:=` code shapes.

`with_stmt` is a transaction block (§8.2). Its context expression is any
`expression` in the grammar, but lowering accepts only `begin()` (with the
optional `ident "="` prefix binding the transaction handle — `with t =
begin():`, §8.2, `[Decided]`); any other context is rejected. `with` does
**not** provide Python's general context-manager statement.

> **Direction.** Planned statement forms, not in today's grammar:
> `rec x = e` recursive bindings (**[Decided]**, §4.3), annotation-only
> forward declarations such as `h: Feed(_)` with no initialiser
> (**[Decided]**, §3.7 — today an annotation *requires* a value), and
> out-of-line collection definition through a subscript target,
> `c[i] = v` (**[Tentative]**, §6.3 — this would relax the
> no-subscript-target rule above). (`mut_assign_stmt` and `with_stmt`
> above are already implemented — §4.3, §8; they are in the grammar, not
> this list.)

### 2.3 Expression precedence

From lowest to highest; all binary operators are left-associative unless
noted:

| Level | Operator(s) | Notes |
|---:|---|---|
| 1 | `\x -> …` (lambda), `yield` | prefix forms; non-associative |
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
| 15 | postfix: `f(args)`, `x[i]`, `x.attr`, `x.0` | left-fold |
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
       | "(" ")"                              -- the unit value, typed `{}` (§3.1, §6.6)
       | "(" expression "," ")"              -- one-tuple
       | "(" expression ( "," expression )+ [ "," ] ")"   -- tuple
       | "(" record_field ( "," record_field )* [ "," ] ")"   -- record value
       | "[" [ expression ( "," expression )* [ "," ] ] "]"   -- list
       | "[" expression comp_for ( comp_for | comp_if )* "]"  -- collection comprehension
       | "(" expression comp_for ( comp_for | comp_if )* ")"  -- collection comprehension (paren form)
       | "{" typed_ident ( "," typed_ident )* [ "," ] "}"   -- record type (§6.1)
       | "{" expression "," "}"                           -- one-tuple type (§6.1)
       | "{" expression ( "," expression )+ [ "," ] "}"   -- tuple type (§6.1)
       | "{" "}"                                          -- unit type (§6.6)

record_field ::= ident "=" expression
typed_ident  ::= ident ":" expression
comp_for     ::= "for" assign_target "in" expression
comp_if      ::= "if" expression
```

A record **value** is a parenthesised list of `name=value` fields:
`(x=1, y=2)`. The parentheses are the product constructor (§2.4 Direction),
shared with tuples — `(1, 2)` is a tuple, `(x=1, y=2)` a record, `(e)` a
parenthesised `e`, `(e,)` a one-tuple.

A `{...}` literal is **type** syntax (§6.1), never a term-level value: bare
identifier keys with `:` make a record type (`{x: T, y: U}`) and a colon-free
list makes a tuple type (`{T, U}`). A `{...}` in value position is a lowering
error pointing at the `(…)` form. (Finite maps are a collection, written
`[k -> v, …]` — §6.3 — not a brace form.)

**Braces in type position are always a product or a sum, never grouping.** Two
consequences, both enforced:

- A **one-element** tuple type carries the trailing comma — `{T,}` — exactly
  as the term-level one-tuple does (`(e,)`, §3.11). A comma-free `{T}` is a
  parse error pointing at `{T,}`: with no grouping reading available there is
  nothing else for it to mean, and requiring the comma keeps one spelling per
  type.
- An **empty** `{}` is the **unit type** (§6.6). It is not an empty tuple type
  and not an empty record type — those are not types at all; `{}` is simply how
  unit is spelled.

**What a brace group means is a classification over what it contains.** Every
form below is parsed except the refinement, whose `where` is lexed and reserved
but whose brace form has no production (§1.6, §6.4):

```ebnf
brace_type  ::= "{" typed_ident ( "," typed_ident )* [ "," ] "}"  -- record type
             |  "{" type "," "}"                                   -- one-tuple type
             |  "{" type ( "," type )+ [ "," ] "}"                 -- tuple type
             |  "{" "}"                                            -- unit (§6.6)
             |  "{" tag_type ( "|" tag_type )* "}"                 -- variant type (§6.5)
             |  "{" type "where" expression "}"                    -- refinement (§6.4)

tag_type    ::= "`" tagname [ "{" tag_fields "}" ]
tag_fields  ::= type ( "," type )* [ "," ]
             |  typed_ident ( "," typed_ident )* [ "," ]
tagname     ::= [a-z_] [A-Za-z0-9_]*
```

The forms are told apart by their first distinguishing token, so classification
never needs lookahead past one item:

| Contains | Form | Example |
| --- | --- | --- |
| a top-level `where` | refinement (§6.4) | `{Int where _ > 0}` |
| `` ` ``-prefixed items | variant type (§6.5) | ``{ `some{Int} \| `none }`` |
| `ident : type` items | record type | `{x: Int, y: Int}` |
| types, ≥2 or 1-plus-comma | tuple type | `{Int, Bool}`, `{Int,}` |
| nothing | unit (§6.6) | `{}` |
| one type, no comma | **error** — write `{T,}` | `{Int}` |

The backtick row sits above the error row and that ordering is load-bearing: a
one-arm variant type is a single comma-free item, so classifying it as a tag
first is what keeps `` {`a} `` from being read as a malformed `{T,}`.

A top-level `where` wins over every other reading and takes the rest of the
brace group as its predicate, so `{T where p | q}` refines `T` by `p | q` (§3.3)
rather than declaring a variant.

**A tag's braces are its payload type's own braces, elided** (§6.5). A record
payload is `` `some{a: Int} ``, a tuple payload `` `some{Int, Bool} ``, and
doubling the braces — `` `some{{a: Int}} `` — is rejected, which is what keeps
one spelling per type. Every brace form above reads the same inside a tag as
outside it, including the one-tuple's comma: `` `some{Int,} `` stores `{Int,}`.

The one form that differs is the one a standalone type has no reading for. A
comma-free `{T}` is a parse error above, so inside a tag those braces are free to
be the **tag's** — `` `some{Int} `` stores a bare `Int`, which is what makes
`` `some(1) `` its constructor. That is the elision: the braces you write are the
payload's whenever the payload has any, and the tag's when it does not.

> **Direction — term-level delimiters [Decided].** The three
> delimiters split by role
> (2026-06-29 §1):
>
> | Delimiter | Role | Examples |
> | --- | --- | --- |
> | `( … )` | product **terms** | tuple `(1, 2, 3)`, record `(f1=1, f2=2)` |
> | `[ … ]` | **collections** — definition *and* lookup | list `[1, 2, 3]`, map `[k -> v, …]`, indexing `counts[word]`, `xs[0]` |
> | `{ … }` | structural **types** | tuple type `{T, U}`, record type `{f: T}`, variant type ``{ `some{T} \| `none }``, refinement `{T where _ > 0}` |
>
> Under that scheme `{…}` never appears at the term level: record values are
> written `(name=e, …)`, and finite maps are collection literals
> `[k -> v, …]` (**[Decided]**).
>
> Map entries use `->`, not `=` (**[Decided]**). `a -> b` is **pair
> syntax** — sugar for the two-tuple `(a, b)`, valid in construction
> (`let x = 1 -> 2`) and in patterns (`for k -> g in m`, §7.2) — so a
> map literal is a collection of entry pairs, matching the
> collections-are-functions model (§6.3). It also keeps the two
> operators' binding disciplines distinct: the left of `=` is always a
> *definition target* (a name, a record field label, a collection
> point `c[i]`), while the left of `->` is an *evaluated key
> expression*. And it removes a one-character trap: `[x = 5]` (map)
> vs `[x == 5]` (one-element list of `Bool`). Three earlier sketches
> are superseded: map entries as `[k: v, …]` (`:` is settling on
> annotation/type duty), as `[k=v, …]` (which read as keyword
> arguments), and Unicode `[k ↦ v, …]` (CHL is ASCII-only —
> §1.8). Still **[Open]**: the spelling of an *empty* map under the
> new scheme. The record-syntax / call-argument interaction is
> resolved by the functions-take-one-product-argument direction
> (§3.8): `f(x=1)` *is* `f` applied to a record — keyword arguments
> and record arguments are the same thing.

---

## 3. Expression semantics

Each CHL expression denotes a value; some expression forms additionally
perform an **effect** when evaluated. The effecting forms:

- **Feed `<<`** (§3.7) appends its right-hand side to a deferred
  collection.
- **`yield`** (§3.13) appends its operand to the deferred collection the
  enclosing generator function returns.
- **A call to an effecting function** — one that writes a `Mut(…)`
  parameter (pass-by-reference, §6.2) or writes a transactional mutable variable
  inside a `with begin():` block (§8) — performs that function's writes.
  A function's effects are always visible in its signature (a `Mut(…)`
  parameter, or a write to a `Txn` variable in its body); there are **no
  implicit-effect functions**, so an inert expression statement (§4.9)
  stays detectable and rejected.

Mutation of a *variable* is a property of statements, not expressions:
`x := e` (§4.3, §8.1) writes a mutable variable, and loop accumulation
(§4.6) and transactions (§8.2) are the statement contexts that give those
writes their sequencing. A bare *reference* to a mutable variable is a
pure read — a dereference of its current value; the effect is carried by
the `:=` write and the effecting call, never by the read.

Every other expression form is *pure*: it depends only on its inputs and
has no observable effect. A pure expression is safe to evaluate zero,
one, or many times, and it is only over pure sub-expressions that the
freedoms below (unordered collections, unspecified evaluation order)
apply. Ordering *between* effects is not free-for-all: it is governed by
the dependency-edge model of §8.5 — effects are ordered exactly by the
data dependencies among them, and unordered (freely interleaved)
otherwise.

> **Direction [Decided].** The `requires Transaction` / `given` / `summon`
> contextual-parameter layer (§8.7) adds a *second* way for a call to be
> effecting — a function that manifests a transaction from context rather
> than through a `Mut(…)` parameter. That layer is not yet implemented;
> the `Mut(…)`-parameter and `with begin():` effecting-call forms above
> are.

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
**loop-carried accumulator** (§4.6): a `:=` write to an outer-scope name
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

Most CHL expressions are *pure* (see the effect inventory above): a pure
expression has no observable effect, so the order in which the
sub-expressions of a compound expression evaluate is **not specified** by
this document. Argument evaluation order in a call, operand order in a
binary operator, the relative order of two independent feeds in the same
loop body — none of these are sequenced. The append effects (`<<`,
`yield`) contribute to bag-valued deferred collections and commute, so
they too impose no order among themselves beyond data dependencies. The
one place order *is* observable — effecting calls and transactional
writes — is governed by the dependency-edge model of §8.5, not by source
position.

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
map key, division by zero, integer overflow. Where this document says
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

`Int`, `String`, and `Bool` literals denote themselves, and `()` is the literal
for the unit type `{}` (§6.6).

A literal's **type says which literal it is**, not merely its base: `5` has type
`{Int where _ == 5}` (§6.4), the refinement pinning that one value. So `x = 5`
gives `x` the type `Int@5`, and it keeps that unless a binder discards it:
`x: Int = 5` binds `x` at `Int` (an exact annotation *is* the binder's type),
while `x <: Int = 5` leaves `x` at `Int@5` (a bounded annotation only has to admit
the value) — see
[Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded). Any
operation that computes a *new* value drops it, since it is a fact about one
value and not about the operation: `x + x` is an `Int`, and a mutable variable
never takes it (a mutable variable is the sequence its writes produce, so no one write's
value describes it). Unit is the exception with nothing to say: it has one
inhabitant, so pinning it would add nothing to the base.

> **Direction [Decided] — `true`/`false`.** The boolean literals are spelled
> `True`/`False` today, the one exception to the capitalization rule above. They
> are renamed to `true`/`false`, which is not yet implemented: a boolean literal
> is a *term*, so `Caps` becomes exceptionless.

### 3.2 Names

A name refers to the value bound by the nearest enclosing scope
(parameter, lambda parameter, assignment, or function definition).
Name resolution is purely static — there is no dynamic lookup, no
introspection of the binding environment.

Forward references are not allowed: a name must be in scope at the
point of use. Mutual recursion between top-level functions is
**[Planned]** — see the 2026-03-05 recursion design notes.

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

> **Direction [Tentative] — `Real` and `/`.** The target language has a
> fractional type, `Real`, and a division operator `/` on it. Neither
> exists today: `Real` is no type the checker knows, `/` is not lexed
> (§1.8), and there is no fractional literal (§1.7), so a quantity that
> wants a fraction has nothing to write it with. Everything else is
> **[Open]** — what `Real` denotes (exact rationals, a decimal, or the
> `f64` §12 rules out), whether `/` is total or partial at zero
> (*Partiality*, §3), whether `//` survives beside it, and how an `Int`
> literal acquires the type in a `Real`-typed position.

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

> **Direction [Decided].** Planned membership *expressions*: `e in s` tests set membership, `k in m` tests for a key
> in a map (2026-06-29 §2).
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
denotes. The expression itself returns the unit value `()`; its
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
> (2026-06-29 §5; the
> north-star `fanout` program is the worked example). This vocabulary
> supersedes the `deferred`-introducer sketch from the 2026-04-23
> sink-operators design notes.
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
target[index]    -- subscript: list element or map lookup
target.attr      -- attribute: record field by name
target.0         -- attribute: tuple field by position
```

- **Subscript** on a list with integer index `i` denotes the i-th
  element (0-based). An out-of-range subscript is a compile-time type
  error when statically known; otherwise the expression is not
  defined (see *Partiality*, §3).
- **Subscript** on a map with key `k` denotes the value associated
  with `k`. Looking up a missing key is not defined (see *Partiality*,
  §3).
- **Attribute** denotes the value of a field of a product (§3.11),
  keyed either by **name** (`r.age`, on a record) or by **position**
  (`t.0`, on a tuple). The field must exist; a missing one is a
  compile-time type error. An identifier cannot begin with a digit, so
  the two forms never collide. The forms compose freely, since they are
  one operation differing only in the key: `r.p.1`, `t.0.b`.

Lists and maps denote *finite functions* from their index domains
(`UInt`, `K`) to their element / value type, so a subscript is
"evaluate the finite function at a point" — the same operation as a
call, `c[k]` and `c(k)` alike.

**`[…]` is lookup and `.` is projection — they are not
interchangeable.** A product is heterogeneous, so it is not a finite
function and has no domain to look up in: `t[0]` is an error pointing
at `t.0`. Conversely `.` does not index a collection. The distinction
is by *spelling*, not by whether the index happens to be a literal, so
the meaning of `xs[0]` does not depend on what `xs` turns out to be.

> **Direction [Tentative].** The collections sketch
> (2026-06-29 §2, §6.3
> below) makes partial lookup total by returning an option: `lst[i]`
> and `map[k]` have type `Option(T)` (matched with `` `some(v) `` /
> `` `none ``, §6.5, as in the north-star `txn_kv`), while `Array` lookup stays direct
> (`arr[i]: T`) because its bounds are statically checked. That would
> eliminate the not-defined lookup cases above (see *Partiality*, §3).
> A `FullMap` is the map's version of `Array`'s escape from the option
> (§6.3): its domain *is* the key type, so `m[k]: V` directly.

### 3.10 Lambda

```
\x -> body
\x, y, z -> body
\x: T -> body                    -- typed parameters [Planned]
\ -> body                        -- zero-arity
```

`\` introduces the binders and `->` separates them from the body — e.g.
`groupby(sales, \r -> r.region)`. A lambda denotes an anonymous function
value; applying it to a tuple of argument values gives the value of `body`
in an environment where each parameter is bound to its corresponding
argument positionally.

Like `def`-defined functions (§4.1), lambdas are uncurried: an n-arg
lambda consumes all n arguments at once and is invoked through an
n-arg call.

Parameters are bare identifiers today. Because `->` (not `:`) terminates
the binder list, `:` is free for a per-parameter annotation `\x: T -> body`
(**[Planned]** — not yet parsed); refinement annotations are likewise not
writable, though some built-ins (e.g. `groupby`, §7.2) produce refined
lambdas internally. `\x -> x -> 1` (a lambda returning a pair, §2.4) is
unusual but unambiguous — the first `->` closes the binder, the rest is
body.

### 3.11 List, tuple, record literals

| Form | Denotes |
|---|---|
| `[]`, `[e₀, e₁, …]` | A finite list — an indexed bag of elements. The element at integer index `i` is `eᵢ`, but iteration order is unspecified (§3). Element types must unify. |
| `(e,)`, `(e₀, e₁, …)`, `e₀, e₁, …` | An anonymous heterogeneous product (tuple). Element types may differ. Tuples are positional, not unordered: `(1, 2)` and `(2, 1)` are distinct values. |
| `(name=e, …)` | A record (named-field product). Field names are bare identifiers; field types may differ. The parentheses are the product constructor, shared with tuples (§2.4). |

A trailing comma is allowed in every form (and required to disambiguate
`(e,)` from `(e)`).

**One-element products carry the comma at both levels.** The same rule holds
for the tuple *type*: `{T,}` is the one-element tuple type, and the comma is
what distinguishes it (§2.4) — a comma-free `{T}` is a parse error. Only
*tuples* need it: a one-field record needs no comma at either level, since
`name=value` (`(a=1)`) and `name: T` (`{a: Int}`) already mark the form.

**Tuple vs. record.** Both use `( … )`: a comma-list of bare expressions is
a tuple (`(1, 2)`), a comma-list of `name=value` fields is a record
(`(x=1, y=2)`). `(e)` (no field, no trailing comma) is a parenthesised `e`.
Both are projected with `.` (§3.9), keyed by position for a tuple (`t.0`)
and by name for a record (`r.x`); neither is subscripted.

**Records are not braces.** `{...}` is type syntax (§6.1) — a record *type*
`{name: T}` or a tuple type `{T, U}`. A `{...}` in value position is a
lowering error. Finite maps are a collection literal `[k -> v, …]` (§6.3,
**[Decided]**), not a brace form.

**Empty forms.** `()` is the unit value (§3.1) — there is no zero-field product
distinct from it, so it is equally what an "empty record" would denote. Its type
is the unit type, written `{}` (§6.6). `[]` is the empty list.

> **Direction [Decided].** The literal forms migrate with the
> delimiter split (§2.4) and the collections model (§6.3), form by
> form:
>
> | Today | Target |
> | --- | --- |
> | `(1, 2)` — tuple | unchanged: `( … )` is the product constructor |
> | `(name=e, …)` — record | a record is a product with named fields (and a call's keyword arguments are exactly such a record — §3.8) |
> | finite map | `[k -> v, …]` — a collection of entry pairs (§2.4); `[ … ]` is the collection delimiter |
> | `[1, 2, 3]` — list | same spelling, but shared across collection types: the literal can denote an `Array`, `List`, or `Set`, disambiguated by annotation or usage, with `list([…])` / `set([…])` constructors for explicitness (**[Tentative]** — §6.3) |
> | empty record / unit | `()`, the unit value: with no fields there is nothing to tell a record from a tuple, so an empty record, an empty tuple, and unit coincide (§3.1, §6.6) |
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
accumulator forces sequencing. The expression itself returns `()`;
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

### 3.15 Variant constructors

A **variant** is a tagged sum. `` `tag(e) `` injects `e` at tag `tag`; the
bare form `` `tag `` (equivalently `` `tag() ``) injects `()`, the value that
carries no information (§3.11). How a variant *type* is written is §6.5;
matching one is §4.10.

A tag carries exactly **one** payload, and the parens after it are the ordinary
product-term parens (§3.11), so a constructor reads like a call whose argument is
the product its values form (§3.8):

```python
x = `some(1)
y = `none
z = `ok(1, 2)       # one payload: the tuple those two values form
w = `pt(x=1, y=2)   # ... or the record, as with a call's arguments
u = `one(1,)        # the comma is the one-tuple's, as everywhere else
```

Variants are **structural**, exactly as records are: a tag has no
declaration and no owner. `` `some(1) `` has the one-tag type
`` {`some{Int}} ``, and *width subtyping* — the dual of the record rule —
lets it flow into any variant type whose tag set contains it, so the same
value is usable as an `Option(Int)`. Two consequences worth stating
outright:

- There is **one flat space of tag names**. The same spelling means the
  same tag everywhere, so `` `ok(1) `` written in two unrelated places
  denotes the same tag. They are still independent *values*; they
  interact only if they meet in one variant type, where their payloads
  must agree.
- A tag's payload type is fixed by **where the tags meet**, not at the
  constructor. `` `ok(1) `` and `` `ok("s") `` are each fine alone; if both
  flow into one variant, the mismatch is reported where they join.

This is the polymorphic-variant model, and the **backtick** plays the role
capitalization plays in languages that capitalize constructors. Tags are
structural and undeclared, so name resolution cannot tell `some(v)` from a
call to a function named `some`, nor bare `none` from a variable read. The
backtick resolves that, and it is the *same* mark in every position — term,
pattern (§4.10) and type — so a tag never has to be recognised from
context.

A constructor is an ordinary atom, so it takes a postfix chain:
`` `some(r).x `` is the attribute `x` of `` `some(r) `` (§3.9).

An annotation may write the arms out or use the `Option(T)` abbreviation, and a
constructor flows into either:

```python
x: {`some{Int} | `none} = `some(1)
y: Option(Int) = `some(1)
z: {`ok{Int} | `err{String}} = `err("nope")
```

> **Direction [Tentative].** A variant type can be *written* but not yet
> *named*: tags have no declaration site, so a misspelled tag is caught only
> where it fails to meet its counterpart, and a constructor's payload arity is
> not checked at the constructor. The planned refinement is the structural type
> alias of §6.1 — `` Option(T) = {`some{T} | `none} ``,
> `` Result(T) = {`ok{T} | `err{String}} `` — which gives a tag a resolution
> site and checks the payload there. It would also replace the
> built-in `Option(T)` above with a prelude definition. An alias is still
> structural: it names a shape, so two aliases with the same tags are the same
> type. Nominality is the separate `type` declaration direction (§6.1).

---

## 4. Statement semantics

A CHL **program** is its top-level block (§2.1): a sequence of
statements. Each non-terminal statement either introduces a binding
visible to the remainder of the block, or performs an effect (a feed
into a deferred output). The block's *value* is the value of its final
expression statement; if the program mutable variables any sinks (e.g.
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

Annotation types are arbitrary expressions evaluated in the
surrounding scope. `p: T` fixes the parameter's type at `T`; `p <: T`
leaves it inferred and bounded above by `T` (see [Two annotation
forms: exact and bounded](#two-annotation-forms-exact-and-bounded)).
The two forms may be mixed across a parameter list. A return-type
annotation, introduced by `=>`, specifies a fixed output type for the
function. The inferred type of the function body must be a subtype of
the annotated output type.

```python
def f(x: Int, y: Int) => Int:
    return x + y
```

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

> **Direction.** The read-only-*capture* rule is today's language:
> mutation already crosses a function boundary, but through a `Mut(…)`
> **parameter** (pass-by-reference — implemented, §8.1, §6.2), not by
> capturing and writing an outer name. The **[Decided]** extension lets a
> function mutate *captured* state whose type carries the wrapper — as the
> north-star `txn_kv`'s `put` does to the top-level
> `store: Mut(Map(…), Txn)`. Either way the capability is visible in the
> types at the binder, not smuggled in.

`=>` is the function-type arrow, so a `def`'s signature has an equivalent
binding form: `f: (T => U) = \t -> …` binds `f` to a lambda checked against
the function type `T => U` (§6), the same type `def f(t: T) => U:` gives it.
Recommended style annotates both parameters and the return type on top-level
`def`s; the north-star programs follow it.

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
| `target = value` | Evaluate `value`, bind it to `target` as an **immutable** binding for the rest of the enclosing scope. Never mutates. |
| `target: T = value` | Same, additionally checking that `value` has type `T`. |
| `target := value` | **Mutation** (§8.1): introduce (the first `:=`) or write a mutable variable. It is `:=`, not any annotation, that makes a variable mutable; transactional mutable variables are always introduced this way (`x: Mut(V, Txn) := …`). |
| `target op= value` | Compound mutation — `target := target op value`, for `op` ∈ `+ - * //`. The target **must** be a mutable variable (one introduced with `:=`); a `+=` to an immutable binding is a type error, not a silent rebind. |
| `target <<= value` | Resolves a previously-deferred name to `value` (§4.4). |

`target` is an `AssignTarget`: a bare name or a (nested) tuple of bare
names. Tuple destructuring:

```python
a, b = pair
(x, (y, z)), w = nested
```

is supported at any nesting depth.

> **Direction [Tentative].** Destructuring targets generalize: any
> tuple-yielding expression can be destructured wherever a target
> appears — assignment and `for` binders alike — and `k -> v` pair
> patterns (§2.4) join tuple patterns. Today's grammar special-cases
> the `reqs, resps = http_serve(…)` statement form (§7.4); that is an
> implementation restriction, not a design one. The decided pattern
> surface is §4.3.1.

**No assignment-as-expression** — neither `=` nor `:=` is an expression
(the mutation `:=` is a statement, §1.8). **No multi-target chained
assignment** (`a = b = c` is not in the grammar).

Annotated assignment **requires** a value (`x: T` alone is a parse error,
unlike Python's bare type-only declarations).

A `:=` write to a name introduced *outside* a `for` loop is a
**loop-carried accumulator** update (§4.6); inside a `with begin():` block
it is a transactional write (§8.2). A plain `=` never mutates — reusing a
name with `=` in the same scope is immutable shadowing (§5), and a plain
`=` to an outer-scope name *inside* a loop body is rejected, pointing at
`:=` (§4.6). The model behind every `:=` is **temporal functional
mutation** — a mutable variable is a pure function from a time domain to
values, and a write reveals one more position of it (§8.1, and
[src/ccl/design/mutability.md](../src/ccl/design/mutability.md)).

> **Direction — `=`, `rec` [Decided].** `:=` and its compound forms are
> **implemented** (§8.1); the rest of the target binding model is still
> [Decided]. That model (2026-06-29 §3) splits bindings along two axes:
> plain `=` is reserved for *timeless equations* — `x = e` asserts
> `x ≡ e` with no before/after — with `:=` (already in place) as the
> **time** axis and a new marker `rec` as the **self-reference** axis:
>
> - **Self-reference → `rec`.** A self-referential *value* binding must
>   be marked: `rec reach: Set({src: Int, dst: Int}) = … reach …` solves
>   the equation as a least fixpoint (see the north-star `reachability`).
>   `rec` stays in the timeless `=` world — a fixpoint is a value, not a
>   mutation. Unmarked value self-reference is a compile error; `def`
>   self-reference and recursive types need no marker.
>
> **[Open]**: whether same-scope *shadowing* (`x = 1` then `x = 2`, legal
> today per §5) survives once `=` reads as a timeless equation — two
> equations for one name in one scope contradict the reading, but the
> brainstorm doesn't address it.

#### 4.3.1 Destructuring patterns

**[Decided]** — the surface below is decided and not implemented; see the end of
this section for what today's grammar accepts.

A binding LHS is a **pattern**: a shape that names the parts of the value
being bound. Patterns appear in three positions — an assignment target
(§4.3), a `for` binder (§4.6), and a `case` arm (§4.10) — and the same
grammar serves all three.

```ebnf
pattern      ::= ident
              |  pattern ":" type                              -- annotated
              |  "(" pattern ( "," pattern )* [ "," ] ")"       -- tuple, parenthesised
              |  pattern ( "," pattern )+ [ "," ]               -- tuple, bare
              |  "(" field_pat ( "," field_pat )* [ "," ] ")"   -- record
              |  "`" tagname [ "(" pattern ( "," pattern )* [ "," ] ")" ]  -- variant (§6.5)
              |  "_"                                            -- wildcard

field_pat    ::= ident "=" pattern
```

The forms mirror the term-level constructors exactly (§3.11): a pattern is
written the way the value it matches is written, with binders where the
value has sub-values. That includes the delimiters — patterns are terms, so
they use `( … )` and never `{ … }`, and a variant pattern uses parens for
its fields even though the variant *type* writes them in braces
(`` case `some(x) `` against `` `some{Int} ``).

**Annotations ride any node, and `:` binds tighter than `,`.** A pattern
component may carry its own type, so the annotation sits wherever the
type is worth stating:

```python
(x, y): {Int, Int} = z           # one annotation on the whole tuple pattern
x: Int, y: Int = tuple           # one per component; no parens needed
(x=x2, y=y2): {x: Int, y: Int} = r   # record fields rebound to x2, y2
`some(x): {`some{Int}} = y       # variant pattern, single-tag variant type
```

Because `:` binds tighter than `,`, `x: Int, y: Int` above parses as the
two-component tuple pattern `(x: Int), (y: Int)` rather than binding `x`
to a type that swallows the comma. That is what makes the parens optional
on an annotated bare tuple pattern, and it is the same precedence a
`def` parameter list (§2.2) and a record type (§2.4) already read by.

A **record** pattern's `field=binder` mirrors the record value's
`field=value`: the left of `=` is the field being projected, the right is
the pattern it is matched against. `(x=x2)` therefore binds field `x` to
the name `x2`; `(x=x)` is the same-name case and has no shorthand.

Patterns are still **static** — which names a binding introduces is
decidable from the syntax alone (§2.2). A variant pattern is the one form
that can *fail* to match, which is why it only appears in a `case` arm or
against a single-tag variant type, where the match is exhaustive.

Today's grammar accepts only the tuple forms, unannotated, with the
annotation restricted to the whole target (`ann_assign_stmt`, §2.2);
record, variant, wildcard, and per-component annotations are all
unimplemented.

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

**Loop-carried accumulators.** A `:=` write (§4.3, §8.1) to a name
introduced *before* the loop — a pre-loop `:=`, a function argument, or
any binding from an enclosing frame — is an **accumulator update**, not a
per-iteration shadow. It introduces an inter-iteration data dependency
that **forces the loop to run sequentially** in the order the dependency
requires:

- Before the loop, the name has its outer value.
- At each iteration, the body computes a new value from the
  previous-iteration's value and the current element.
- After the loop, the name holds the value at the final iteration (or, if
  the source was empty, the outer pre-loop value).

Loops are parallel by default (above); an accumulator is what serialises
them. A loop with multiple accumulators is still a single sequential loop —
the dependencies advance in lockstep with the iteration.

```python
acc := 0
for i in [1, 2, 3, 4, 5]:
    acc := acc + i
acc                              # 15
```

Multiple accumulators are supported (one per outer name written with
`:=`); their updates within an iteration are ordered by their data
dependencies, so a later update may refer to an earlier accumulator's
just-computed value. The same covers generator functions with loop-carried
state (`total := 0; for x in xs: total += x; yield total`).

Accumulation **requires `:=`**. Because a plain `=` never mutates, a plain
`=` to an outer-scope name inside a loop body is a lowering error — left to
mean anything it could only be a silently-discarded per-iteration shadow,
never an accumulator:

> `assignment to X is mutation: X is bound outside the for-loop body
> (function argument or pre-loop binding). `=` binds immutably; to mutate
> a mutable variable, introduce it with `:=` before the loop and write it
> with `X := …` or `X += …``

A plain `=` whose target is a **fresh** name (not introduced in an outer
frame) is unaffected: an ordinary per-iteration binding, in scope for the
rest of that iteration and gone at the next.

The converse also holds: a mutable variable must be introduced **before**
the loop that accumulates it. A `:=` inside a loop body whose target is not
an already-declared accumulator is a lowering error, at every spelling —
`y := 0`, `y: Mut(Int) := 0`, and `y: Mut(Int, Txn) := 0` alike, since
whether an introduction carries a type annotation says nothing about
whether it introduces a mutable variable. A mutable variable scoped to one iteration would need
the loop's own iteration extent as its sequencing domain, which is the
nested-recurrence case below:

> `Y is a mutable variable introduced inside a for-loop body, which is not
> supported: declare it before the loop (`Y := …`) so its updates carry
> across iterations, or bind a per-iteration value immutably with `Y = …``

The same holds for `op=`, which is a mutable write and not a rebind: `x += e`
inside a loop body requires `x` to be a mutable variable declared before the
loop. A target that is not gets the matching error rather than a
per-iteration binding.

Falling back to a per-iteration binding is deliberately *not* what happens in
either case, for the reason a plain `=` to an outer name is rejected: it would
silently discard every update at the iteration boundary, which is the one thing
`:=` exists to rule out. For `op=` it is worse than a lost update — `op=` reads
the old value, so a per-iteration rebind reads the binding's *initial* value on
every iteration.

*Currently unsupported* (see §12): nested for-loops with mutable
variables, mutable variables introduced inside a loop body or a `with
begin():` block, and `while` loops.

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
return                -- equivalent to `return ()`
return expression
```

`return` produces the enclosing function's result. CHL has no early
exit: `return e` is only meaningful as the **last** statement of a
function body, or as the last statement of each branch of a terminal
`if`/`else`. A `return` followed by further statements is rejected —
the "return early, fall through otherwise" idiom must be written
explicitly as `if cond: return e\nelse: <rest>`.

### 4.9 Expression statement

A bare expression `e` is a statement. The expression is evaluated; if it
appears as the **last statement** of a block, its value is the block's
value. If it appears elsewhere, it must **have an effect** — a feed
(`target << value`), or a call to an effecting function (one that writes a
`Mut(…)` parameter or a transactional mutable variable, §8) — otherwise the
statement is inert and is rejected.

This rules out Python's "expression for its side-effect" idiom for any
effect *not* visible in a function's signature: CHL has **no
implicit-effect functions**, so whether a bare call is a legitimate effect
statement or an inert mistake is decidable from the callee's type.

> **Direction [Decided].** The `requires Transaction` / `given` / `summon`
> contextual-parameter layer (§8.7) adds a further kind of effecting call —
> a function that manifests a transaction from context rather than through
> a `Mut(…)` parameter (`put(req.body.key, req.body.value)` in the
> north-star `txn_kv`). It is not yet implemented; the effect rule above
> already covers the implemented `Mut(…)`-parameter and `with begin():`
> effecting calls.

---

### 4.10 `match` — tag dispatch

`match` dispatches on the tag of a variant. It is a **block statement**,
mirroring `if` (§4.5): each `case` names a tag and optionally binds its
payload for that arm's block.

```python
match x:
    case `some(v):
        v + 1
    case `none:
        0
```

A pattern spells its tag exactly as a constructor does (§3.15), so an arm
reads as the inverse of what it matches. Three payload spellings make two
statements:

| Pattern | Means |
|---|---|
| `` case `tag(v): `` | the tag carries a payload; bind it to `v` |
| `` case `tag(_): `` | the tag carries a payload this arm does not read |
| `` case `tag: `` | the tag carries **nothing** |

A binder is an ordinary local, scoped to its arm. `_` is the unused-binder
spelling and not a name, so the body cannot refer to it. `case _:` uses `_` in
the same sense, for an arm that names no tag.

**The third form states the payload's type rather than eliding the binder.**
`` `some{Int} `` and `` `some `` are different types (§6.5), so `` case `some: ``
matches a payload-less `` `some `` and is an error against one carrying an
`Int`. An arm that has a payload and does not read it is written
`` case `some(_): ``.

The default arm below takes no backtick: `_` is the absence of a tag, not a
tag.

Like `if`, a `match` is value-yielding by position: where a value is
required (a function body, the program value), every arm's block must end
in a value-yielding statement.

**Each tag is handled by exactly one arm.** Two arms for one tag is an
error — the arms *partition* the scrutinee's tags, so first-match never
arbitrates and arm order is not observable. A per-arm guard would change
that: two arms could then name one tag and be told apart by their guards,
which is order-sensitive. Guards are a **[Tentative]** direction (see the
note at the end of this section), so the partition rule is stated for the
guard-free language of today.

**`case _:` is the default arm**, matching whatever the tagged arms did
not. It binds no payload — the tags it covers have different payload
types, so there is nothing single to bind — and it must be the **last**
arm, since an arm after it could never be selected. At most one is
allowed.

A `match` whose *only* arm is the default names no tag, so it dispatches
on nothing: its value is that arm's, whatever the scrutinee is. It is
legal and says nothing about the scrutinee's type — which therefore need
not be a variant. The scrutinee is still an expression in scope and is
type-checked as one.

Patterns are **shallow**: an arm matches one tag and binds the whole
payload, with no nesting, no literal patterns, and no per-arm guard.

A `match` is not yet accepted **inside a `for`-loop body**, which admits
only assignments, `<<` feeds, `yield`, `if` guards, `with begin():` blocks
and bare calls. Dispatching per element is written as a `def` that matches
on its parameter and is called from the loop or a comprehension, which is
the same first-match rule reached through a call.

> **Direction [Tentative].** What is missing is a **one-line** spelling, not
> expression-ness: a `match` in a value position yields a value as an `if`
> chain does (§4.5). The candidate spelling is the block with its line breaks
> removed — `` match scrut: case `foo(x): x case `bar(y): to_x(y) `` — where
> `case` delimits the arms, so no separator is needed. It waits on a one-line
> block rule, which no block statement has today (`if c: x` does not parse
> either), so the rule to settle is layout's rather than `match`'s. Tuple
> destructuring on assignment targets (§4.3) is unaffected and remains the
> only other pattern-like form.
>
> `_` is accepted as an unused binder in a **pattern payload** only.
> Extending it to every binder position — a lambda parameter, a `for` target,
> a tuple destructuring slot — is **[Tentative]**. It needs a written rule for
> what distinguishes `_` in a type position (§2.4, where it means "infer this")
> from `_` in a binder position; position decides it, and nothing states so.
>
> A per-arm guard (`` case `some(v) if v > 0: ``) is the natural next
> addition — the IR already carries a guard alongside each arm's pattern —
> and needs a *tag-test* predicate term so the arm's gate can combine "is
> this tag" with the guard. It also relaxes the one-arm-per-tag rule above:
> two arms may then name one tag, and arm order becomes observable between
> them.

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
   final iteration" to bind it to, because iterations are unordered and
   may run in parallel (§3, §4.6). This is a deliberate divergence from
   Python's leaky-loop-variable behaviour. Any value the loop needs to
   produce for downstream code must be carried out via a loop-carried
   accumulator (§4.6) or yielded into a deferred collection.

A binding form (`=`, annotated `x: T = e`, `:=` (mutable introduction —
§8.1), `<<=`, `for`, `def`, `lambda`, comprehension `for`) introduces a
name for the rest of its enclosing scope. Re-binding the same name in the
same scope with `=` **shadows** (previous values are not recoverable);
re-writing a mutable with `:=` advances its history rather than shadowing
(§8.1). (Whether `=` shadowing survives the timeless reading of `=` is
**[Open]** — see §4.3.)

There is no `global` / `nonlocal` mechanism — closure capture is the
only way for a function to refer to outer names, and capture is
read-only.

---

## 6. Types (informal sketch)

This section is a sketch. The authoritative type system lives in
[`src/ccl/infer/`](../src/ccl/infer/) — see
[src/ccl/design/type-inference.md](../src/ccl/design/type-inference.md).
CHL types are inferred; a user-written annotation either *fixes* the
binder's type or *bounds* it — see
[Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded).

Built-in surface types. (The names below are this spec's vocabulary
for talking about the checker; annotations are writable on `def`
parameters and `x: T = e` bindings. As everywhere in this document,
an **unmarked** entry is accepted in annotation position today; a
marked one carries its status per "How to read this document".)

- `Int` — signed 64-bit integer.
- `Real` — a fractional number (**[Tentative]**, §3.3). The checker has no
  fractional type, there is no fractional literal (§1.7), and `/` is not
  even lexed (§1.8, §12).
- `Bool` — `True` or `False`.
- `String` — UTF-8 string.
- `{}` — unit type, one inhabitant, and its only CHL spelling (§6.6). There is
  no *empty* (uninhabited) type.
- `List(T)` — finite collection of `T`-values, indexed by `[0, n)`.
  The index → element mapping is part of the value (so `xs[i]` is
  well-defined); iteration order, however, is unspecified (§3). Written
  `List(T)` or `List(_)`.
- `{T₀, T₁, …}` — tuple type (structural `{…}` type syntax — §6.1). The
  one-element case is `{T,}`, with the comma required, and a comma-free
  `{T}` is a parse error (§2.4, §3.11). The zero-element case is `{}`
  itself — the unit type (§6.6).
- `{name: T, …}` — record type. Two records are the same type iff they
  have the same field names with the same field types.
- ``{ `tag₀{…} | `tag₁{…} | … }`` — variant type (§6.5). Two variants are the
  same type iff they have the same tags with the same payload types; the arms
  are a set, so their written order does not matter.
- `{T where p(_)}` — refinement type (§6.4), where `_` refers to the value being refined.
- `Mut(V)` / `Mut(V, Txn)` — mutable-variable / transactional-variable
  type (§6.2, §8).
- `Map(K, V)` — finite-map type. **[Planned]** — the map literal
  `[k -> v, …]` (§3.11) and `Map(…)` as an annotation are both
  unimplemented.
- `FullMap(K, V)` — *total*-map type (**[Tentative]**, §6.3): every value
  of `K` is a key, so lookup yields `V` rather than `Option(V)` and has
  no missing case. Not implemented.
- `Time` — a position in the commit order, what a transaction handle's
  `current_time()` answers (**[Tentative]**, §8.2). §8.2 calls the handle
  itself a `Txn` value, and the two spellings are not reconciled.
- `{T₀, T₁, …} ⇒ U` — function type. A function takes exactly one
  argument (§3.8): an n-parameter function's domain is the
  corresponding tuple type, and a keyword-argument function's domain
  is a record type — `{x: T, y: U} ⇒ V`. Surface syntax uses the `=>`
  arrow.

CHL also supports **refinement types**: a value of the refined type is
a value of the base type for which a predicate holds. Refinements are
inferred internally by built-ins like `groupby` (§7.2); the surface
form `{T where p(_)}` (§6.4) is writable in annotation position.

> **Direction [Decided] — function contracts.** A contract can be written two
> ways, and which one to reach for is a matter of the case at hand. As a
> **refinement type on an annotation** (§6.4), where it is part of the signature
> a caller reads: a parameter's precondition is `qty: {Int where _ > 0}`, and a
> postcondition is a return annotation, which may name the parameters because
> they are in scope there — `{Int where _ >= item.cost * qty}`. Or as an
> **`assert` in the body**, which suits a contract that falls out of the body's
> own logic: `assert qty > 0` lifts to the same refinement on `qty`. Asserts are
> not restricted to the top of a block — one anywhere refines the binders in
> scope from that point on, and one under a conditional contributes a
> path-sensitive refinement, which is what an annotation cannot express.
> Whichever surface writes it, what the checker holds is an ordinary refinement
> type, and call sites must discharge parameter refinements, so preconditions
> propagate outward: a refined parameter is an obligation on its caller, and the
> caller's own precondition an obligation on *its* caller, until the chain
> reaches whatever first admits the value from outside — a request handler, a
> file, a source. That **trust boundary** is where the check has to become real,
> and it is the parameter refinement, not a convention, that puts it there. For
> the HTTP boundary specifically, the sketch has the library derive the check
> from the handler's own signature rather than have every handler restate it
> (§7.4).
>
> Discharge is a spectrum, not a promise of static proof: an assert
> the compiler can prove is discharged at compile time and erased; one
> it cannot prove remains a runtime check. A planned `static assert`
> form (**[Open]**) demands compile-time discharge — failing the build
> when the proof doesn't go through — and may generalize to a
> constexpr-like marker forcing any statement to resolve at compile
> time. One further case: an assert whose subject is the value the body
> **returns** lifts to a refinement on the **codomain**, not to a
> parameter binder — it is a postcondition written as an assert, and it
> lands where a return annotation would.
>
> ```python
> def clamp(n: Int) => Int:
>     m = if n < 0:
>             0
>         else:
>             n
>     assert m >= 0        # ... so the signature reads => {Int where _ >= 0}
>     m
> ```
>
> This is the surface a *conditional* postcondition needs, which a return
> annotation cannot express: `clamp`'s two branches establish `m >= 0` two
> different ways (one trivially, one from the `else`'s own condition), and the
> assert states the bound once, after the branch, over the value both of them
> produce. Because the refinement lands in the signature, it also binds every
> later rewrite of the function — a reimplementation that violates it fails to
> typecheck against its own contract rather than against a test.
>
> Also **[Open]**: the precise placement and reference rules (what a
> pre- or postcondition may mention, which local an assert on the result
> names as its subject, how the lift renames it to `_`, where the lift
> draws its cut points) need elaboration; and *nominal* domain types
> carrying their own invariants (a `Price` whose `assert amount >= 0`
> rides the type instead of being repeated per function) are the agreed
> direction for factoring recurring contracts, with no syntax settled
> yet (§6.1, §6.4). Pinned by `discount_contract` (the mechanism in
> isolation), `nonneg_inventory` (data refinement plus guarded
> discharge), and `storefront` (both combined, plus the codomain lift
> under `static assert`).

The underlying type system additionally tracks unions, source types,
and inference variables; see
[docs/operational-semantics/](operational-semantics/) for the formal
treatment.

### 6.1 Direction: term/type syntax split [Decided]

(2026-06-29 §1.)

**Capitalization distinguishes term from type.** Lowercase heads are
terms; capitalized heads are types. Data *constructors* build values,
so they are lowercase — `` `some ``/`` `none ``, `` `ok ``/`` `err `` — and
only the type (`Option(T)`) is capitalized. `Caps` means *type*, without
exception (unlike ML and Rust, which capitalize constructors). Those
constructors are **variant tags**, so they additionally carry the `` ` ``
prefix in every position (§6.5); the capitalization rule is
what fixes their case, and the backtick is what marks them as tags rather
than ordinary names.

**Application is shared across levels.** `f(args)` is application
whether `f` is a value or a type constructor: `split(line)` and `ok(v)`
at the term level; `List(T)`, `Map(K, V)`, `Set(T)`, `Mut(V)` at the
type level. The head's case tells you which. Since Cambra is
dependently typed, a type constructor can take a *term* argument —
`Default(0, Nat)` — with no special bracket rule; in particular `[…]`
is **not** generic-argument syntax (it belongs to collections, §2.4).

**`{…}` is structural-type syntax** (§2.4): tuple type `{T, U}` (one
element `{T,}`), record type `{f: T}`, variant type
``{ `some{T} | `none }`` (§6.5), refinement `{T where p(_)}` (§6.4).

> **Direction [Tentative].** Named types come in two strengths. A
> plain `=` binding to a capitalized name is a structural **alias** —
> `Item = {price: Int, cost: Int}` — interchangeable with the type it
> names, and worked through in §6.7. A `type` declaration is **nominal** —
> `type Price = {amount: Int}` — distinct from every other type of the
> same shape. Nominal types are the agreed home for domain invariants
> (a `Price` carrying `assert amount >= 0` in its declaration, per the
> contracts direction in §6), so a contract states its ontology once
> instead of repeating asserts at every function; the declaration
> syntax for that invariant is not yet settled.

### Two annotation forms: exact and bounded

An annotation at a binder answers one of two questions, and the two
have different spellings because the answers differ.

> **Note — why these two spellings.** `<:` relates two *types* everywhere
> else, and here it sits between a term and a type. The capitalization
> rule (§6.1) is what makes that unambiguous rather than a pun: a
> lowercase head means the left side is a term, so `a <: T` reads "`a` has
> a type that is a subtype of `T`", while `A <: T` reads "`A` is a subtype
> of `T`". Which reading applies is settled by the case of the name, not
> by the operator.
>
> Exact gets the lighter spelling because it is the safer default, not
> because it is the more frequent intent. An annotation is written where
> the type is *not* obvious or where a contract is being fixed, and in
> both of those cases the more precise reading is the one to have by
> default. `<:` is then a deliberate opt-in: it loosens the contract and
> accepts inference whose result is harder to predict from the annotation
> alone.

`x: T` is **exact**: the binder's type *is* `T`. The initializer (or,
at a parameter, the argument) must be a subtype of `T`, and nothing
downstream of the binder sees more than `T`.

`x <: T` is **bounded**: the binder's type is *inferred*, with `T` as
an upper bound. The value's own type flows through; `T` only
constrains what may reach the binder.

Both forms are accepted wherever a binder is introduced — an
assignment (`x: T = e`, `x <: T = e`), a mutable introduction
(`x: Mut(V) := e`), and a `def` parameter — and mean the same thing in
each. `<:` does not appear **inside a type literal**: it says how an
annotation is read, and what it annotates is a term, so `{a <: Int}` is
not a record type. That is a restriction on type literals, not a claim
that a binder is the only place an annotation can go — an inline
annotation on an expression would carry both modes for the same reason a
binder does.

The two coincide only when the value's type already **is** the
annotation — when there is nothing for the annotation to discard. They
differ whenever the value's type is a *strict* subtype of it, which is
more often than it sounds, because a CHL type carries more than a base:

- **Width.** `x: {a: Int} = (a=1, b=2)` binds `x` at `{a: Int}`, so
  `x.b` is an error — the annotation is what discards the field.
  `x <: {a: Int} = (a=1, b=2)` binds `x` at the record's own type, which
  still has both fields, so `x.b` is `Int@2`.
- **Literal singletons** (§3.1). `i: Int = 0` binds `i` at `Int`;
  `i <: Int = 0` leaves it at `Int@0`. Only the second still carries the
  fact a totality proof needs, so an exact annotation on an index
  discards the proof that a lookup is in range.

Note that the second example annotates a bare `Int` and the two forms
still differ. The annotation's own shape is not what decides it: `Int@0` is
a strict subtype of `Int`, so there is something to discard. What makes
the forms coincide is the *value* knowing nothing beyond what the
annotation says.

A mutable introduction takes only the **exact** form, and only a
`Mut(…)`: `x: Mut(V) := e` and `x: Mut(V, Txn) := e`. A `:=` binder's
type *is* a `Mut(V, D)`, and both of the other spellings would have to
be reinterpreted to mean anything:

- `x: V := e` names the value type, not the binder's. The binder is at
  `Mut(V, D)`, so reading a bare `V` there would make `:` mean
  something at a `:=` binder that it means at no other.
- `x <: Mut(V) := e` claims nothing the exact form does not. `Mut` is
  **invariant** in its value type — a mutable variable is both read and
  written through the same binder — so the only type below `Mut(V, D)`
  is `Mut(V, D)`.

Both are rejected rather than reinterpreted. As everywhere else, the
exact annotation *is* the type: `x: Mut(Int) := 5` binds the value at
`Int`, discarding the seed's singleton, while the unannotated `x := 5`
keeps it. The annotation constrains every contribution to the value —
the seed and each write.

The same invariance makes a `Mut(…)` annotation exact wherever it is
written, so a `def` parameter takes `c: Mut(V)` and not `c <: Mut(V)`.

> **[Open]** — a mutable whose *value* type is inferred under a ceiling
> has no spelling. Under invariance that is not a bound on the binder's
> type at all, so it would need a bound in the value position
> (`Mut(<: V)`, say) — and `<:` does not appear inside a type literal.
> Nothing needs it today; the rejection above is what keeps the option
> open.

> **Note.** An exact parameter annotation also fixes how many times
> the function is compiled. A bounded or absent one leaves the
> parameter's type open, so each call site's argument type — down to
> *which literal* it is — can produce its own specialization; an exact
> one gives every call site one shared definition. Recommended style
> therefore annotates a top-level `def`'s parameters exactly and
> reaches for `<:` where a caller's more precise type has to survive
> the boundary.

### 6.2 Non-purity as type wrappers

(2026-06-29 §4.)

Whether a value is mutable / feedable / transactional is a property of its
**type**, expressed as a wrapper: `Mut(V)`, `Feed(V)`, `Mut(V, Txn)`.
Wrappers have to appear in function signatures and inside data structures
regardless (a function taking a mutable variable, a map *of* feeds), so
they are types rather than introducer keywords.

`Mut(V)` and `Mut(V, Txn)` are **implemented** — mutation and transactions
are specified in §8, and the two supporting rules below hold today. `Feed(V)`
exists as an internal type — what `defer()` and `http_serve` produce (§3.7) —
but its *forward-declaration surface* `h: Feed(_)` is **[Decided]**, not yet
accepted at lowering (§3.7, §7.3); `Feed` as a written type constructor is
likewise not yet resolved in annotations.

Two supporting rules (implemented):

- **Impure types are annotated at binders.** The wrapper must be written
  at the binding that introduces it — a bare `def add_one(x): x += 1` is
  rejected without `x: Mut(_)`.
- **`_` means "infer the rest."** A partial-inference type hole:
  `def add_one(x: Mut(_)): …` infers `Mut(Int)`; likewise `Mut(_, Txn)`,
  `List(_)`.

For ergonomics, an initialising `:=` alone marks a variable mutable
(`total := 0`); a `Mut(_)` annotation is mandatory only where there is no
initialiser — e.g. a `Mut` parameter (§4.3, §8.1).

### 6.3 Direction: collections as functions [Tentative]

The **organizing idea is decided**
(2026-06-29 §2), and
already shows through in §3.9: a collection *is* a function
`Domain ⇒ Value`, and the collection types are variations of that one
shape. The specific encodings below are a working sketch — expect the
details to change:

- `Array(n, T)` — `Fin(n) ⇒ T`: known size and order; statically
  bounds-checked lookup `arr[i]: T`.
- `List(T)` — `{len: Nat, data: Fin(len) ⇒ T}`: an array "boxed" with
  its length when the length isn't statically known; `lst[i]: Option(T)`.
- `Set(K)` — `Map(K, {})`: the domain is the payload; membership via
  `e in s` (§3.4). `{}` is the unit type (§6.6).
- `Map(K, V)` — `{is_key: K ⇒ Bool, data: {K where is_key(_)} ⇒ V}`;
  lookup `m[k]: Option(V)`, membership `k in m`.
- `FullMap(K, V)` — `K ⇒ V`: the **total** map, which is `Map`'s encoding
  with the `is_key` guard dropped, so the domain is all of `K` and every
  key is present. Lookup is `m[k]: V` — there is no missing case, so
  nothing to match (§3.9). A total map is typically *earned* by refining
  the key type down to keys known to exist, rather than by promising
  totality over an open type: `FullMap({String where _ in ks}, Int)` is
  total because its domain says which strings it holds (§6.4). That
  shifts "the lookup hits" from a runtime invariant to an obligation on
  whatever constructs the map. **[Open]**: precise semantics and
  limitations — starting with what that construction-site obligation is
  (a literal must cover the domain; a domain that grows must extend the
  map).
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

### 6.4 Refinement syntax

A refinement is written `{ 𝑇 where 𝑝 }` — the base type, the keyword
`where`, and a predicate over the value being refined:

```python
{Int where _ > 0}                       # a positive Int
{{a: Int, b: Int} where _.a > 0}        # a record refined through a field
{{a: Int} where _.a > 0}                # ... a single-field record; no comma
```

Refinement syntax has three pieces:

- **`{ … }`** because a refinement *is* a structural type (§2.4). The base
  type sits inside the braces in its own spelling, so refining a structural
  type nests two brace pairs (`{{a: Int} where …}`) — the outer pair is the
  refinement, the inner one is the record type. There is no elision.
- **`where`** as the separator, which leaves `|` free to separate variant tags
  (§6.5, §1.8) and reads as the clause it is.
- **`_`** as the refined value. The predicate has no named binder: `_` *is*
  the value, so a refinement is a closed expression about one anonymous
  subject rather than a binder plus a scope. This is the same `_` that
  means "infer this slot" in a type (§6.2), and the two do not collide
  because they sit in different positions — `_` in *type* position is the
  hole, `_` inside a `where` predicate is the value. Both appear at once in
  `{_ where _ > 0}`: refine a to-be-inferred base type by a predicate on
  its value.

The predicate is an ordinary CHL expression of type `Bool`, and `where`
binds looser than everything in it, extending to the closing brace (§2.4).
A `match` over `_` is the idiomatic way to refine a variant:

```python
{ { `some{Int} | `none } where
    match _:
        case `some(x): x > 0
        case `none: true
}
```

> **[Open]** — the layout of that `match`. Newlines and indentation are
> **ignored** inside brackets (§1.4), so a `match` written inside `{…}`
> gets no `INDENT`/`DEDENT` to delimit its arms: the arms above are
> readable to a human but invisible to the layout rules, and the parser
> would have to delimit each arm by the next `case` or the closing brace
> instead. That is parseable — neither token can continue an expression —
> but it is a second, delimiter-derived block discipline for `match`
> alongside the indentation-derived one it has today (§4.10). A
> **single-line `match`** form would collapse the two; its spelling is
> undecided, and so is any expression form of `match` at all (§4.10).

`_` is the value being refined, so a predicate that mentions *another* value
relies on that value having a name where the refinement sits. In a function
signature the parameters do, which is what lets a return annotation carry a
postcondition: `{Int where _ >= item.cost * qty}` refines the result by a
predicate naming two parameters (§6). Ordinary lexical scope (§5) is what
supplies those names, and nothing narrows them to parameters: a refinement
written at the top level may name a top-level binding, which makes that
binding's *value* part of the type —

```python
ks = ["a", "b"]
Key = {String where _ in ks}    # the strings `ks` holds, and no others
```

A refined key type of that shape is what a total map's domain is (§6.3). A
refinement with nothing in scope but `_` speaks only about its one anonymous
subject.

### 6.5 Variants

This section is the **type** side; construction is §3.15 and `match` is §4.10.

A **variant** is a tagged sum: a value is one of a fixed set of tags, each
carrying its own fields. Every tag is prefixed with a backtick, in every
position, and tag names are lowercase (§1.8, §6.1):

| Position | Delimiter | Example |
| --- | --- | --- |
| type | `{ … }`, tags separated by `\|` | ``{ `some{Int} \| `none }`` |
| term | `( … )` | `` `some(1) ``, `` `none `` |
| pattern | `( … )` | `` case `some(x) ``, `` case `none `` |

```python
`some(a=0) : { `some{a: Int} | `none }   # a tag with one named field
`some(1)   : { `some{Int} | `none }      # ... one positional field
`unit      : { `unit }                   # a nullary tag; a one-tag variant
```

The rules, and what each one is doing:

- **`{…}` encloses the type, `|` separates the tags.** A variant type is a
  structural type like any other (§2.4), and the alternation reads as the
  sum it is. A single-tag variant still takes its braces —
  ``{ `unit }`` — and needs no trailing comma, since the `` ` `` already
  marks the form (unlike a one-*tuple* type, §3.11). The braces are what say
  where the `|`-chain ends, so a bare arm outside them is not a type.
- **A tag's braces are its payload type's braces, elided**, and doubling them is
  an error. So a record payload is `` `some{a: Int} ``, never
  `` `some{{a: Int}} ``; a tuple payload `` `some{Int, Bool} ``; a one-tuple
  `` `some{Int,} ``, keeping the comma that says so (§3.11); and a nested
  *variant* payload reuses the arm's own braces,
  ``{ `outer{`some{Int} | `none} | `done }``. That last is also how a variant
  type prints, so a rendered type reads back as itself.

  Requiring the elision is what keeps **one spelling per type**, the same reason
  a standalone `{T}` must carry its comma (§2.4). It is available because a
  comma-free `{T}` has no standalone reading: those braces are therefore the
  **tag's**, and `` `some{Int} `` stores a bare `Int` — which is what makes it
  the type of `` `some(1) ``. A **nullary** tag writes no braces at all, and
  `` `some{} `` agrees with it, the empty product being unit (§6.6).
- **Terms and patterns use `( … )`**, because they are terms, and `( … )`
  is the product constructor at the term level (§2.4). The tag's parens are that
  product's, elided the same way, so construction *is* a call in shape (§3.8):
  `` `some(1) ``, `` `pair(1, True) ``, `` `some(a=0) ``, and the one-tuple
  `` `some(1,) ``. A pattern reads like the construction it matches (§4.3.1).

  Unlike the type level this yields no uniqueness, and does not try to: `( e )`
  is also *grouping* at the term level (§3.11), so `` `pair((1, True)) `` denotes
  the same value and no rule could forbid it. Braces and parens remain
  non-interchangeable across levels, and each rejection names the form that
  belongs in that position.
- **Tags are lowercase** because a tag builds a value, and `Caps` means
  type without exception (§6.1).

**The arms are a set**, canonicalized by tag name: ``{ `none | `some{Int} }``
and ``{ `some{Int} | `none }`` are the same type, and an annotation written in
either order compares equal to what inference produced.

`Option(T)` is the canonical variant — ``{ `some{T} | `none }`` — and is
what a partial lookup returns under the collections direction (§3.9,
§6.3). It is a built-in *abbreviation* in the same category as `List(T)`, not a
distinguished kind of type: nothing in the language privileges the spellings
`some` and `none`, and writing the arms out gives the same type. `Result` is the
same shape with `` `ok ``/`` `err `` and has no built-in spelling — write its
arms out, or wait for the type alias (§3.15).

Variants are matched with `match`/`case` (§4.10). Destructuring one directly
against a single-tag variant type, where the match cannot fail, is **[Decided]**
and not implemented (§4.3.1).

### 6.6 The empty product is unit

**A product with no fields is not a type of its own — it is unit.** Unit is a
base type, spelled `{}` in type position and only that (§2.4), and inhabited by
the value `()` (§3.11). Neither spelling is a product *expression* that happens
to evaluate to unit; they are simply how the type and its one value are written.

An "empty tuple type" and an "empty record type" are therefore **not types**
here. Nothing makes them incoherent in the abstract — a product with no fields
has nothing to distinguish positional keying from named keying, so both
descriptions would name the same one-inhabitant type — but neither is a type CHL
has. The compiler holds that as an invariant rather than a convention: no
zero-field product exists in the type representation at all, every product is
built through a constructor that maps the empty case to unit, and an assertion
catches any path that would bypass one.

**The reason is subtyping.** A product flows into a product that requires a
subset of its fields — `{a: Int, b: Int}` is accepted where `{a: Int}` is
required, and the extra field is simply not read. An *empty* field set is a
subset of every field set, so a zero-field **product** would be a type every
product flows into, arriving with every field dropped and nothing in the
program to mark the loss. Unit is a **base** type instead, and a base type
accepts only itself: getting from a product to unit takes an operation that
says so.

### 6.7 Type-alias statements

**[Tentative]** — not implemented. Nothing special-cases a capitalized
left-hand side: `src/ccl/lower/mod.rs` lowers the right of an `=` as a *term*,
so a `{…}` there is rejected as type syntax in value position and a bare type
name is an unresolved name. The alias-versus-nominal split this rests on is
the Direction note in §6.1, tentative there too.

A **type alias** binds a capitalized name to a type expression with plain `=`,
as an ordinary statement of the block it sits in:

```python
Count = {Int where _ >= 0}       # a name for a refined base type
Item = {price: Int, cost: Int}   # ... for a record type
Priced = {Item where _.price >= _.cost}   # ... built from another alias
```

Afterwards the name is writable wherever a type is: a parameter or return
annotation (`def f(n: Count) => Item:`), a type argument (`List(Priced)`,
`Mut(Count)`), a field type inside a record or `Feed(…)`.

The rules, and what each one is doing:

- **`=`, and no keyword.** An alias is a *timeless equation* between a name and
  a type, which is what `=` already means (§4.3 Direction) — so it is
  `assign_stmt` (§2.2), not a new statement form. What separates it from a
  value binding is the **case of the name**: `Caps` means type, without
  exception (§6.1). A `type` keyword is deliberately not involved; that
  spelling belongs to the *nominal* declaration §6.1 sketches, which an alias
  is not.
- **An alias names an existing type; it does not make a new one.** The alias
  and its right-hand side are the same type, interchangeable in every position,
  with no nominal distinction, no conversion, and no invariant of the alias's
  own. Type equality is structural and so is unaffected by spelling: `Count`
  and `{Int where _ >= 0}` are one type, and a refined alias is an ordinary
  type reference wherever it is written — `n: Count` carries the refinement
  into the signature exactly as the brace form would (§6.4).
- **The right-hand side is any type expression**, including one that names other
  aliases (`Priced` above) and one carrying a refinement whose predicate names
  *values* in scope (§6.4). An alias opens no scope of its own: the predicate
  sees what the statement sees, and nothing more.
- **No forward reference** (§3.2). The names on the right must already be in
  scope, so an alias follows both the aliases and the values it reads. A
  *self*-referential alias needs no `rec` marker, since §4.3 exempts recursive
  types, but what one would denote is unworked.

**[Open]** — whether an alias may be **parameterised** (`Pair(T) = {T, T}`),
which is the difference between naming a type and naming a type constructor;
whether aliases are block-scoped like every other binding (§5) or top-level
only; and whether the case rule alone carries the weight, since `Count = Int`
and `count = n` are one statement form telling a reader which world it is in by
one letter.

The north-star `storefront` exercises four aliases, two of them refined.

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

> **[Open]** — the restriction combinator's **name**, and how any of
> these combinators are *called*. The corpus spells the same operation
> two ways: `txn_kv` and `ledger_balance` write `c.restrict(\e -> …)`,
> the north-star `storefront` writes `orders.filter(\o -> …)`, and
> nothing decides between them — one of the two names has to go. Both
> are written in **method** position, which §3.9 does not admit: `.`
> there is projection of a field out of a product, not lookup of a
> library function on a collection, and `catalog.keys()` and
> `txn.current_time()` are the same shape. Whether a collection's
> combinators are reached through `.` at all — and if so what resolves
> the name, given that a collection *is* a function (§6.3) and has no
> fields — is open with them.

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

> **Direction [Tentative].** Iterating a keyed collection yields its
> **entries** — `groupby` returns a map-like `K ⇒ Collection` value, a
> bare `for` binder binds the whole entry pair, and a `k -> g` pattern
> (pair sugar, §2.4) destructures it, so the rollup can rebuild a map
> with a map comprehension:
>
> ```python
> [key -> sum([o.price for o in g]) for key -> g in groupby(paid, \o -> o.sku)]
> ```
>
> (the north-star `storefront` `/stats` rollup). Today's implemented
> iteration, shown above, yields the bare groups with no key.

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
> (2026-06-29, Open/deferred):
> how responses carry status codes, the structured-request surface
> (`req.body`, `req.query`, `req.time`, headers), response pairing via
> feed-at-index (`resps[req.id] = …`, as the north-star `txn_kv`
> writes it), and multi-endpoint multiplexing are all sketches, not
> decisions — closing any of them out means designing the HTTP
> library. The sketch the north-star `storefront` handlers are
> written against: a response is a record,
> `{code: {Int where 100 <= _ <= 599}, body: String}`, and the status
> constructors are ordinary library functions over it
> (`def not_found(body): (code=404, body=body)`, likewise `ok` /
> `bad_request` / `conflict`), with the record literal as the escape
> hatch for other codes — no new language surface. They live in an
> **`http` module** (**[Decided]**): programs write `import http`,
> then `http.ok(…)` / `http.not_found(…)`, and the north-star
> programs address the source the same way, `http.serve(…)`. Modules
> are records, so a module can be passed as one; the general module
> system (user modules, multi-file) remains future work (§9). A response feed's
> element type would be per-endpoint: a bare serializable value,
> answered as a 200 carrying it (`txn_kv` writes `String` bodies; the
> north-star `storefront` `/stats` answers with its revenue map
> directly), or the response record — one type, **not** the union of
> the two, since unions are structural, for records and variants, not
> a pattern-matchable set algebra over arbitrary types; a handler with
> any non-200 arm therefore wraps every arm. How the sink accepts
> either element type (an instance riding §8's typeclass solver?),
> the wire serialization of bare structured values, and whether an
> endpoint's response type can carry a contract refinement
> (`{Response where _.code < 500}`, "never answers 500") ride on the
> same library design. So does the typing of the response sink
> itself: a *deferred keyed collection* — supporting both
> `resps[req.id] = …` and a feed form `resps << …` — that needs CCL
> and CHL definitions. The `(requests, responses)`
> tuple-destructuring form above is what's implemented today,
> special-cased to `http_serve` only as an implementation matter
> (§4.3 Direction).
>
> **Request validation derived from the handler's type**, in the same
> **[Open]** design. A request is untrusted input, so the endpoint is a
> trust boundary and every refinement the handler's calls impose on
> `req.body` has to be discharged there (§6). The sketch has the
> *library* do it rather than each handler restate it: the request
> schema is read off the constraints the handler already implies, and a
> request violating one is refused before the body runs, so a handler
> body holds domain logic only. A handler that wants a *particular*
> answer for a rejected field takes the check back by writing it — a
> pattern match on a lookup is both the check and the branch that
> answers it, and its success arm is what refines the field for the
> calls below. Unsettled: what a derived refusal answers with (which
> status, which body), how a derived check evaluates a refinement whose
> predicate reads program state (§6.4), and whether writing the check by
> hand *opts the handler out* of the derived one for that field or
> merely duplicates it.

---

## 8. Mutability, transactions, and feeds

CHL programs reassign variables, accumulate in loops, run transactions,
and stream replies to sinks — yet the runtime is pure dataflow with no
mutable cell anywhere. This section specifies the **surface a programmer
writes** for mutation and transactions, and the **behaviour they may rely
on**. How the compiler eliminates all of it into pure dataflow (the
causal-recursion model, the commit engine, the loop engines) is the
realization, specified in
[src/ccl/design/mutability.md](../src/ccl/design/mutability.md); this
section is the observable contract that realization must honour.

**The one-line model.** A mutable variable *is* a function from a
**sequencing domain** (a time axis) to a value. "Mutation" is the
incremental revelation of that function as the domain advances; "reading"
is a lookup at the current position. Sequential rebinding, loop
accumulation (§4.6), and concurrent transactions are then *one* model over
three domains — a degenerate statement sequence, a `for` loop's iteration
order, and the transaction commit order `Txn` — not three mechanisms. A
**feed** (`<<`, §3.7) is the *same* kind of object under a different
merge law (§8.4): a mutable variable is *last-write-wins*, a feed is
*append-only*.

### 8.1 Mutation is explicit: the `:=` operator

A variable is mutable **by the operator that introduces it**. `:=` both
introduces and writes a mutable variable; plain `=` is an immutable
binding and *never* mutates (§4.3). The annotation is optional — it is
`:=`, not the annotation, that makes a variable mutable — but a written
one is a `Mut(…)`, exactly, because that is the binder's type (§6.1).

```python
cnt := 0                       # loop accumulator; value type and domain inferred
cnt: Mut(Int) := 0             # value type spelled exactly, so `cnt` is `Int`, not `Int@0`
balance: Mut(Int, Txn) := 0    # transactional mutable variable over the commit order
```

- `:=` — the write operator, for the first introduction (`cnt := 0`) and
  every later write (`cnt := cnt + 1`), at top level, in a loop, or in a
  transaction. `+=` / `-=` / `*=` / `//=` are compound shorthands. A `:=`
  or `+=` applied to a name that is *not* mutable is a **type error**, not
  a silent rebind — this is the rule that makes "declare it with `:=`" a
  real discipline.
- `Mut(V)` / `Mut(V, D)` — the optional mutability annotation (§6.2), and
  the only shape one can take: a bare `cnt: Int := 0` is rejected, since
  the binder's type is `Mut(Int, D)` (§6.1). `V`
  is the value type; `D` is the sequencing domain, inferred as the writing
  loop's domain when omitted or written `_`. **`Txn` is never inferred** —
  sharing a variable across concurrent writers or endpoints is a semantic
  commitment the program must spell, so a transactional mutable variable is always
  introduced `balance: Mut(V, Txn) := …`.
- `Mut(…)` is also legal as a function **parameter** annotation —
  pass-by-reference, so a callee can write the caller's variable
  (§6.2). It carries a **downward-only, no-aliasing** discipline: a `Mut`
  argument is always a bare variable (never a computed expression), `Mut`
  never appears inside a composite type (no tuple/record/list/`Feed` of
  `Mut`, so it is never returned).

  A plain `b = a` off a mutable **reads** it — a snapshot of its current
  value, exactly as `a + 1` or `f(a)` read it. It is not an alias, and not
  an error: only `:=` introduces a mutable, so `b` is an ordinary
  immutable binding and writing through it (`b += 1`) is the type error
  §8.1 already gives. To seed a *new* mutable from one, use `:=`
  (`b := a`); no annotation is required.

A name needs `:=` exactly when its history spans iterations or
transactions; a value computed once and never rewritten stays a plain `=`.

### 8.2 Transactions: `with begin():`

A transaction is a `with begin():` block, usable anywhere a statement can
appear — as a loop body (one transaction per iteration) or standalone (a
single transaction):

```python
for req in incr_reqs:
    with begin():
        balance += 1
```

- `begin()` is the transaction marker. **All writes in one block commit
  atomically** — the whole block's writes become visible together or not
  at all. There is no partially-visible commit.
- Writes to a `Txn`-domain mutable variable are legal **only** inside a `with
  begin():` block; a write outside one is rejected (§8.3), as is a write
  reached through a transactional-writer function *called* inside a block
  (a disguised nested transaction).
- **Nested transactions are rejected** — a block commits as one unit, so a
  `with` inside it has no coherent meaning.
- **Deny guard.** A block may carry a single bare `if p:` guard; the
  transaction commits iff `p` holds over its snapshot, and a denied
  transaction contributes no write and no reply. An `elif`, an `else` that
  writes, or more than one `if` guard in one block is **[Planned]**
  (rejected today with a diagnostic) — the general path-based conditional
  model is worked through in the design doc.
- **Transaction handle — `with t = begin():` [Decided].** Binds `t` to the
  transaction's commit time (a `Txn` value); designed but rejected at
  lowering today.

**Scope transactions minimally.** Only the operations that must be atomic
go inside `with begin():` — input validation before it, response
assignment after it. The north-star handlers observe this throughout (e.g.
`storefront`'s `/order` matches the catalog before opening the transaction
around `reserve` + `quote` + the feed).

> **Direction [Tentative] — a block is also the value it computes.**
> Scoping minimally puts the reply outside the block, which leaves the
> block needing to hand its result out: a `with begin():` block in value
> position denotes the value of its last statement, the same rule a
> function body follows (§4.1), and the enclosing binding carries it past
> the block's end. Nothing admits it today — §2.2 has `with_stmt` as a
> compound statement and an `assign_stmt` right-hand side as an
> `expression`, and the two never meet. **[Open]** is how §8.4's gating
> rule reads against it: a reply fed *inside* a block rides the commit and
> a denied transaction replies nothing, while a reply outside fires
> regardless — and this shape puts the reply outside with a value that
> came from inside, so which of the two it inherits has to be said.

### 8.3 Reads

- **In-context** (inside the mutating loop or block) — a bare reference is
  the value at the current position: the previous iteration's value, or,
  after a write earlier in the same iteration/block, the just-written
  value (**read-your-writes**).
- **Trailing induction read** — after a `for` loop, a bare reference to an
  induction accumulator is its final value (or the pre-loop value if the
  source was empty). The loop has ended, so "latest" is unambiguous.
- **A `Txn` mutable variable is read only inside a `with begin():` block.** A bare
  read outside one is an error. Reading inside a block pins a
  **snapshot-consistent** view: several mutable variable reads in one block see
  one commit snapshot — the reason the block is required.
- **As-of read.** A mutable variable read fed *out* of a block that does not
  itself write that mutable variable is an **as-of read at an arbitrary commit
  position** — the mutable variable's value as of wherever the reading transaction
  lands in the commit order, replied indexed by the *reading* loop. This
  is uniform whether the reader is a live request stream, a finite loop,
  or the synthesized singleton of a standalone read.
- **Terminal read — `await_final(x)` [Decided].** `await_final(x)` waits for
  `x`'s whole commit history to complete and yields its final value (§8.6). It
  is the only terminal read of a mutable variable: every other read is an
  arbitrary as-of sample, so a program that means the final value has to say
  so.

### 8.4 Feeds are the second form of mutability

A feed (`<<`, §3.7) is the **same history object** as a mutable variable,
under the **append-only** merge law: contributions union (`++`), there is
no carry-forward, and a read yields the whole stream — which is exactly
why a feed is an unordered bag (§3.7) while a mutable variable derefs to a
single latest value. `o << e` is surface-impure in the same way `x := e`
is; the two differ only in that merge law.

Two feed shapes interact with transactions, and the difference is
observable:

- **Reply *inside* a block** (`out << e` within `with begin():`) rides the
  commit: it is **sequenced after the commit** and **gated** — a denied
  transaction replies nothing — and is indexed by commit tick.
- **Reply *outside* the block** rides its own loop's domain and fires every
  iteration regardless of commit — request-indexed, value-correct, but not
  commit-ordered. **To gate or commit-order a reply, put it inside the
  block.**

### 8.5 Ordering and concurrency

A mutable program's meaning is an *ordering story* — which effect happens
before which. CHL states that story as a single principle:

**Execution is maximally concurrent; nothing is ordered by its position in
the source text. The only ordering is the transitive closure of dependency
edges, and every edge originates at an _event_.** Two pieces of logic are
ordered exactly when a chain of dependency edges connects them, and freely
interleaved (or parallel) otherwise. The events:

- **Program start.** Initializers, literals, constant loop sources
  (`[10, 20, 30]`), and top-level `=` bindings are available here; logic
  reading only them runs immediately.
- **Incoming data on a source.** Each element arriving on a source
  (`stdin()`, `http_serve`, …) is an event; logic consuming it depends on
  its arrival. This is the event that **pins commit order**: a writer
  driven by a live stream commits in the stream's real arrival order.
- **A data dependency forced by logic.** When logic reads a value another
  piece produces, the read depends on the write — read-your-writes in a
  block, a commit decision reading a snapshot, a reply consuming its own
  commit record.
- **`await_final`.** The **completion event** of a transactional mutable variable
  (§8.6): it is available only once every writer of the mutable variable has
  drained, and everything downstream depends on that completion.

Consequences a program may rely on:

- **Commit order is not global.** Two `with begin():` blocks are ordered
  relative to each other only if they mention a mutable variable in common —
  a shared variable is what makes one block's commit visible to the other.
  Blocks with no variable in common are **unordered**: nothing in the
  language imposes an order between them, and their transactions interleave
  freely. Two independent `for` loops relate their accumulators the same way.
- **Commit order is not lexical order.** Two `with begin():` blocks do
  **not** commit in the order they appear in source; each block's position
  is fixed by its trigger event (a source arrival, or the loop index for a
  batch writer). A programmer's default lexical-order assumption is wrong.
- **Read-your-writes** within a block or iteration.
- **Reply-after-commit / cross-endpoint monotonicity.** A reply fed from
  inside a block is sequenced after that commit; combined with arrival-order
  monotonicity this gives external consistency — a client that sees `ok 2`
  then reads another endpoint observes `≥ 2`.
- **Terminal vs. temporal reads.** `await_final` (and the trailing
  induction read) wait for a history's *completeness*; an as-of read waits
  only for the *frontier* (that no earlier-or-equal commit is still
  outstanding) and samples the mutable variable as of the reader's own position.
- **A shared program-start anchor gives no *relative* order — by design,
  not by omission.** A standalone `with begin():` or a literal-list loop
  depends on **program start** like everything else, but on nothing more.
  Program start is a *single* event: it sequences each block after itself,
  yet imposes no order *among* the blocks it triggers, so they are mutually
  unordered — the engine may serialize them any way and the program is
  correct under all of them. (A live-stream writer differs because its
  successive arrivals are *distinct* events carrying a real order, which
  the commits inherit.) This is the contract, not a gap: to fix a relative
  order, **supply a distinguishing edge** — drive the writers from the
  source whose arrival order you mean, introduce a data dependence, or
  bound the result with `await_final`. An order-sensitive body with no such
  edge has nondeterministic denotation, by design.

### 8.6 `await_final` [Decided]

`await_final(x)` is a builtin call on a transactional mutable variable
`x: Mut(V, Txn)`, an expression of type `V`: the mutable variable's **final
committed value**, once every block that writes `x` has finished, or the
initializer if it was never committed. It is the commit-domain counterpart of
the trailing induction read (§8.3) and the completion event of the ordering
model (§8.5) — the one read that waits for a `Txn` mutable variable's
completeness rather than sampling its frontier.

```python
pool: Mut(Int, Txn) := 100
for r in reqs:
    with begin():
        pool -= r
final = await_final(pool)      # `pool` once every writer of it has finished
```

**`x` is unreferenceable afterward.** After `await_final(x)`, any later
reference to `x` — a read, a write, or a second `await_final(x)` — is a compile
error. That is what makes the completion event well-defined: the await closes
`x`'s writer set at that point, so "final" names a fixed value. (A `for` loop's
accumulator gets a terminal read for free because the loop has a lexical end; a
mutable variable has none, so the barrier is drawn by consuming it.) The rule is
about `x` alone — a later block that does not mention `x` is an ordinary
transaction.

**Nothing a writer of `x` needs may depend on `await_final(x)`**: the await
completes only once every block writing `x` has finished, so such a dependency
is a cycle. Three positions are rejected — a writer's iteration source, a
writer's decision body, and a transactional mutable variable's seed. Awaiting a
mutable variable written *elsewhere* is an ordinary dependency between two
computations, which is what makes **phase separation** — drain one transaction,
then seed the next from its final value — compile:

```python
a: Mut(Int, Txn) := 100
for r in reqs1:
    with begin():
        a := a - r
b: Mut(Int, Txn) := await_final(a)   # `b`'s seed is `a`'s final value
for r in reqs2:
    with begin():
        b := b - r
```

An **induction** accumulator may likewise be seeded from an await
(`x := await_final(pool)`): a different recurrence, so there is no cycle.

One restriction unrelated to cycles: `await_final` may not appear inside a `with
begin():` block, which reads its mutable variables bare as a snapshot; awaiting
there would wait on the history that block extends.

**Completeness is per variable.** `await_final(x)` waits for every block that
may write `x` and for nothing else, so a mutable variable whose writing blocks
are all finite settles while other variables — including ones `x` shares a block
with — are still being written by a live source. If no block writes `x` at all,
or every transaction denies, the await is `x`'s initializer.

> **Current limitation.** The *rejection* rule is enforced slightly wider than
> it is stated: a block's dependency on an `await_final` is refused when the
> awaited variable merely shares a block with one the dependent block writes,
> not only when that block writes the awaited variable itself. Reaching a
> wrongly-refused program takes a dependency that comes back into a related
> variable, and the refusal is a compile error, never a wrong answer.

### 8.7 Direction [Decided]: transactions as contextual parameters

(2026-06-29 §6; the north-star `txn_kv` program is the worked example.)

The implemented model above passes a transaction *implicitly by block
scope* (`with begin():` establishes it; `Mut(…, Txn)` mutable variables are the
shared state). A **[Decided]** further direction adds an explicit
contextual-parameter mechanism modeled on Scala 3's `given`/`using`/`summon`,
so a transaction can be threaded into a called function without a `Mut`
parameter:

- `def put(…) requires Transaction:` — the function declares it needs a
  transaction from context.
- `given txn` — injects an existing transaction into the context.
- `summon(Transaction)` — manifests the contextual transaction as a value.

Supporting decisions (same source):

- **Discharged by the typeclass/given solver, *not* algebraic effects.**
  Cambra compiles to static dataflow; handler-based effects make control
  flow non-local and data flow handler-dependent — exactly what the
  dataflow compiler cannot see through. `requires Transaction` is ordinary
  dictionary passing, resolved by the same solver that will serve general
  typeclasses.
- **Locally-scoped givens, not global coherence.** A fresh transaction is
  minted per `with begin():` block; many exist over a program's life.
- **Domains as a type index.** `Transaction(dom)`, created with
  `with dom.begin()`, restores per-domain coherence while allowing fresh
  transactions across scopes. Start with one global domain and make `dom`
  itself a given, so the common case omits it.
- **Commit/abort are data operations on a time-region**, not control
  effects: block exit merges the region forward (commit), `abort()` drops
  it (rollback) — a structured early-exit, not exception unwinding.
- **Terminology:** type `Transaction`; variable abbreviation `txn` (never
  `tx`, which collides with "transmit"); operations `begin()` / `abort()`.
- **Implicit *parameters* only — never implicit conversions**; given
  visibility stays explicit and resolution inspectable (hence `summon`).

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
illustrate implemented features. The **north-star** programs are
instead written in the *target* syntax of the Direction notes (`rec`,
`:=`, `(f=…)` records, `\`-lambdas, `Feed`/`Mut` wrappers, type
aliases, refinements, transactions) and are pinned as expected
compile-errors that go red one by one as the direction lands; read
them as the direction's worked examples, with the same status caveats
as the Direction notes they exercise. `storefront` is the north-star
proper — one application over all of it, in the two versions
`v0.cambra` and `v1.cambra` — and `reachability`, `fanout`, `txn_kv`,
`discount_contract`, `nonneg_inventory`, and `ledger_balance` isolate
one capability each so a failure names one gap.

---

## 12. Reserved for future work

The following are deliberately omitted from CHL today, in some cases
with parser-level support that lowering rejects:

- **`while` loops** — currently a parse error (the `while` keyword is
  not yet recognised). Tracked as future work under mutability
  ("while loop lowering").
- **Nested `for` loops with mutable variables** — a single-level
  for-loop accumulator works (§4.6), but mutation inside a nested loop
  is not yet lowered.
- **A mutable variable introduced inside a loop body or a transaction
  block** — a mutable variable must be declared before the loop that
  accumulates it (§4.6), and a `with begin():` block may write mutable variables
  declared outside it but not introduce its own. Both would need a
  sequencing domain nested inside the enclosing one.
- **Generator body shapes** — a `def` containing any `yield` is a
  generator function semantically (§4.2), but today the compiler only
  accepts bodies that are exactly one top-level `for`. Top-level
  `yield`s, multiple sequential `for` loops, nested `for`s where the
  inner loop yields, and post-loop statements are all rejected
  pending support.
- **First-class functions in arbitrary positions** — see the
  2026-03-05 first-class-functions design notes.
- **Recursion** — self-reference in `def` is not yet wired through;
  self-referential *value* bindings get the explicit `rec` form
  (**[Decided]**, §4.3).
- **Imports / multiple files** — CHL is single-file today. Importing
  *built-in* modules is decided ahead of the rest (`import http`, the
  HTTP Direction note in §7.4); user modules, multi-file programs, and
  the general namespace story arrive together later — that is when the
  full *module* concept earns a place in this spec (§2.1 deliberately
  avoids it now).
- **Classes / `try`** — not in the language. `with` **is** a keyword
  (§1.6), but only for transaction blocks `with begin():` (§8.2); it does
  not carry Python's general context-manager meaning.
- **Float arithmetic** — no `f64` type at the surface.
- **String operations** beyond `+` concatenation.
- **Surface refinement type syntax** — refinement types (§6) are
  inferred today only via built-ins like `groupby`; the decided
  surface form is `{T where p(_)}` (**[Decided]**, §6.4), not yet in
  the grammar. `where` is already **lexed** and reserved (§1.6); what is
  missing is the brace-form production and `_` in term position inside the
  predicate. Function contracts are written either as those annotations or as
  `assert`s lifted to refinements (**[Decided]**, §6) — `assert` is likewise not
  yet a statement.
- **Named variant types** — a tag has no declaration site, so a misspelled tag
  is caught only where it fails to meet its counterpart, and a constructor's
  payload arity is not checked at the constructor. The structural type alias
  (`` Option(T) = {`some{T} | `none} ``) is the planned resolution site, and
  would replace the built-in `Option(T)` with a prelude definition
  (**[Tentative]**, §3.15, §6.1).
- **Pattern matching** beyond a `match` arm's single tag — `match` / `case`
  tag dispatch over a variant is implemented (§4.10), but patterns are
  shallow: no nesting, no literal patterns, and no per-arm guard. `match` is a
  statement only; an expression form is **[Open]**, and the layout rules
  (§1.4) force the question for a `match` inside a refinement predicate
  (§6.4).
- **Destructuring patterns** beyond tuples — record, variant, and
  wildcard patterns in assignment targets and `for` binders (a `match`
  arm's tag pattern is §4.10), and per-component annotations with `:`
  binding tighter than `,` (**[Decided]**, §4.3.1).
- **Unit values do not run** — the type surface is settled (`{}` for the type,
  `()` for the value, §6.6) and both typecheck, but a unit-valued program
  output cannot be materialized by the interpreter: it has no column
  representation, so `x = ()` compiles and then fails at runtime. This is a
  runtime gap, not a surface one.
- **The term-level delimiter migration** — record values are `(f=1, …)`, and
  `{…}` no longer denotes a term-level value (it is record-type / tuple-type /
  unit syntax, §2.4). Finite maps as `[k -> v, …]` remain **[Decided]**; earlier
  plans to spell them `[k: v, …]`, `[k=v, …]`, or Unicode `[k ↦ v, …]` are
  superseded by the map-literal decision.
- **Map comprehensions** — not in the grammar; the surface form
  follows the map-literal decision above: `[k -> v for …]`
  (**[Decided]** as surface, unimplemented; the north-star
  `storefront` `/stats` rollup uses it).
- **The target syntax at large** — the mutation and transaction
  **core is implemented** (`:=`, `with begin():`, `Mut(…, Txn)` mutable variables,
  feeds — §8), now spelled in the canonical target syntax: parenthesised type
  application (`Mut(V, Txn)`, `List(T)`) and capitalized primitive names
  (`Int`, `Bool`, `String`), with record types `{name: T, …}` and tuple types
  `{T, U}` writable in annotation position (§6.1), and variants writable in all
  three positions — type, term and pattern (§6.5, §3.15, §4.10). The remaining
  **Direction** notes are unimplemented: `rec` bindings (§4.3), destructuring
  patterns (§4.3.1), membership `in` (§3.4), the `->` pair/map-entry syntax
  (§2.4), refinements (§6.4), the `Feed(_)`
  forward-declaration surface (§3.7, §6.2), and
  transactions-as-contextual-parameters (§8.7). The north-star programs
  pin the target; the sequencing is tracked

When each lands, this spec will be updated alongside the lowering and
the demo programs.

---

## See also

- [docs/design.md](design.md) — overall Cambra architecture.
- [src/chl_parser/design-chl-parser.md](../src/chl_parser/design-chl-parser.md) — the parser implementation.
- [src/ccl/design/](../src/ccl/design/README.md) — the CCL IR and the
  lowering/inference/optimization passes.
- [docs/operational-semantics/summary.md](operational-semantics/summary.md) — CCL's operational semantics.
- [docs/demo-programs.md](demo-programs.md) — runnable examples and their status.

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

CHL source is UTF-8 text. A span is a byte range of one source file.

### 1.2 Whitespace, comments, line structure

- **Inline whitespace** (`' '`, `'\t'`) separates tokens and is otherwise
  insignificant.
- **Comments** start with `#` and extend to the end of the line.
- **Physical newlines** terminate *logical* lines, except when suppressed
  by an unclosed bracket (see Implicit line continuation, below).
- **Blank lines and comment-only lines** do not affect indentation.

### 1.3 Indentation (off-side rule)

Indentation determines block boundaries. Its width is the byte count of leading spaces and
tabs; a tab counts as one byte, not expansion to a tab stop. Blank and comment-only lines
do not establish or close a level. Indentation inside brackets is ignored.

For ordinary statement blocks, indentation levels start at zero. A line farther indented
than the current level opens a new level. A dedent must return to an enclosing level;
otherwise lexing fails with `InconsistentIndent`. A line at the current level leaves the
block structure unchanged.

An `if` or `match` on the right-hand side of an assignment opens one further level; see
[Assignment forms](#43-assignment-forms). When a header spans physical lines inside
brackets, its indentation is that of the statement's first line.

End of input closes every open level.

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
forall requires
import use    as     pub    run    param  this
```

`where` is the refinement predicate separator (§6.4). It is lexed so the name is
**reserved**: a bare `where` is a keyword rather than an identifier. The refinement
syntax itself is parsed, in every annotation position that takes a type (§6.4).

`with` is a keyword: it introduces a transaction block, `with begin():`
(§8.2). It does **not** carry Python's general context-manager meaning.

A lambda is written `\x -> body` (§3.10); `\` and `->` are punctuation
(§1.8), not keywords, so `lambda` is an ordinary identifier — it, along with
`while`, `class`, `try`, `except`, `global`, `nonlocal`,
`del`, `assert`, `raise`, `is`, are **not** keywords in CHL today. Some are
reserved for future use.

`import`, `use`, `as`, `pub`, `run`, `param` and `this` are the module keywords
([9. Modules [Decided]](#9-modules-decided)). The statements they introduce parse, and lowering
refuses each of them until modules are implemented.

`match` and `case` introduce tag dispatch over a variant (§4.10).

`forall` begins a polymorphic type (**[Planned]**,
[Polymorphic type annotations](#polymorphic-type-annotations)). `requires` begins a `requires`
clause, which ends a `def` signature or a polymorphic type
([Trait requirements](#trait-requirements)). `requires Transaction` is **[Planned]**
([8.7 Direction [Decided]: transactions as contextual parameters](#87-direction-decided-transactions-as-contextual-parameters)).

> **Direction.** Planned binder/keyword vocabulary, not lexed today:
> `rec` (recursive binding — §4.3, **[Decided]**), `given` and `summon` (the
> transactions-as-contextual-parameters layer — §8.7, **[Decided]**), `type` (nominal types,
> **[Decided]**, [6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)),
> and `assert` and its `static assert` form (function contracts — §6, **[Decided]** as the
> surface, **[Open]** as to what `static` demands). Avoid taking these names for other purposes.
> (`with`, `:=`, `match`, `case`, `where`, `forall`, `requires` and the module keywords are
> **already** lexed — the first two carry today's transactions and mutation, §8, `match`/`case`
> carry tag dispatch, §4.10, `where` separates a refinement's predicate, §6.4, and `forall` and
> `requires` begin a polymorphic type and a `requires` clause, §6.10 — so they are not in this
> list.)

### 1.7 Literals

| Form | Token | Notes |
|---|---|---|
| `0`, `42`, `1234` | `Int(i64)` | Decimal only; no `_` separators, no hex/bin/oct, no negation in the token (`-3` is `UnaryOp(Neg, 3)`). |
| `"hello\n"`, `'world'` | `String` | Double- or single-quoted. Escapes: `\n \t \r \\ \" \' \0`. Unknown escapes are preserved verbatim (the `\` is kept). A literal closes on the line it opens on: a raw newline before the closing quote is the lex error `UnterminatedString` ([11.1 Lex errors](#111-lex-errors)), so there are no multi-line strings. No triple-quoted `"""..."""`, no f-strings, no raw `r"..."`. |
| `True`, `False` | `Bool` | |

There are no floating-point literals — CHL has no `f64` type at the
surface level.

### 1.8 Operators and punctuation

```
+  -  *  **  //  ++  ->  =>
&  |  ^
== != <  <= >  >=
=  += -= *= //=
:=  <:  ::
<<  <<=
(  )  [  ]  {  }  ,  :  .  ;  \  `  ?  @
```

`::` separates a qualifier from the name it qualifies: a module or a run from its member
(`cart::total`, [9.6 Qualified references](#96-qualified-references)), a module from its label or
tag (`r.mod2::f1`, `` mod2::`some ``, [9.12 Field labels and tags belong to a
module](#912-field-labels-and-tags-belong-to-a-module)), and a nominal type from its method
(`Price::discounted`, [6.8 Nominal types and methods
[Decided]](#68-nominal-types-and-methods-decided)). A qualified name parses wherever a name does,
and lowering refuses it until modules are implemented.

> **Direction [Decided].** Postfix `!` joins the set. It unwraps a proven `` `some ``
> ([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)).

`:=` is the **mutation** operator (§4.3, §8.1) — it introduces and writes
a mutable variable. It is *not* Python's walrus operator: it is an
Algol-tradition assignment **statement**, and there is still no
assignment-as-expression.

`<:` is the bounded annotation: `x <: T` bounds the binder's inferred type
by `T` where `x: T` fixes it
([Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded)).

`?` directly after a subscript's `]` is the optional lookup, `c[k]?`
([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)). The decided
direction there retires it.

`@` is the decorator introducer ([1.9 Decorators](#19-decorators)); there is no
matrix-multiplication operator.

**Notably absent vs. Python**: `/`, `%`, `>>`, `~`, walrus
assignment-*expressions*, and `...`. Writing one is an error; `//` is floor
division, not `/` twice.

`**` is exponentiation ([3.3 Arithmetic and logical operators](#33-arithmetic-and-logical-operators)). `**=` is not a
token, so the augmented
assignments are the four above.

`++` is not a Python token at all: it is CHL's collection-union operator
(§3.3). There is no increment operator — `++` is always binary.

`\` introduces a lambda binder and `->` separates it from the body —
`\x -> body` (§3.10).

`->` is also the **pair arrow**: `a -> b` is the two-tuple `(a, b)`
([2.4 Atoms](#24-atoms)), which makes a map literal the list of entry pairs
`[k -> v, …]` and a map comprehension `[k -> v for …]`. A lambda's `->` closes
its binder list before the pair arrow is reached, so `\x -> x -> 1` is a lambda
whose body is a pair ([2.3 Expression precedence](#23-expression-precedence)).

`=>` is the function-type arrow. It separates a `def`'s parameter list
from its return-type annotation — `def f(x: Int) => Int:` (§4.1), which
type inference checks against the body's value. It is also a general type
operator inside an expression: `T => U` is a function type, writable in
any annotation position (§6).

`` ` `` (backtick) prefixes a **variant tag**, in every position — type, term,
and pattern: `` `none ``, `` `some(1) ``, ``{ `some{Int} | `none }`` (§3.15,
§6.5). A tag is `` ` `` immediately followed by an identifier with no
intervening whitespace; any other backtick is the lex error `DetachedBacktick`
([11.1 Lex errors](#111-lex-errors)). Tag names are lowercase, since a tag
builds a *value* and `Caps` means type (§6.1).

`|` is the logical-or operator in term position (§3.3) and additionally
separates the arms of a variant **type** (§6.5). The two never meet: a variant
type's arms are `` ` ``-tagged, and a refinement predicate — the one place a
term appears inside `{…}` — is introduced by `where` (§6.4), which is exactly
why the refinement separator moved off `|`.

### 1.9 Decorators

`@` introduces a decorator on the line above a declaration. The decorators are `LoadFrom`
([8.8 `@LoadFrom`](#88-loadfrom)), `RenamedFrom`
([9.18 Reloading a program of modules](#918-reloading-a-program-of-modules)) and `Discard`
([8.9 `@Discard` [Decided]](#89-discard-decided)), so `@` never appears in any other position.
`@RenamedFrom` and `@Discard` parse, and lowering refuses them.

### 1.10 Semicolons

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
sharing a single lexical scope. Semantically the top level behaves
exactly like any nested block (§4). (The parser's root AST node is
named `Module`, after Python's `ast.Module`.)

> **Direction [Decided].** A source file is a **module**. Importing one
> asserts that it performs no IO and reaches its one shared run; running one
> creates a run of its own. The engine runs one root module. Modules are
> specified in [9. Modules [Decided]](#9-modules-decided), whose statements (`import`, `run`, `param`,
> and `pub` on a member) extend this grammar ([2.2 Statements](#22-statements)).

### 2.2 Statements

```ebnf
statement       ::= simple_stmt NEWLINE
                 |  block_assign_stmt
                 |  compound_stmt

simple_stmt     ::= return_stmt
                 |  pass_stmt
                 |  import_stmt
                 |  run_stmt
                 |  param_stmt
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

-- The same six assignment forms with a block statement on the right (§4.3).
-- The block's DEDENT ends the statement, so no NEWLINE follows it.
block_assign_stmt ::= assign_target "=" block_value
                   |  assign_target ":" expression "=" block_value
                   |  assign_target [ ":" expression ] ":=" block_value
                   |  assign_target aug_op block_value
                   |  assign_target "<<=" block_value

block_value     ::= if_stmt | match_stmt

aug_op          ::= "+=" | "-=" | "*=" | "//="

assign_target   ::= ident
                 |  "(" assign_target ( "," assign_target )* [ "," ] ")"
                 |  assign_target ( "," assign_target )+ [ "," ]

compound_stmt   ::= if_stmt | match_stmt | for_stmt | with_stmt | def_stmt
                 |  load_from_stmt | renamed_from_stmt | discard_stmt | pub_stmt

if_stmt         ::= "if" expression ":" block
                    ( "elif" expression ":" block )*
                    [ "else" ":" block ]

match_stmt      ::= "match" expression ":" NEWLINE INDENT case_arm+ DEDENT
case_arm        ::= "case" case_pattern ":" block
case_pattern    ::= "`" ident [ "(" ( ident | "_" ) ")" ]
                 |  "_"

for_stmt        ::= "for" assign_target "in" expression ":" block

with_stmt       ::= "with" [ ident "=" ] expression ":" block

def_stmt        ::= "def" ident "(" [ params ] ")" [ "=>" expression ] [ requires_clause ] ":" block
params          ::= ( type_param "," )* value_param ( "," value_param )* [ "," ]
value_param     ::= ident [ ( ":" | "<:" ) expression ]
-- `type_param` and `requires_clause` are in §6.10.

-- A declaration seeded from the version this source replaces, via `@LoadFrom`. The
-- decorator and the declaration are one statement, which is why a declaration
-- may carry an annotation and no value here and nowhere else.
load_from_stmt  ::= "@" "LoadFrom" "(" ident ")" NEWLINE
                    [ "pub" ] ident ( ":" | "<:" ) expression NEWLINE

-- A run that the version this source replaces held under another name, by `@RenamedFrom`.
renamed_from_stmt ::= "@" "RenamedFrom" "(" ident ")" NEWLINE run_stmt NEWLINE

-- A declaration head marked gone, by `@Discard`.
discard_stmt    ::= "@" "Discard" NEWLINE discard_head NEWLINE
discard_head    ::= ident | "run" module_path [ "as" ident ]

-- `pub` before the statement that introduces a member. Any statement parses
-- after it; one that introduces no member is refused.
pub_stmt        ::= "pub" statement

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
> no-subscript-target rule above).
> (`mut_assign_stmt` and `with_stmt`
> above are already implemented — §4.3, §8; they are in the grammar, not
> this list.)

The module statements `import_stmt`, `run_stmt`, `param_stmt`, `renamed_from_stmt`, `discard_stmt`
and `pub_stmt` parse, with the productions of [9. Modules [Decided]](#9-modules-decided). Lowering
refuses each of them until modules are implemented.

### 2.3 Expression precedence

From lowest to highest; all binary operators are left-associative unless
noted:

| Level | Operator(s) | Notes |
|---:|---|---|
| 1 | `\x -> …` (lambda), `yield` | prefix forms; non-associative |
| 2 | `=>` | function type; *right*-associative — the codomain is the whole expression to its right ([1.8 Operators and punctuation](#18-operators-and-punctuation)) |
| 3 | `<<` | feed operator (right-associative is not meaningful — see [3.7 Feed operator `<<`](#37-feed-operator-)) |
| 4 | `->` | pair; non-associative — `a -> b -> c` is a parse error. The value admits a lambda, the key does not ([2.4 Atoms](#24-atoms)) |
| 5 | `e₁ if cond else e₂` | ternary; *right*-associative |
| 6 | `or` | short-circuit; n-ary flattening |
| 7 | `and` | short-circuit; n-ary flattening |
| 8 | `not` | prefix |
| 9 | `==` `!=` `<` `<=` `>` `>=` | chained, *not* left-fold (see [3.4 Comparisons](#34-comparisons)) |
| 10 | `\|` | logical or |
| 11 | `^` | logical xor |
| 12 | `&` | logical and |
| 13 | `++` | collection union |
| 14 | `+` `-` | additive |
| 15 | `*` `//` | multiplicative |
| 16 | unary `-` | prefix |
| 17 | `**` | exponentiation; *right*-associative. It **straddles** the unary `-` at 16 rather than sitting under it — see below |
| 18 | postfix: `f(args)`, `x[i]`, `x.attr`, `x.0` | left-fold. The method call `x.m(args)` ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)) and the unwrap `e!` ([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)) join this level (**[Decided]**) |
| 19 | atom | literal, name, `(...)`, `[...]`, `{...}`, comprehension |

`**` binds tighter than the unary `-` on its left and looser than the one on
its right, which is why one level cannot place it: `-2 ** 2` is `-(2 ** 2)`,
and `2 ** -1` parses without parentheses. The second is then rejected for its
exponent's sign, a typing rule and not a grammatical one.

`**` groups to the right, so `2 ** 3 ** 2` parses as `2 ** (3 ** 2)`. That
program does not compile: a `**` answers a bare `Int`, which shows nothing
about its sign, so no `**` result is another one's exponent. Parenthesising
the other way — `(2 ** 3) ** 2` — compiles, the grouping being what the
rejection is about rather than the associativity.

```ebnf
expression ::= lambda_expr | yield_expr | fun_type | feed_expr | pair
             | ternary | bool_or | bool_and | bool_not
             | comparison | log_or | log_xor | log_and | collection_union
             | sum_expr | product | unary | power | postfix | atom

-- Every position a bracket encloses: a list or tuple element, a call argument,
-- a subscript index, a record field, a brace item, a refinement predicate, a
-- comprehension clause. The one-line `match` (§4.10) is legal only here, so the
-- enclosing `)`, `]` or `}` always closes its arm list. The bracketed atom forms
-- in §2.4 recurse through this production rather than through `expression`.
bracketed_expression ::= oneline_match | expression

oneline_match ::= "match" expression ":" ( "case" case_pattern ":" expression )+
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

**The pair arrow builds a two-tuple.** `a -> b` is `(a, b)` — one value with two
spellings — so a map literal `[k -> v, …]` is a list of entry pairs, a map
comprehension `[k -> v for …]` a comprehension of them
([3.12 Comprehensions](#312-comprehensions)), and `for k -> v in m` a tuple
binder ([4.6 `for` — iteration](#46-for--iteration)). Reading such a list as a
`Map` is a separate step. The explicit constructor `map([…])` performs it today;
the annotation and usage routes are **[Decided]** and unimplemented
([3.11 List, tuple, record literals](#311-list-tuple-record-literals)).

The value operand admits a lambda where the key does not, so `["inc" -> \x -> x + 1]`
is a map of functions. A lambda on the key side would take the pair's own `->` as
its binder terminator.

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
> `[k -> v, …]`.
>
> Map entries use `->`, not `=`, so a map literal is a collection of entry
> pairs, matching the collections-are-functions model (§6.3). It also keeps the two
> operators' binding disciplines distinct: the left of `=` is always a
> *definition target* (a name, a record field label, a collection
> point `c[i]`), while the left of `->` is an *evaluated key
> expression*. And it removes a one-character trap: `[x = 5]` (map)
> vs `[x == 5]` (one-element list of `Bool`). Three earlier sketches
> are superseded: map entries as `[k: v, …]` (`:` is settling on
> annotation/type duty), as `[k=v, …]` (which read as keyword
> arguments), and Unicode `[k ↦ v, …]` (CHL is ASCII-only —
> [1.8 Operators and punctuation](#18-operators-and-punctuation)). An *empty* map is `empty_map()`
> ([3.11 List, tuple, record literals](#311-list-tuple-record-literals)), which the `[k -> v, …]`
> form has no way to write: with no entry there is no key to read a type
> off. The record-syntax / call-argument interaction is
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
  stays detectable and rejected. Effects becoming part of a function's
  type is **[Tentative]**
  ([6.9 Effects in function types [Tentative]](#69-effects-in-function-types-tentative)).

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

### Accumulator iteration order is not yet defined [Open]

A loop-carried accumulator sequences its loop's iterations "in the order the dependency
requires" ([4.6 `for` — iteration](#46-for--iteration)), and an accumulator whose update does
not commute (`last := v`) makes the result depend on that order. This document does not say
what the order is. The compiler runs a list's iterations in index order, but over a keyed
collection, such as a `Map` or a `groupby` result, no order is implied, so two equal maps could
give different results. Whether the order is the keys' order, an ordering supplied as a given
(the direction above), or a refusal of non-commuting accumulation over an unordered collection
is **[Open]**. The compiler refuses an accumulating loop whose source is not indexed by
iteration position (``a `mut` loop's source must be indexed by iteration position``), so the
question does not arise in a program it accepts.

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

CHL has not defined the result of partial operations such as out-of-range indexing, missing-key
lookup, division by zero, or integer overflow. A runtime trap, divergence, or static rejection by
refinement types remain possible decisions. None permits C-style undefined behaviour: an
implementation cannot assign arbitrary behaviour to an accepted program.

This gap differs from unordered collections and unspecified evaluation order, which are defined
parts of the language. The planned result of an aggregate over an empty collection is covered in
[Aggregates](#71-aggregates).

The selection rules of [Short-circuit `not`, `and`, `or`](#35-short-circuit-not-and-or),
[Ternary](#36-ternary) and `if`/`elif` let an unselected operand be undefined without making the
selecting expression undefined. These guarantees hold under any resolution of the question above.

### 3.1 Literals

`Int`, `String`, and `Bool` literals have singleton refinement types. For example, `5` has type
`{Int where _ == 5}`, displayed as `Int@5`. Unit `()` has the
[empty product type](#66-the-empty-product-is-unit) `{}`; it needs no additional refinement.

An inferred immutable binding preserves the literal's singleton. An exact annotation can replace
it with the base type, whereas a bounded annotation retains it:

| Binding | Inferred binding type |
|---|---|
| `x = 5` | `Int@5` |
| `x: Int = 5` | `Int` |
| `x <: Int = 5` | `Int@5` |

[Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded) defines the
annotation rules. Mutable bindings do not retain the singleton of an individual write.

Computed results do not inherit operand refinements: `2 + 3` has type `Int`.

> **Direction [Decided] — Boolean spelling.** The implemented literals are `True` and `False`.
> The planned spellings are `true` and `false`, following the lowercase convention for terms.

### 3.2 Names

Name resolution is static. A name refers to the nearest enclosing binding in scope at its use;
there is no dynamic lookup or introspection of the binding environment. Forward references are
not supported. Mutual recursion between top-level functions is **[Planned]**.

[Scoping and binding](#5-scoping-and-binding) owns the scope rules.

### 3.3 Arithmetic and logical operators

[Expression precedence](#23-expression-precedence) defines parsing precedence and associativity.

| Operator | Meaning |
|---|---|
| `a + b`, `a - b`, `a * b` | Integer addition, subtraction, and multiplication. `+` also joins two strings. |
| `a // b` | Integer division rounded toward negative infinity: `-7 // 3` is `-3`, not `-2`. This matches [Python's floor division](https://docs.python.org/3/reference/expressions.html#binary-arithmetic-operations), so the shared syntax retains its meaning. Division by zero and overflow are not defined (see [Partiality](#3-expression-semantics)). |
| `a ** b` | Integer exponentiation. The exponent must be provably non-negative. |
| `-a` | Signed integer negation. |
| `a & b`, `a \| b`, `a ^ b` | Boolean conjunction, disjunction, and exclusive-or. Both operands must be `Bool`; these are not integer bitwise operators. |
| `not a` | Boolean negation. |
| `a and b`, `a or b` | Boolean conjunction and disjunction. The right operand need not be defined when the left settles the result; see [Short-circuit `not`, `and`, `or`](#35-short-circuit-not-and-or). |
| `a ++ b` | Multiset union of collections with the same element type, not ordered concatenation. See [Collections are unordered](#collections-are-unordered). |

For every integer base `a`, `a ** 0` is `1`, including `0 ** 0`. The exponent must satisfy
`{Int where _ >= 0}`. A non-negative literal or a parameter with that
refinement is accepted:

```python
def scaled(e: {Int where _ >= 0}) => Int:
    2 ** e
```

A negative exponent or an exponent of unrefined type `Int` is rejected. Exponentiation is
right-associative, so `2 ** 3 ** 2` is rejected: the inner `3 ** 2` has type `Int`, which does
not establish the outer exponent's bound. `(2 ** 3) ** 2` is accepted.

The expression operators `/`, `%`, `>>`, `~`, and `@` are not supported; see
[Operators and punctuation](#18-operators-and-punctuation).

> **Direction [Tentative] — Fractional arithmetic.** A fractional type `Real` and division
> operator `/` are proposed, not implemented. Their representation, behaviour at zero,
> relationship to `//`, and conversion from integer literals are **[Open]**.
> There are no fractional literals.

### 3.4 Comparisons

The comparators are `==`, `!=`, `<`, `<=`, `>`, and `>=`. A chain `a < b < c`
compares adjacent operands and conjoins the results: `a < b and b < c`. It is not the
left-associated comparison `(a < b) < c`. This equivalence does not add a short-circuit guarantee
beyond the [Boolean-operator rules](#35-short-circuit-not-and-or).

Incompatible operand types produce a compile-time type error. Product equality is componentwise:
two tuples or records must have the same shape, and every corresponding component must support
equality. A wider record is not compared only on its shared fields. Products do not support the
ordering comparators; collection elements are not product fields, so this rule does not provide
collection equality.

`is`, `is not`, `in`, and `not in` are not comparison operators. A comprehension with a
guard or an aggregate can express a membership query.

> **Direction [Decided] — Membership expressions.** `e in s` is planned for set membership,
> and `k in m` for map-key membership. This does not change `in` as an iteration keyword in
> `for x in xs`.

### 3.5 Short-circuit `not`, `and`, `or`

`not e` negates a Boolean. `and` is true when all its operands are true; `or` is true when
at least one operand is true. All operands must have type `Bool`, and the result is `Bool`.
There is no truthiness conversion or Python-style return of an operand.

Once a prefix of the operands determines the result, the remaining operands need not be defined.
This is a definedness rule, not a requirement to evaluate operands in source order:

```python
b: Int = 0
False and (10 // b > 0)
```

is `False`, though `10 // b` is not defined.

### 3.6 Ternary

```python
then_expr if cond else else_expr
```

The condition must have type `Bool`. The result is `then_expr` when the condition is `True`
and `else_expr` otherwise. An unselected branch need not have a defined value and contributes
no feed or yield effect. Both branches must still type-check.

This guarded division evaluates to `0` without evaluating the division by zero:

```python
b: Int = 0
0 if b == 0 else 10 // b
```

The result type is the [join of the branch types](#joining-the-types-of-several-values).
Ternaries associate to the right: `x if a else y if b else z` parses as
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
element type is the type of `value`, or where several feeds target one
defer, the join of their value types
([Joining the types of several values](#joining-the-types-of-several-values)).

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
**data source** — `stdin()` or any source pre-registered by the host
(§7.4) — against the builtins `defer()` (§7.3) and `empty_map()` (§3.11),
or as the context of `with begin():` (§8.2). A zero-argument call against
any other name is a compile-time error.

### 3.9 Subscript and attribute access

Subscript syntax distinguishes proven application from checked lookup:

| Form | Meaning | Result |
|---|---|---|
| `c[k]` | Apply the collection to a key accepted by its domain type. | The value at `k`. |
| `c[k]?` | Check a compatible key for membership in a keyed collection. | `Option` of the value type. |
| `r.name` | Project a record field. | The named field's type. |
| `t.0` | Project a tuple field. | The positional field's type. |

A missing product field is a type error. Product projection and collection lookup are distinct:
`t[0]` is rejected, not interpreted as `t.0`. Projections compose, as in `r.p.1` and `t.0.b`.
An identifier cannot begin with a digit, so named and positional field syntax do not collide.

`c[k]` evaluates a finite function at a point and requires a proof that `k` is in its domain.
A `FullMap(K, V)` accepts a key of type `K`; a refined present-key domain instead requires
membership in that refinement. Proven lookup does not define an absent-key runtime result.

Checked lookup returns `some` with the value when the key is present and `none` when absent.
For a set, the value is unit. Presence can be established before the domain is final; absence
requires the final domain. A live feed with no final domain may never answer an absent-key lookup.

#### Subscript and unwrap syntax [Decided]

The replacement makes `c[k]` the optional lookup and retires `c[k]?`. A presence proof narrows
its result from `Option(T)` to the single arm `some(T)`. Postfix `!` unwraps that single-arm value:

```python
def unwrap(o: {`some{T}}) => T:
    `some(ret) = o
    ret
```

Under this design, `c[k]!` is accepted only when the result type excludes `none`. Failure to
establish presence is a type error at `!`, not a runtime unwrap failure. The destructuring rule
is [Destructuring patterns](#431-destructuring-patterns). The proposed `!` has postfix precedence;
`!=` remains one token, so `x! == y` requires a space before `==`.

> **[Interim]** The compiler has no postfix `!`. Today's `c[k]?` corresponds to the decided
> `c[k]`, and today's `c[k]` corresponds to the decided proven access `c[k]!`.

A direct call `c(k)` remains function application, not an optional membership test.

#### Method calls [Decided]

`x.m(args)` calls a method of `x`'s type. Calling a function stored in a field takes parentheses
around the projection: `(r.f)(args)`. See
[Nominal types and methods](#68-nominal-types-and-methods-decided).

#### Absence at a cut [Open]

The proposed readiness condition for optional lookup is a domain fixed at a cut, rather than
termination of its producer. A time-bounded view of a live feed or a transactional store read
could establish such a domain even when the underlying source never ends. The language does
not yet provide a general cut interface for this rule.

An unpinned live feed still cannot establish absence. A provisional `none` followed by a
correction would require incremental view maintenance, not an irrevocable Option answer.
A timeout-based answer would depend on wall-clock timing. These alternatives do not change
the current rule: a lookup decides absence only once the collection's domain is final.

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
(**[Planned]** — not yet parsed), which is also what makes a refinement
unwritable on a *lambda* parameter; one parses on a `def` parameter, on a
`def` result, and in a binding's annotation (§6.4). Some built-ins (e.g.
`groupby`, §7.2) produce refined lambdas internally. `\x -> x -> 1` (a lambda
returning a pair, §2.4) is unusual but unambiguous — the first `->` closes the binder, the rest is
body.

A capitalized lambda binder is an error. A capitalized name is a type, bound only by an alias
([6.7 Type-alias statements](#67-type-alias-statements)), a `def`'s type parameter, or a
polymorphic type `forall (T) V` (**[Planned]**,
[Polymorphic type annotations](#polymorphic-type-annotations)).

### 3.11 List, tuple, record literals

| Form | Meaning |
|---|---|
| `[]`, `[e₀, e₁, …]` | A positional collection. Element types must unify; indices are zero-based. Iteration order is unspecified by default. |
| `(e,)`, `(e₀, e₁, …)`, `e₀, e₁, …` | A heterogeneous tuple. Positions are significant: `(1, 2)` differs from `(2, 1)`. |
| `(name=e, …)` | A record with named fields, whose types may differ. |

Trailing commas are allowed. A one-element tuple requires a comma, so `(e,)` differs from the
parenthesized expression `(e)`. The same distinction applies to tuple types: `{T,}` is a
one-element product and `{T}` is a parse error. A one-field record needs no comma because
`name=value` or `name: T` identifies the form.

Lists require constant elements: an element must not vary with an enclosing loop or
comprehension variable, including through a local binding or a call. The same restriction
applies to mutable values written by an enclosing loop. A parameter can become constant at a
call site: `def f(n): [n, 1]` accepts `f(3)` but not `f(x)` inside `for x in xs`.
Use a comprehension, such as `[n for i in [1, 2]]`, to repeat a varying value.

> **Partly implemented.** `[1 + 1]` is accepted, but `[sum([1, 2])]` is not yet accepted as a
> constant list literal.

Tuples and records are products, projected with `.` rather than subscripted; see
[Subscript and attribute access](#39-subscript-and-attribute-access).
A field may itself hold a collection, as in `(cash=10, lines=[1, 2, 3])`.
Each field retains its own domain. A product containing a two-element collection and a
three-element collection is not one collection of paired elements.

Braces are reserved for types: `{name: T}` and `{T, U}` are product types, not value constructors.
Using them as values fails lowering. `()` is unit; there is no distinct zero-field record or
tuple. Its type is `{}`; see [The empty product is unit](#66-the-empty-product-is-unit).

#### Keyed constructors

`k -> v` and `(k, v)` produce the same tuple node. Consequently, `[k -> v, …]` is a positional
list of pairs, not intrinsically a map. Current keyed construction requires an explicit call:

| Expression | Key | Value |
|---|---|---|
| `set(xs)` | An element of `xs`. | Unit. |
| `map(entries)` | The first component of each pair. | The second component. |

Both return concrete data functions over the present keys. A sum annotation requires `box`,
for example `m: Map(Int, Int) = box(map([1 -> 10, 2 -> 20]))`.
`list(...)` is not a builtin; `box([1, 2])` can satisfy a `List(Int)` annotation.

Repeated set elements produce one key. Duplicate keys in a constant map are a compile-time error;
see [Type-directed literals](#type-directed-literals-decided).

#### Empty forms

`[]` supplies no element type. Its uses or annotation constrain the type; an otherwise
unconstrained element type becomes unit. For example, `xs: List(Int) = box([])` selects `Int`.
This does not provide a key type to `map([])` or `set([])`; those constructors are rejected.

`empty_map()` directly constructs an empty keyed sum. Its annotation must determine the key
and value types:

```python
cart: Mut(Map(String, Int), Txn) := empty_map()
prices: Map(String, Int) = empty_map()
seen: Set(String) = empty_map()
```

The set annotation works because `Set(K)` currently lowers as `Map(K, unit)`. An unannotated
`empty_map()` is rejected; later keyed writes do not replace its required type annotation.
Inference details and the distinction between empty positional and keyed domains belong to
[The empty literal names no element type](../src/ccl/design/collections.md#the-empty-literal-names-no-element-type).

#### Type-directed literals [Decided]

Literal typing inserts constructors according to annotation or usage. A positional literal can
supply an `Array`, `List` or `Set`; a pair literal can supply a list of pairs, a set keyed by whole
pairs, or a map keyed by first components. The chosen collection type, not a distinct pair-literal
AST node, determines re-keying.

The explicit forms are `list([…])`, `set([…])` and `map([…])`. An annotation such
as `m: Map(K, V) = [k -> v, …]` or a keyed lookup selects `map` implicitly.

The constant-map rule rejects duplicate keys at compile time, applying the immutable
non-overlap rule described under [Collection types](#63-direction-collection-types-decided).
Mutable or fed collections instead use their declared merge law. The key type must support
equality; general discharge through contextual parameters remains planned.

The delimiter split retains `(…)` for products, `[…]` for collections and `{…}` for types.
Whether a future empty constructor can cover all collection kinds remains open; `empty_map()`
is the current keyed constructor, not a general empty-collection term.

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

> **Direction — map/set comprehensions and entry iteration [Decided].**
> A **map comprehension** is a comprehension whose element is a pair:
> `[k -> v for …]` — the element `k -> v` is the 2-tuple `(k, v)`
> ([3.11 List, tuple, record literals](#311-list-tuple-record-literals)), which
> parses today — read as a `Map` exactly as a map literal is. A **set
> comprehension** has no brace form (`{ … }` is types-only,
> [2.4 Atoms](#24-atoms)), so it is written
> `set([e for …])`. Iterating a **keyed** collection yields its
> *entries* as pairs, destructured with the 2-tuple pattern in the `for`
> binder: `for k -> v in m` (≡ `for (k, v) in m`), and likewise
> `for k -> g in groupby(c, key)` — so the group-by rollup composes as
> `[k -> agg(g) for k -> g in groupby(c, key)]` (the north-star
> `storefront` `/stats`). A single binder takes the whole entry rather than the
> group (§4.6), so iterating the groups alone is `values(groupby(c, key))`.

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
during error recovery (see [chl-parser/design-chl-parser.md](../chl-parser/design-chl-parser.md)).
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

> **Direction [Decided] — labels and tags belong to a module.** With
> modules, the flat space is one per module: a tag or a record field label
> written unqualified means the current module's, and `m::ok` or
> `r.m::f` names module `m`'s
> ([9.12 Field labels and tags belong to a module](#912-field-labels-and-tags-belong-to-a-module)).
> Within one file this changes nothing. Nominal variants, whose tags live
> inside their type, are **[Tentative]**.

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

**Variants are structural, so a constructor synthesizes its own type.** `` `sme(1) ``
is the type ``{`sme{Int@1}}``, whatever the writer meant, and the payload type is
whatever term sits in the parens. A tag mismatch is therefore reported where the
constructor meets a counterpart that lacks the tag — an annotation, a `match` arm's
expected type, a join — rather than at the constructor.

> **Direction [Tentative].** A **parameterised** type alias (§6.7 [Open]) —
> `` Option(T) = {`some{T} | `none} ``, `` Result(T) = {`ok{T} | `err{String}} `` —
> gives the arms a name to write, and would replace the built-in `Option(T)` above
> with a prelude definition. An alias names a shape, so two aliases with the same
> arms are the same type. The unparameterised alias §6.7 specifies already names
> the arms at a fixed payload type.

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

Annotation types are arbitrary expressions evaluated in the
surrounding scope. `p: T` fixes the parameter's type at `T`; `p <: T`
leaves it inferred and bounded above by `T` (see [Two annotation
forms: exact and bounded](#two-annotation-forms-exact-and-bounded)).
The two forms may be mixed across a parameter list. A capitalized
parameter is a type parameter, not a value
([Type parameters](#type-parameters)). A return-type
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
> appears — assignment and `for` binders alike. Today's grammar special-cases
> the `reqs, resps = http_serve(…)` statement form (§7.4); that is an
> implementation restriction, not a design one. The decided pattern
> surface is §4.3.1.

**No assignment-as-expression** — neither `=` nor `:=` is an expression
(the mutation `:=` is a statement, §1.8). **No multi-target chained
assignment** (`a = b = c` is not in the grammar).

**A block statement may sit on the right.** Every form in the table above
accepts an `if` chain or a `match` where it accepts an expression, and binds
that block's value — its last statement's, by the rule in §4.5:

```python
label = if score > 90:
        "high"
    elif score > 50:
        "mid"
    else:
        "low"

n = match msg:
    case `ping(seq):
        seq
    case `close:
        0
```

**A block on the right indents one level in from its statement**, and its
branch bodies one level further. `elif` and `else` return to that first level,
never to the statement's own column — a chain written there ends the assignment
instead of continuing it, and is rejected. A `match` needs no rule of its own:
its `case` arms already sit one level in and their bodies one level further.

Which columns those are is the writer's choice, as everywhere else in the
layout: the requirement is that the chain indent past the statement and the
bodies past the chain.

The block's DEDENT ends the statement, so nothing follows it on the line. Every
branch must produce a value, and an `if` with no `else` is rejected (§4.5); a
one-line spelling of the same thing is the ternary (§3.6) or, for `match`, the
bracketed form in §4.10.

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

`if`/`elif`/`else` is a statement. It is value-yielding by position: as the
last statement of a block, and on the right of an assignment (§4.3). The
one-line spelling of the same choice is the ternary (§3.6).

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
value, an assignment's right-hand side), every branch — including `else` —
must end in a value-yielding statement, and the missing-`else` case is
rejected as "if used as an expression, all branches must produce a value."

### 4.6 `for` — iteration

```python
for target in iter:
    body
```

`target` is an `AssignTarget`; `iter` is any expression denoting a
collection. The body executes once per element of `iter`, with
`target` bound to the current element.

**What the element is depends on the collection kind [Planned].** The iteration
element is chosen per type — it is *not* uniformly the value:

| `iter` type | element bound to `target` |
|---|---|
| `List(T)` / `Array(n, T)` / `Collection(T)` | the value `T` |
| `Set(K)` | the key `K` |
| `Map(K, V)` | the entry `(K, V)` |

A **single** target binds the whole element; a **tuple / `->`** target
destructures it, so a map iterates entries unpacked as `for k -> v in m:` (the
north-star `storefront` rollup, §7.2). The keyed element carries its membership
proof, so a key from `for k -> v in m` (or `for k in s`) narrows `m[k]` to
`` `some ``, and `m[k]! : V` type-checks (§3.9). Reaching a map's keys or values as their own
collections is `keys(m)` / `values(m)` / `items(m)` (§6.3).

> **[Interim].** Today `for`-in binds the **value** (codomain) for every
> collection — so a map iterates its values (as `groupby` results do) and a set
> iterates `unit`. A destructuring target parses in either spelling, `(k, v)` and
> `k -> v` alike, and lowering takes only a simple name. Entry/key iteration is
> the [Planned] work; it only *adds* the type-directed element choice, so
> `for k -> v in m` is the form to write once it lands. Design:
> [collections.md, "Operations: how the trait layer dispatches [Planned]"](../src/ccl/design/collections.md#operations-how-the-trait-layer-dispatches-planned).

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

**Nested loops.** A `for` inside a `for` body is a recurrence of its own, running
once per position of the loop around it. An accumulator declared before the outer
loop is carried through both: at each enclosing position the inner recurrence starts
from the value the accumulator holds there, and the outer one takes the value the
inner left. The rule is per level rather than per depth, so a nest is unbounded in
depth. The inner body may read the outer binder, and the inner source may be the outer
element itself, which gives each enclosing position its own inner domain.

```
total := 0
for xs in [[1, 2], [3, 4]]:
    for x in xs:
        total += x
total                     # 10
```

Accumulators at different depths keep their own domains, so two in one nest are two
recurrences rather than one with a wider key set.

A `<<` feed from inside the nest appends at the innermost position, so the channel it
builds carries one value per position of the nest rather than one per group.

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

A `:=` inside a loop body whose target is not an already-declared accumulator
**introduces** a mutable variable scoped to the block that writes it. Its updates
carry across the statements of that block, and it restarts at its seed on the
next iteration, so the loop around it is its sequencing domain — a recurrence
nested inside the enclosing one:

```
total := 0
for x in [1, 2]:
    y := x
    y += 10
    total += y
total                     # 23
```

An `if` branch is a block of its own, so a `:=` there introduces a variable that
branch alone writes and reads.

A variable introduced in a loop body may be accumulated by an inner `for`, which is a
nested loop like any other: it runs once per iteration of the loop around it, starting
from the value the variable holds there.

```
total := 0
for x in [1, 2]:
    inner := 0
    for y in [10, 20]:
        inner += y
    total += inner
total                     # 60
```

Two introductions are lowering errors. A **transactional** one, `y: Mut(Int,
Txn) := 0` inside a loop body, names commit time, a sequencing domain the loop
around it does not supply. One inside a loop that writes no mutable variable
declared before it (a generator, or a loop that only feeds) has no recurrence of
that loop to live in.

> `Y is a mutable variable introduced inside a for-loop body, which is not
> supported: declare it before the loop (`Y := …`) so its updates carry
> across iterations, or bind a per-iteration value immutably with `Y = …``

The same holds for `op=`, which is a mutable write and not a rebind: `x += e`
inside a loop body requires `x` to be a mutable variable — one declared before
the loop, or one an enclosing body introduced. A target that is neither gets the
matching error rather than a per-iteration binding.

Falling back to a per-iteration binding is deliberately *not* what happens in
either case, for the reason a plain `=` to an outer name is rejected: it would
silently discard every update at the iteration boundary, which is the one thing
`:=` exists to rule out. For `op=` it is worse than a lost update — `op=` reads
the old value, so a per-iteration rebind reads the binding's *initial* value on
every iteration.

*Currently unsupported* (see §13): a mutable variable introduced inside a
`with begin():` block, and `while` loops.

### 4.7 `pass`

A statement that contributes nothing, for a block that takes statements and
expects no value:

```python
total := 0
for m in [`debit(3), `credit(4)]:
    match m:
        case `debit(d):
            total += d
        case `credit(c):
            pass
total                 # 3
```

A `match` arm is where one is needed. An `if` arm can be left out — a guard
with no `else` does nothing at the positions it rejects — while a `match`'s
arms partition the scrutinee's tags, so an arm that does nothing is still
written.

`pass` contributes nothing at every position, last included, so a block reads
as though it were not written. The blocks that expect no value are a `for`-loop
body, a `with begin():` block, and the `if` / `match` arms inside one.
Everywhere else a block's value is its last statement, and a block of nothing
but `pass` has no statement to be one: `def todo(x): pass` is rejected, because
the function body must yield a value.

A loop body of nothing but `pass` is a loop whose body has no effect; the loop
still runs, once per element of its source. A `with begin():` block of nothing
but `pass` is rejected, by the rule that a transaction must write or feed
([8.2 Transactions: `with begin():`](#82-transactions-with-begin)).

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

**Both statement contexts admit a `match`** — a `for`-loop body and a `with
begin():` block. An arm may `yield` or `<<`, and the fed value may read the arm's
payload, the loop's accumulators, or both.

#### The one-line form

```
match scrut: case `foo(x): x case `bar(y): to_x(y)
```

The block with its line breaks removed, and an expression in place of each
arm's block. `case` delimits the arms, so no separator is needed, and the arm
list runs to the first token that cannot begin an arm.

**A one-line `match` is legal only inside a bracket** — `(…)`, `[…]`, `{…}` —
so a `)`, `]` or `}` is always in place to close the arm list. That covers a
call argument, a list or tuple element, a subscript index, a record field, a
comprehension clause, and a refinement predicate (§6.4). In a value position
that has no bracket of its own, the parentheses are written:

```python
n = (match msg: case `ping(seq): seq case `close: 0)
```

The bracket is what makes nesting readable. An arm body is an ordinary
expression, which cannot itself derive a one-line `match`, so a nested one
carries its own bracket and two arm lists never compete for the same `case`.
Without the requirement, `` match a: case `p: match b: case `q: 1 case `r: 2 ``
has two readings, and under the greedy one the outer `match` has no way to
spell an arm after `` `p ``.

Restricting the arm body instead of requiring the bracket does not hold: a
lambda body and a `=>` codomain each take a whole expression, so an inner
`match` reappears through either of them.

The indented and one-line forms differ in the arm body and in nothing else:
same arms, same partition rule, same value.

> **Direction [Tentative].**
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

> **Direction [Decided].** The top-level scope is its module's. Import
> names, run names, and parameters are in scope throughout the module,
> as type aliases are, and another module's member is reached by a
> qualified name, `m::f`, including through a parameter of `Module{…}` type
> ([9.6 Qualified references](#96-qualified-references)).

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
- `UInt` — unsigned 64-bit integer.
- `Real` — a fractional number (**[Tentative]**, §3.3). The checker has no
  fractional type, there is no fractional literal (§1.7), and `/` is not
  even lexed (§1.8, §13).
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
- `Map(K, V)` — finite-map type. The map literal `[k -> v, …]`
  ([3.11 List, tuple, record literals](#311-list-tuple-record-literals)) parses as the list of
  entry pairs that a `Map` annotation or `map([…])` re-keys.
- `FullMap(K, V)` — *total*-map type (**[Tentative]**, §6.3): every value
  of `K` is a key, so lookup yields `V` rather than `Option(V)` and has
  no missing case. The annotation and its total lookup are implemented;
  what obligation totality places on whatever builds the map is **[Open]**,
  so the annotation is a promise the checker propagates rather than checks.
- `Time` — a position in the commit order, what a transaction handle's
  `current_time()` answers (**[Tentative]**, §8.2). §8.2 calls the handle
  itself a `Txn` value, and the two spellings are not reconciled.
- `{T₀, T₁, …} ⇒ U` — function type. A function takes exactly one
  argument (§3.8): an n-parameter function's domain is the
  corresponding tuple type, and a keyword-argument function's domain
  is a record type — `{x: T, y: U} ⇒ V`. Surface syntax uses the `=>`
  function. Whether the function is a collection or a callable capability
  is inferred, never written (§6.3).
- `Module{name: T, Name <: U, …}` — the type of a module's public members,
  through which one module is passed to another (**[Decided]**,
  [9.8 Module types](#98-module-types)).
- `forall (T) U` — polymorphic type: for every type `T`, a `U`
  ([6.10 Polymorphic types](#610-polymorphic-types)), written only as a whole `let` annotation.

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
> direction for factoring recurring contracts, with no invariant syntax
> settled yet ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)).
> Pinned by `discount_contract` (the mechanism in
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

Named types come in two strengths. A plain `=` binding to a capitalized
name is a structural **alias** — `Item = {price: Int, cost: Int}` —
interchangeable with the type it names, and specified in §6.7.

A `type` declaration is **nominal**, `type Price = {amount: Int}`, and is
specified in [6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided).

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

### Joining the types of several values

Several constructs yield one of several values without saying which. Each is typed by
the **join** of the values it could yield: the type that holds of all of them and says
nothing more.

| Construct | The values joined |
|---|---|
| ternary `a if c else b` (§3.6) | the two branches |
| `if`/`elif`/`else` used for a value (§4.5) | every branch, `else` included |
| `match` (§4.10) | every arm's result |
| a collection literal or comprehension (§3.11, §3.12) | the elements |
| a mutable variable (§8.1) | every value written to it |
| a feed (§3.7) | every contribution |

The join keeps what every value establishes and drops the rest, so a refinement
survives only where all of them carry it: `1 if c else 2` is `Int`, `5 if c else 5` is
`Int@5` (§3.1), and `[5, 5]` has element type `Int@5` where `[5, 6]` has `Int`.

**Where the values establish nothing in common there is no join, and the construct is
a compile-time error.** `1 if c else "x"` is rejected rather than given some
`Int`-or-`String` type, and the same holds for a `match` whose arms disagree or a
mutable variable written at two unrelated types. Cambra has no anonymous union type to
fall back on; to carry values of several types in one place, say which by tagging them
— a variant (§6.5) if the tags are meaningful to the program, `box` (§7.5) if they
are not.

> **Direction [Planned] — joining two collections.** Two collections that are not the
> same collection — `xs if c else ys` over lists of different length — establish
> nothing in common either, because a collection's elements are indexed and the two
> disagree about which indices exist. The two answers a program might want differ: one
> keeps both possibilities and which occurred, the other forgets which collection it is
> and with it the length. Neither is the default, so the program says which. `box` asks
> for the first (§7.5); a `List(T)` or `Collection(T)` annotation asks for the second
> (§6.3).

### 6.3 Direction: collection types [Decided]

The collection interface has six forms:

| Type | Domain and elements | Access |
|---|---|---|
| `Array(n, T)` | `n` indexed values of type `T`; length is static. | `arr[i]!` when the index type establishes the bound. |
| `List(T)` | Indexed values of type `T`; length is not named statically. | `lst[i]` returns `Option(T)`. |
| `Set(K)` | Distinct keys with no associated data beyond unit. | Key membership, or `s[k]` returning `Option(unit)`. |
| `Map(K, V)` | One value per present key. | `m[k]` returns `Option(V)`; `m[k]!` requires presence. |
| `FullMap(K, V)` | A value for every inhabitant of `K`. | `m[k]!` for a key of type `K`. |
| `Collection(T)` | Elements of type `T` with unspecified domain shape. | Generic collection operations. |

`FullMap` totality is relative to its domain type. A group-by's domain is refined to keys
present in its producer, not every value of the key's base type. A `List` hides its domain
length in a sum witness; it does not store a separate length field in a product representation.
The current representations are specified in
[The six collection types](../src/ccl/design/collections.md#the-six-collection-types).

The implemented annotation forms are not six nominal types. `Set(K)` and `Map(K, unit)` lower
to the same representation. `Array` and `FullMap` have explicit domains; the other four are
dependent sums. Introducing one of those sums from a concrete collection requires `box`.
Existing sums can widen under the sum-kind relation; that relation is not automatic insertion
of a constructor into an unboxed term.

#### Collection operations

- Arrays and lists have positional order. Sets, maps and generic collections have no
  implicit order. Ordering follows from the type and is not stored. Order-dependent operations
  over unordered collections take an explicit
  ordering instance. Default parallel iteration and loop-carried dependencies are specified in
  [Iteration](#46-for--iteration); storage order does not establish a source-language ordering.
- Membership `in` tests keys for sets/maps and values for arrays/lists/collections.
  A successful key-membership guard refines the key for proven access.
- Maps iterate entries, sets keys, and arrays/lists/collections values. `keys(m)`, `values(m)` and
  `items(m)` expose lazy collection views. Numeric `sum(m)` rejects entries; `sum(values(m))`
  requests value aggregation.
- Type-directed literals share `[…]` across collection forms; explicit or inferred
  constructors select positional storage or re-keying. The constructors and constant-element rule
  are in [List, tuple, record literals](#311-list-tuple-record-literals).
- Immutable collections support non-overlapping element-wise definitions `c[i] = v`.
  Feed uses `c << v`, and keyed mutation uses `c[i] := v`. Their current supported forms
  belong to [Mutability, transactions, and feeds](#8-mutability-transactions-and-feeds).

Making `Set` and `Map` distinct nominal types remains tentative. It would also require a
decision about widening: the current structural `Map(K, V) <: Collection(V)` relation need
not be the rule for a nominal map whose iteration element is an entry. The alternatives are
recorded in
[Telling Set and Map apart](../src/ccl/design/collections.md#telling-set-and-map-apart-open).
General contextual parameters for equality and ordering belong to the planned operation
interface, not the compiler's implemented arithmetic trait tables.

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
        case `none: True
}
```

That `match` is the one-line form (§4.10). Newlines and indentation are
ignored inside brackets (§1.4), so a `match` written inside `{…}` gets no
`INDENT`/`DEDENT` to delimit its arms; the refinement's own `}` closes the arm
list instead, and the line breaks above are for the reader. The predicate needs
no parentheses of its own, because the braces are already the bracket the
one-line form requires.

`_` is the value being refined, so a predicate that mentions *another* value
relies on that value having a name where the refinement sits. In a function
signature the parameters do, which is what lets a return annotation carry a
postcondition: `{Int where _ >= item.cost * qty}` refines the result by a
predicate naming two parameters (§6). Ordinary lexical scope (§5) is what
supplies those names, and nothing narrows them to parameters: a refinement
written at the top level may name a top-level binding, which makes that
binding's *value* part of the type. The example uses membership `in`, which
is **[Planned]** ([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)):

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
arms out, or name them with a type alias (§6.7) at a fixed payload type.

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

- **`=`, and no keyword.** An alias is a timeless equation between a name and a
  type, which is what `=` already means (§4.3 Direction), so it is `assign_stmt`
  (§2.2) and not a new statement form. What separates it from a value binding is
  the **case of the name**: `Caps` means type, without exception (§6.1). A
  `type` keyword is not involved; that spelling belongs to the nominal
  declaration ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)),
  which an alias is not.
- **An alias names an existing type; it does not make a new one.** The alias and
  its right-hand side are the same type, interchangeable in every position, with
  no nominal distinction, no conversion, and no invariant of the alias's own.
  Type equality is structural and so is unaffected by spelling: `Count` and
  `{Int where _ >= 0}` are one type, and `n: Count` carries the refinement into
  the signature exactly as the brace form would (§6.4). An alias is accepted and
  rejected in exactly the positions the type it names is.
- **The right-hand side is any type expression**, including one that names other
  aliases (`Priced` above) and one carrying a refinement whose predicate names
  values in scope (§6.4). An alias opens no scope of its own: the predicate sees
  what the statement sees, and nothing more.
- **A capitalized name is bound only by an alias.** Every other binding form —
  `:=`, `op=`, `<<=`, a `for` target, a comprehension generator — rejects a
  capitalized binder and names this one. A `def` name is not yet checked; a
  capitalized one binds a value the type language cannot see. A capitalized
  parameter is a type parameter ([Type parameters](#type-parameters)).
- **The type language's own names are reserved.** `Int`, `UInt`, `String`,
  `Bool`, `Unit` and `Txn`, and the constructors `Array`, `Collection`, `Feed`,
  `FullMap`, `List`, `Map`, `Mut`, `Option` and `Set`, are refused as alias
  targets. The four writable primitives keep their meaning; `Unit` and `Txn` are
  reserved without being writable as annotations at all — the unit type is
  written `{}` (§6.6) and `Txn` is read only in a `Mut(V, Txn)` second slot.
- **An alias is block-scoped** (§5), and each block declares a given name once.
  An alias in an inner block shadows a same-named outer one from its statement
  to the end of that block, and the outer one is back after it.
- **The name is in scope from its statement to the end of its block**, as a
  value binding's is (§3.2). An annotation above the statement does not read it,
  and neither does the right-hand side, so `Loop = Loop` and a chain naming an
  alias declared below it are unresolved names. A recursive alias is therefore
  unwritable; §4.3 exempts recursive types from the `rec` marker, but what one
  would denote is unworked.

An alias is erased before type checking. Each use stands for the type the name
was declared with, and a predicate in that type reads the bindings its
declaration sees, so a local below the alias spelled like one of them does not
change what the alias means. No later phase knows the name.

**[Open]** — whether an alias may be **parameterised** (`Pair(T) = {T, T}`),
which is the difference between naming a type and naming a type constructor. A
parameterised left-hand side is currently an "invalid assignment target" parse
error. If added, a parameterised alias is written in this head form; `forall (T) V` is a
polymorphic type, not a type constructor
([Polymorphic type annotations](#polymorphic-type-annotations)).

The north-star `storefront` exercises four aliases, two of them refined.

### 6.8 Nominal types and methods [Decided]

A `type` declaration binds a capitalized name to a new **nominal** type:

```python
type Price = {amount: Int}
```

`Price` is distinct from `{amount: Int}` and from every other type of that shape, which is
the difference from an alias ([6.7 Type-alias statements](#67-type-alias-statements)).

A nominal type is the home for domain invariants: a `Price` carrying `assert amount >= 0`
in its declaration states the contract once, rather than as an assert at every function
(the contracts direction in [6. Types (informal sketch)](#6-types-informal-sketch)). The
syntax of that invariant is **[Open]**.

**A method is a `def` whose first parameter is `self`, annotated with a nominal type.**

```python
def discounted(self: Price, pct: Int) => Price:
    …
```

Every `def` of that signature is a method of the type its `self` names. A method binds no
module-level name: `discounted(p, 10)` does not call it, and two types in one module may each have
a method `discounted`. Two methods of one type with one name are an error naming both sites.
Whether a module other than the type's own may declare methods of it is **[Open]**.

A method is reached two ways:

| Written | Means |
| --- | --- |
| `p.discounted(10)` | the method call: `discounted` of `p`'s type, with `p` as `self` |
| `Price::discounted(p, 10)` | the same call, naming the type, with `self` passed first |
| `Price::discounted` | the method as a function value, of type `(Price, Int) => Price` |

`Price::discounted` names the method without an instance. It is how a call states which type's
method it means, and the method as an unapplied value has no other spelling.

**Methods and fields are separate namespaces, and the parentheses decide which is meant.**
`r.f(args)` is a method call, and `r.f` is a field and never a method. A value of `type Counter =
{f: Int => Int}` holds both when `Counter` also has a method `f`: `r.f` is the function the field
holds, and `Counter::f` is the method. Calling the function a field holds is written `(r.f)(args)`
([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)).

**A type in scope brings its methods into scope.** `x.m()` resolves `m` among the methods
of nominal types in scope unqualified. A type in scope only qualified, `mod::Price` through
`import mod` ([9.2 Imports](#92-imports)), qualifies its method
calls too: `x.mod::Price::discounted(10)`, or `mod::Price::discounted(x, 10)`. With `import
mod use Price`, `x.discounted(10)` and `Price::discounted(x, 10)` both resolve.

**After `.`, a capitalized segment marks a method.** A `::` path after `.` whose segments are all
lowercase is a qualified field label, `r.mod2::f1`
([9.12 Field labels and tags belong to a module](#912-field-labels-and-tags-belong-to-a-module)).
A path with a capitalized segment names a method: that segment is the type, the segment after it is
the method, and call parentheses follow, `x.mod::Price::discounted(10)`. Module path segments are
lowercase and type names capitalized ([9.15 Module files](#915-module-files)), so the case of the
segments decides. A qualified field label followed by call parentheses is an error, since a method
belongs to a type and not to a module. Calling the function such a field holds is written
`(r.mod2::f1)(args)`.

**A method call needs its receiver's type.** `x.m()` resolves `m` from the type of `x`. When
nothing before the call in program text determines that type to be a nominal type, the call is a
type error that asks for an annotation on `x`.

### 6.9 Effects in function types [Tentative]

A function's type includes its **effects**. An effect is one of:

- IO, through a source or a sink ([7. Built-in functions and
  sources](#7-built-in-functions-and-sources));
- mutation of state provided from outside the function, through a `Mut(…)` parameter or a
  captured mutable variable ([8. Mutability, transactions, and
  feeds](#8-mutability-transactions-and-feeds)).

Today's effecting calls ([3. Expression semantics](#3-expression-semantics)) carry the
mutation effect, read off a `Mut(…)` parameter or a `Txn` write in the body. Under this
direction the function's type states it. Everything else about effects is **[Open]**: how an
effect is written in a function type, how effects compose and are inferred, and whether a feed
write is an effect of its own.

**[Open] — crash handling.** What a program does when an effect fails at run time, and in
particular whether the dataflow downstream of the failure pauses, is undecided.

### 6.10 Polymorphic types

A **polymorphic** binding has one definition and a type that each use instantiates at its own
types. A `def`, and a binding whose right-hand side is a lambda, is polymorphic over every type its
body leaves open. Each call is checked against its own instantiation.

```python
def swap(a, b):
    (b, a)

(swap(1, "x"), swap(True, 2))   # (("x", 1), (2, True))
```

The inferred type carries what the body requires of each open type. `def add(a, b): a + b`
requires `Addable` of its operand types ([Trait requirements](#trait-requirements)), so
`add(1, "s")` is rejected at the call. `def f(a): (a + 1, a + "s")` is rejected at the definition,
because no type satisfies both of its requirements.

A binding whose right-hand side names a polymorphic binding is polymorphic too. `g = f` binds `g`
at `f`'s type, and each use of `g` instantiates that type as a use of `f` would:

```python
def add(a, b):
    a + b

plus = add
(plus(1, 2), plus("a", "b"))   # (3, "ab")
```

Every other binding is **monomorphic**: it has one type, shared by every use and settled by all of
them together. A binding whose right-hand side is a call, a collection, a tuple or record, or a name
of a monomorphic binding is monomorphic. A tuple or record of polymorphic functions is therefore
monomorphic, and making each field polymorphic on its own is **[Open]**.

#### Type parameters

```ebnf
def_stmt        ::= "def" ident "(" [ params ] ")" [ "=>" expression ] [ requires_clause ] ":" block
params          ::= ( type_param "," )* value_param ( "," value_param )* [ "," ]
type_param      ::= Ident [ ( ":" | "<:" ) expression ]  (* Ident: a capitalized identifier *)
value_param     ::= ident [ ( ":" | "<:" ) expression ]
```

A capitalized parameter is a **type parameter**. It names a type in the parameter annotations, the
result annotation, the `requires` clause, and the body. Type parameters precede the value
parameters.

```python
def first(T, a: T, b: T) => T:
    a

first(3, 7)       # T = Int
first("a", "b")   # T = String
```

- **A type parameter is not an argument.** `first` takes two arguments. Each call infers the
  type parameters from its arguments. Supplying one explicitly is **[Open]**: it would be a named
  component in an otherwise positional call, which
  [3.8 Function calls](#38-function-calls) leaves open.
- **Every type parameter is determined by the arguments.** It appears in a value parameter's
  annotation, or it is the associated type of a requirement whose other positions are determined
  ([Trait requirements](#trait-requirements)). Any other type parameter is an
  error at the definition.
- **A type parameter is opaque in the body.** A value of type `T` supports what `T`'s bound and the
  `requires` clause state, and nothing else. `def inc(T, x: T) => T: x + 1` is an error at `+`,
  because no requirement states that `T` and `Int` are `Addable`.
- **Two type parameters have no common type but what their bounds give them.** With `a: T` and
  `b: U`, `a if c else b` is an error: no type the program can write covers both. With bounds it
  is the least type their bounds place above both: `T` under `U <: T`, and `Int` under `T <: Int`
  and `U <: Int`. The definition is rejected whether or not anything calls it.
- **A type parameter does not leave its definition.** A value of type `T` flowing into something
  declared outside the `def`, as in `outer << x` with `x: T`, is an error naming `T`: outside the
  definition `T` names no type.
- **A type parameter is scoped like an alias declared in the function's block**
  ([6.7 Type-alias statements](#67-type-alias-statements)). It shadows an outer alias of the same
  name. An alias of the same name declared in the body is an error naming both.

#### Kinds and bounds

A type parameter ranges over a **kind**, a set of types. `T: K` states that `T` is one of the types
in the kind `K`:

- `Type` is every type. `T` alone is `T: Type`.
- `SubtypesOf(U)` is every subtype of `U`, `U` included. `T <: U`, the **bound** form, is
  `T: SubtypesOf(U)`.

Any other kind, such as a listing `T: [Int, String]`, is **[Open]** and an error. A type written as
a kind, as in `T: Int`, is an error.

`T <: U` restricts `T` to subtypes of `U`. The body uses a value of type `T` as a `U`. The caller
receives its own type for `T`.

```python
def stamped(T <: {at: Int}, a: T) => {Int, T}:
    (a.at, a)

pair = stamped((at=2, sku="mug"))
pair.1.sku   # "mug": T is the argument's record type, sku included
```

With `a: {at: Int}` and a `{Int, {at: Int}}` result instead, `pair.1` is `{at: Int}` and
`pair.1.sku` is an error. A call whose argument is not below the bound is rejected at the call.

- A kind names only the type parameters before it. A bound naming its own parameter is a recursive
  type, which [6.7 Type-alias statements](#67-type-alias-statements) leaves unwritable.
- No kind gives a type parameter a lower bound.

#### Trait requirements

```ebnf
requires_clause ::= "requires" requirement ( "," requirement )*
requirement     ::= Ident [ "(" req_arg ( "," req_arg )* ")" ]
req_arg         ::= expression | Ident "=" expression
```

A **trait** is a named requirement on a list of types. Each operator places one on its operand
types. The traits are built in:

| Trait | Required by | Operands | Associated type | Satisfied by |
| --- | --- | --- | --- | --- |
| `Addable` | `+` | 2 | `Output` | `Int`, `UInt`, `String` |
| `Subtractable` | `-` | 2 | `Output` | `Int`, `UInt` |
| `Multipliable` | `*` | 2 | `Output` | `Int`, `UInt` |
| `Divisible` | `//` | 2 | `Output` | `Int`, `UInt` |
| `Exponentiable` | `**` | 2 | `Output` | `Int`, `UInt` |
| `Negatable` | unary `-` | 1 | `Output` | `Int` |
| `Equatable` | `==`, `!=` | 2 | none | `Int`, `UInt`, `String`, `Bool`, and a tuple or record whose fields are `Equatable` |
| `Orderable` | `<`, `<=`, `>`, `>=`, `max` | 2 | none | `Int`, `UInt`, `String`, `Bool` |

`max` places `Orderable(T, T)` on its element type `T`. A binary trait is satisfied by two operands
of one listed type, and a tuple or record satisfies `Equatable` only against the same product
([3.4 Comparisons](#34-comparisons)). A trait's `Output` is the type that satisfies it.

- **An associated type is written by name after the operands.** `requires Addable(A, B, Output=O)`
  states that `A` and `B` are `Addable` and that `O` is their `Output`. Omitting `Output=…` leaves
  it unnamed.
- **A requirement's arguments are any types.** `Equatable` reads a product componentwise, as `==`
  does ([3.4 Comparisons](#34-comparisons)), so `requires Equatable({T, U}, {T, U})` also states
  `Equatable(T, T)` and `Equatable(U, U)`.
- **A requirement no instance can satisfy is an error at the requirement.**
  `requires Orderable(List(T), List(T))` is rejected where it is written: no `List` is `Orderable`,
  so no call could satisfy it.
- **A requirement on base types alone states nothing about a parameter.** It must be satisfiable,
  and it has no other effect; naming a type parameter as its associated type is an error.
- **One clause holds every requirement.** `Transaction`
  ([8.7 Direction [Decided]: transactions as contextual parameters](#87-direction-decided-transactions-as-contextual-parameters))
  is written in the same clause: `requires Transaction, Orderable(T, T)` (**[Planned]**).
- **The body uses only what the clause states.** An operator whose operand type involves a type
  parameter is an error unless a requirement or the parameter's bound covers it. Where both do, the
  requirement decides: `a + b` under `T <: Int` and `requires Addable(T, T, Output=T)` is a `T`.
- **Each call satisfies each requirement at its own instantiation.** A call that does not is
  rejected at the call. A secondary label at the requirement is **[Decided]**.
- Declaring a trait or an instance is **[Open]**.

#### Polymorphic type annotations

```ebnf
poly_type       ::= "forall" "(" type_param ( "," type_param )* ")" expression [ requires_clause ]
```

In a type position, `forall (T, U <: B) V requires …` is the type of a polymorphic value: for
every `T` and `U` that meet the kinds and requirements, a value of type `V`. A polymorphic `def` has
this type, with its type parameters moved into the `forall`. `first` above has type
`forall (T) {T, T} => T`.

```python
pick: forall (T) {T, T} => T = first
```

- **It annotates a polymorphic binding.** A monomorphic binding with a polymorphic annotation is an
  error.
- **The annotation is exact.** The right-hand side is checked once, with each type parameter
  opaque, and every use instantiates the annotation rather than the right-hand side's inferred
  type.
- **A bounded annotation `g <: P = e` with a polymorphic `P` is [Open].** By the bounded form's
  meaning ([Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded)),
  `g` would keep `e`'s own type, with `e` checked against `P`. It is an error until polymorphic
  subtyping is decided.
- **It is written only as a whole annotation.** Inside another type, as in
  `{forall (T) T => T} => Int`, it would type a function that takes a polymorphic argument. That is
  **[Open]** and an error.
- **An alias may name it.** `Pick = forall (T) {T, T} => T` declares an alias of a polymorphic type,
  and `pick: Pick = first` uses it as a whole annotation
  ([6.7 Type-alias statements](#67-type-alias-statements)). Such an alias inside another type is
  the nested case above.
- **It is never a type constructor.** `forall (T) V` does not denote a function from types to
  types. A parameterised alias, if added, is written in the head form `Pair(T) = {T, T}`
  ([6.7 Type-alias statements](#67-type-alias-statements)).
- **A diagnostic prints an inferred polymorphic type in this notation.** A mismatch against a
  polymorphic annotation prints the right-hand side's type with each variable it quantifies as a
  parameter, `A`, `B`, … in order of first appearance, and each trait it requires of them as a
  requirement. `def inc(a): a + 1` prints as
  `forall (A) A => Int requires Addable(A, Int, Output=Int)`. A part of the type the notation cannot
  write, such as a parameter joined with another type, is marked in the printed type (`A ∨ Int`),
  not dropped.

#### A use that checks compiles

A polymorphic binding's type, inferred or written, states every requirement its body places on the
types it quantifies, and an instantiation that a checking use produces raises no error in the body
(**[Decided]**).

Every error a use causes is reported at the use. A secondary label at the requirement it fails,
the line of the body that imposes it or the annotation that states it, is **[Decided]**.

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

Every aggregate's result is to become `Option(T)`, `` `none `` for an
empty collection, as §3.9's optional lookup is **[Planned]**. A
statically proven deref for a collection known to be non-empty goes with
it, and is not designed yet. Until then `max` of an empty collection is
not defined ([Partiality is not yet defined](#partiality-is-not-yet-defined-open)).

The north-star programs additionally assume non-aggregate built-ins —
`str`, `open`, `stdout`, and a stream-restriction combinator
`restrict` — all **[Tentative]**: they exist only as usage sketches in
[`tests/programs/`](../tests/programs/), with no design writeup.

> **[Open]** — the restriction combinator's **name**, and how any of
> these combinators are *called*. The corpus spells the same operation
> two ways: `txn_kv` and `ledger_balance` write `c.restrict(\e -> …)`,
> the north-star `storefront` writes `orders.filter(\o -> …)`, and
> nothing decides between them — one of the two names has to go. Both
> are written in **method** position, as are `catalog.keys()` and
> `txn.current_time()`. A method call resolves among the methods of a
> nominal type ([6.8 Nominal types and methods
> [Decided]](#68-nominal-types-and-methods-decided)), and no collection
> type is nominal today. Whether the collection types become nominal
> types with these combinators as methods is open with them.

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

> **Direction [Decided].** Under the collections model, `groupby(c, key)`
> returns a `Map(K, Collection)` — its refined-domain result type *is* a
> map keyed by `K` (see
> [src/ccl/design/collections.md](../src/ccl/design/collections.md)). Its
> entries iterate as key–value pairs, so the rollup destructures the pair
> in the `for` binder and can rebuild a map with a map comprehension
> (§3.12):
>
> ```python
> [key -> sum([o.price for o in g]) for key -> g in groupby(paid, \o -> o.sku)]
> ```
>
> (the north-star `storefront` `/stats` rollup). A single binder takes the whole
> entry rather than the group (§4.6), so `for g in values(groupby(…))` is how to
> iterate the groups alone — which is what the unkeyed form above does today.

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
call denotes the entire stream the source will produce. `http_serve` is
both a source and a sink: it returns a source of requests and a sink for the
responses ([10. Sinks](#10-sinks)).

| Call | Source | Domain |
|---|---|---|
| `stdin()` | Process standard input | One element per line of UTF-8 text. |
| `http_serve(port, method, path)` | HTTP server, a source and a sink | Returns a `(requests, responses)` 2-tuple. The requests source yields request bodies; the responses sink is a deferred collection to feed. Must be assigned at top level via tuple destructuring (see below). |

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
- the `resps` side is a sink, a deferred output: feeds into it
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
> **`http` module** (**[Decided]**): programs write `import std::http`,
> which binds `http`, then `http::ok(…)` / `http::not_found(…)`, and
> address the source the same way, `http::serve(…)`. `std::http` is a
> module of the std root ([9.16 The std root](#916-the-std-root)).
> The north-star programs still spell these `http.ok` and `http.serve`.
> A response feed's
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

### 7.5 `box`

```
box(x)
```

Pairs `x` with **which type it is**, giving a value that carries its own type alongside
it. A consumer defined on every alternative unboxes implicitly, so `box(x)` is usable
wherever `x` is; what the pair buys is the join, which keeps both types as alternatives
instead of looking for one type that covers both
([Joining the types of several values](#joining-the-types-of-several-values)).

```python
counts = box([1, 2, 3]) if detailed else box([10])
sum(counts)                     # fine — works for either list
```

`counts` holds one of the two lists and which one it is, so no length is invented and
nothing is dropped. `sum` is defined on both alternatives, so it consumes `counts`
directly; an operation valid for only one is a compile-time error rather than a runtime
one. Where the alternatives are the same type there is one alternative, and
`box(xs) if c else box(xs)` is `xs`.

`box` takes an unboxed value, so `box(box(x))` is a compile-time error. Alternatives
combine by nesting the conditionals rather than the boxes: `box(a) if c else (box(b) if d
else box(e))` has three alternatives at one level, one per arm.

The alternatives are anonymous: the pair records the types themselves, not names chosen
by the program. Where the choice is meaningful to the reader, a variant (§6.5) names its
arms and `match` dispatches on them; `box` is for the case where the alternatives need
no names.

**Box each branch's result, not something inside it.**

```python
box([y for y in xs if y > 1]) if c else box(ys)              # ✅
[y for y in box(xs) if y > 1] if c else [z for z in box(ys)]  # ❌
```

Both spellings box something, and both branches of the second are boxed values — a
comprehension over a boxed collection is boxed in turn, over the same alternatives. What
separates them is where the **filter** sits. Boxed inside, the filter is part of the
alternative that branch records, and the two branches join. Boxed outside, the filter
applies to whichever alternative was taken and so is not part of any of them, and two
such values do not join. Dropping the filter makes the second spelling type-check, which
is what identifies it as the cause.

**An abstract collection type needs `box` too.** `List(T)` and `Collection(T)` say
nothing about which collection they are, so a value reaches one only by being boxed:
`x: List(Int) = box([1, 2, 3])` binds, and `x: List(Int) = [1, 2, 3]` is an error. That
is the same requirement as above rather than an alternative to it — the annotation keeps
the elements and forgets which collection it was, and with it any proven lookup (§3.9).

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
- **Branch guards and tag dispatch.** A block may carry `if`/`elif`/`else`
  guards, more than one of them, and `match` dispatch. Each branch's
  writes are scoped to its own path and the transaction commits on the
  disjunction of the writing paths, so a write on the spine beside a
  guard commits unconditionally. A bare `if p:` with no `else` is the
  deny idiom: where `p` fails over the snapshot the transaction
  contributes no write and no reply.
- **An induction accumulator may not be written under a branch inside a
  block** (rejected with a diagnostic). Write it after the block, or, if
  it should be shared across the transaction, declare it `Mut(…, Txn)`
  and write it on the spine.
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
- **A `Txn` mutable variable is read only inside a `with begin():` block.** A
  bare read outside one is an error, and stays one: the block is what pins a
  **snapshot-consistent** view, so that several mutable variable reads in one
  block see one commit snapshot. A read that wants no snapshot has the two terms
  below instead — an as-of read fed out of a block, or `await_final`.
- **As-of read.** A mutable variable read fed *out* of a block that does not
  itself write that mutable variable is an **as-of read at an arbitrary commit
  position** — the mutable variable's value as of wherever the reading transaction
  lands in the commit order, replied indexed by the *reading* loop. This
  is uniform whether the reader is a live request stream, a finite loop,
  or the synthesized singleton of a standalone read.
- **Terminal read — `await_final(x)`.** `await_final(x)` waits for `x`'s whole
  commit history to complete and yields its final value (§8.6). It is the only
  terminal read of a mutable variable: every other read is an arbitrary as-of
  sample, so a program that means the final value has to say so.

### 8.4 Feeds are the second form of mutability

A feed (`<<`, §3.7) is the **same history object** as a mutable variable,
under the **append-only** merge law: contributions union (`++`), there is
no carry-forward, and a read yields the whole collection — which is
exactly why a feed is an unordered bag (§3.7) while a mutable variable
derefs to a single latest value. `o << e` is surface-impure in the same
way `x := e` is; the two differ only in that merge law.

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

### 8.6 `await_final`

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
- **One `requires` clause.** `Transaction` and trait requirements share it:
  `requires Transaction, Orderable(T, T)`
  ([Trait requirements](#trait-requirements)).

### 8.8 `@LoadFrom`

`@LoadFrom(x)` decorates a declaration, binding it to the value the version this
source replaces held for the mutable variable `x`, read once when the
replacement takes over:

```python
# v1
qty: Mut(Int, Txn) := 0

# v2
@LoadFrom(qty)
qty_units: Int
```

This is the one declaration that carries an annotation and no value — the
decorator is where the value comes from. A bare `y: T` elsewhere is a parse error
([4. Statement semantics](#4-statement-semantics)). [1.9 Decorators](#19-decorators) lists every
decorator.

A load is a declaration, so it appears where declarations do: the top level, or a
`def` body. A `for` body and a `with begin():` block take statements rather than
declarations and reject one. Inside a `def`, the name resolves to the variable
that function's own instantiation declares before it resolves to a top-level one,
the way a name resolves anywhere else.

A load inside a `def` is refused where the version being replaced called that
`def` more than once. Each call site declares its own variable of the loaded
name, and the source tells the call sites apart only by the order they appear in;
a reorder would move each site's value onto its neighbour with nothing in either
version saying so. Binding each call site to a name — `a = f(…)` rather than a
bare `f(…)` — tells them apart, and the load then resolves.

`x` is a name, not an expression, and it is a variable the *previous* version
declared: the version being compiled need not declare it, and retiring `qty`
while seeding `qty_units` from it is the case the decorator exists for.

**What it binds is an ordinary binding.** Nothing requires the declaration to be
mutable. A version that only reads what its predecessor held declares nothing
mutable at all; one that carries state forward names the binding in the
initialiser of the variable that replaces it:

```python
@LoadFrom(qty)
held: Int
qty_units: Mut(Int, Txn) := held * 10000
```

**It is a snapshot, not a read.** The value is what the predecessor held at the
swap, and is a constant from then on — not a dependency on `x` going forward. It
is therefore not a read of a transactional variable and needs no `with begin():`
block ([8.3 Reads](#83-reads)).

**A variable may be declared, loaded, or both.** A variable the new version
declares carries its value forward whether or not a `@LoadFrom` names it, which
is the ordinary reload. The decorator is for the variable the new version
declares under a different name, or retires. A version doing both — declaring `x`
and loading from `x` — leaves `x` running on its own value and starts the new
variable at a copy of it taken at the swap. The two are separate variables from
then on, and neither reads the other.

**The annotation states the shape.** The value the running program holds has to fit
it, and the two forms ([Two annotation forms: exact and
bounded](#two-annotation-forms-exact-and-bounded)) read here as they do at any other
binder: `held: T` binds at `T`, and `held <: T` binds at the loaded value's own type
with `T` as an upper bound.

```python
@LoadFrom(qty)
held <: Map(String, Int)
qty_units: Mut(Map(String, Int), Txn) := [q * 10000 for q in held]
```

A comprehension over a map binds each value and keeps the keys, so that scales
every quantity the predecessor held.

**A running program is required today.** A source containing `@LoadFrom(x)` is an
upgrade of a specific predecessor: compiled from nothing, it is an error naming
`x`, and so is one naming a variable the running program does not hold. There is
no `@LoadFrom(x, default)` — a default would turn that error back into a silent
wrong answer.

A live process is the only predecessor a version can be handed state from today.
Durable state is **[Tentative]** ([design.md](design.md)), and a process
restarting from a store on disk is the same migration against a predecessor that
is not running; which predecessors a load may name is settled with durable state
rather than here.

**It is transitional.** The seeding happens once, so the decorator comes out in
the next version. A name a version loads and does not declare is gone after that
version, which is why recompiling a migrating source unchanged is refused: there
is no longer anything of that name to load.

### 8.9 `@Discard` [Decided]

`@Discard` decorates a declaration head with no value, where the declaration stood. It marks that
what the version this source replaces held there is intentionally gone:

```python
@Discard
stock                         # the predecessor's `stock` is intentionally gone
```

A reload that drops a variable holding state is refused without one. The name resolves at its own
position, outward, as `@LoadFrom`'s does. On a `run` statement the tombstone covers every variable
of that run
([9.18 Reloading a program of modules](#918-reloading-a-program-of-modules)), and stands at a
module's top level, as the statement it marks gone does.

**A tombstone resolves against the ancestry**, not only the version it replaces: every version the
running program descends from, through each reload and each branch it was created from. A tombstone
is valid when some version in the ancestry held the address, whether or not the immediate
predecessor does, so it may stay in the source across any number of reloads. A tombstone naming an
address no version in the ancestry held is an error, and so is one compiled with no ancestry at all.
The running program keeps the record of every address its ancestry held, for as long as it runs.

A tombstone may also be removed from the source at any later reload. Once a reload carrying it
succeeds, the running program holds nothing at the address, so a version without the tombstone
deletes no state.

`@Discard` replaces retiring a variable by loading it into an unused binding.

---

## 9. Modules [Decided]

A **module** is one `.cambra` file. The statements of this section, qualified names, and qualified
labels and tags parse. `import` and `run` with their `use` clauses, value `param`s, `pub`,
qualified values, labels, and tags, and qualified type aliases lower, and lowering refuses the rest.
A module is used in one of two ways:

- **Importing** it brings its public members into scope. Importing asserts that the module performs
  no IO and declares no mutable state. Its members exist once in the program, however many modules
  import it ([9.7 Importing asserts no IO and no
  state](#97-importing-asserts-no-io-and-no-state)).
- **Running** it performs its top-level computation, public and private: its state, its sources and
  sinks, and its loops. A module may be run any number of times, each run with its own name, its own
  arguments, and its own state.

The engine runs one **root module**, the top-level definitions of everything that should run. The
root runs other modules, which may run others in turn. A reload replaces the source code of the root
and of every module, so adding, removing, and changing what runs are all edits to source.

Within a module the top level is sequential, as in a single file (§4): a value member names only
members above it. A module's public members are reached from another module as `m::f`, and one
module is handed to another as a value of a **Module type**, the structural type of its public
members ([9.8 Module types](#98-module-types)).

### 9.1 Vocabulary

- **Module path.** The `::`-separated identifier sequence that names a module, `shop::cart`. A
  module's identity across compilations is its path.
- **Root module.** The module the engine runs. Its run path is empty.
- **Run.** One running of a module, declared by a `run` statement. A run has a **run name** in the
  module that declares it and a **run path** from the root: `eu`, or `eu::inv` for a run `eu`
  declares.
- **Shared run.** The one evaluation of an imported module's top level at one set of arguments,
  whose members every import passing those arguments reaches. Its run path is the module path with
  those arguments
  ([9.7 Importing asserts no IO and no state](#97-importing-asserts-no-io-and-no-state)).
- **Member.** A binding at a module's top level. Bindings inside a `def`, a loop, or a block are
  **locals**.
- **Public member.** A member declared with `pub`. Every other member is private to its module.
- **Parameter.** A value a run supplies, declared by a `param` statement.
- **Module type.** The structural type of a module's public members, `Module{…}`
  ([9.8 Module types](#98-module-types)).
- **Module interface.** What checking records about a module for the modules that use it: its
  public members' contracts, its parameters, and whether it performs IO
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)).

### 9.2 Imports

```ebnf
import_stmt ::= "import" module_path ["(" [arg ("," arg)* [","]] ")"] ["as" ident] [use_clause]
use_clause  ::= "use" use_list
use_list    ::= use_item ("," use_item)* | "(" use_item ("," use_item)* [","] ")"
use_item    ::= ident ["as" ident]
module_path ::= ident ("::" ident)*
```

- `import a::b` binds the last segment, `b`. `import a::b as c` binds `c`. This departs from
  Python, where `import a.b` binds `a`. The module name an import binds appears in the statement.
- `import a::b use f, T as U` binds `b`, and also binds `f` and `U` to the public members `f` and
  `T` of `a::b`. A `use` item binds an unqualified name; the module name stays bound beside it.
- An import name begins with a lowercase letter, as a module path segment does
  ([9.15 Module files](#915-module-files)). A `use` alias keeps the case of the member it names,
  `T as U` or `f as g`. Both rules follow from a capitalized name being a type
  ([6.1 Direction: term/type syntax split [Decided]](#61-direction-termtype-syntax-split-decided)).
- An import reaches every public member of the module's shared run. Importing a module that
  performs IO or declares mutable state is an error ([9.7 Importing asserts no IO and no
  state](#97-importing-asserts-no-io-and-no-state)).
- An import passes arguments to the module's parameters as a run does
  ([9.4 Parameters](#94-parameters)): keyword-only, one for each parameter without a default. Every
  argument is a constant, so two imports of one module with equal arguments reach one shared run,
  and its type members are one type in both: `import sorted_map(K=String)` in two modules gives
  both one `sorted_map::Map`. An omitted argument is the parameter's default, so `import m` and
  `import m(x=1)` reach one shared run when `x` defaults to `1`. An argument may be any constant
  ([9.19 Open questions](#919-open-questions)): a literal, a type, or an import name or run name
  passed as a value of its Module type ([9.8 Module types](#98-module-types)).
- An `import` stands at a module's top level. One inside a `def`, a loop, or a block is an error.
- There is no wildcard `use`. Adding a public member to a module never changes what an importer's
  names mean.
- Every module path is absolute, from the module root or, for a path beginning with `std`, from the
  std root ([9.15 Module files](#915-module-files), [9.16 The std root](#916-the-std-root)). There
  are no relative imports, so moving a file does not change what the file itself imports.
- There is no re-export. `pub` is refused on an `import` and on a `run`, so a module's public
  members are the ones it declares.

### 9.3 Runs

```ebnf
run_stmt ::= "run" module_path ["(" [arg ("," arg)* [","]] ")"] ["as" ident] [use_clause]
arg      ::= ident "=" expr
```

```python
run audit                                             # named `audit`
run storefront(port="8080", region="eu", audit=audit) as eu
run inventory as inv use stock                        # binds `inv`, and `stock` to `inv::stock`
```

- A run's name defaults to the module path's last segment, as an import's does. `as` overrides it.
  A run name begins with a lowercase letter, as an import name does.
- A `run` stands at a module's top level, as an `import` does.
- Every run has a name, because the name is the run's identity: its state, its routes, and what a
  reload pairs it with. Two runs in one module with the same name are an error, fixed by `as`.
  Renaming a module file renames every run that relies on the default, so a long-lived run names
  itself with `as`.
- Every `run` statement is its own run, and nothing deduplicates them. Two modules that each write
  `run audit` give the root two audit runs, each with its own state. Sharing one run takes passing
  it as an argument ([9.9 Running](#99-running)).
- A `use` clause on a run binds unqualified names to the run's public members, as an import's
  does.
- Arguments are keyword-only, one per parameter without a default. A module with no parameters is
  run without parentheses.
- A run stands at its statement in the declaring module, and performs its module's top level there.
  An argument is any expression over the names above the statement: the declaring module's
  members, earlier runs' members, imports, and parameters. A run's public members are what it
  returns, so `run index(docs=p::documents) as ix` passes one run's member to another. An import
  name or run name in an argument denotes its run as a value of its Module type, which is how a
  module is passed to another.
- A run name is bound from its statement to the end of the declaring module, as a value binding
  is, because a run is an evaluation. `eu::x` reaches the run's public member `x`. An argument names
  only runs above its own, so runs cannot depend on each other in a cycle: `run svc(peer=y) as x`
  above `run svc(peer=x) as y` names `y` before it is bound.
- A run needs no `import`. A run name and an import name in one module may not coincide. Importing a
  module and running it are two runs: the import reaches the shared run, and the `run` statement
  declares another.
- A module returns a run it declares the way it returns any value: by binding it to a public member.
  `pub audit = a`, below `run audit_api as a`, is a member of the run's Module type
  ([9.8 Module types](#98-module-types)), and a module running `shop` reaches the run's members
  through it, `shop::audit::events`, as through a parameter of Module type. `pub` on a `run` is
  refused.

### 9.4 Parameters

```ebnf
param_stmt ::= "param" ident [":" type] ["=" expr]
             | "param" Ident ["<:" type] ["=" type]      (* Ident: a capitalized identifier *)
```

```python
import audit_api

param port: String
param region: String = "us"
param audit: audit_api::AuditLog   # Module{events: Feed(audit_api::Event)}
param Receipt <: {id: String}
param payments: Module{charge: {amount: Int} => Receipt}
```

- A **type parameter** is a capitalized parameter, since `Caps` means type
  ([6.1 Direction: term/type syntax split [Decided]](#61-direction-termtype-syntax-split-decided)).
  It names a type that varies with the run. The module is checked with it as an opaque type, known
  only through its bound: `Receipt` above has an `id` and nothing else checking can rely on. A run
  or an import supplies it as an argument, `Receipt=stripe::Receipt`, as it does any parameter
  without a default. **[Planned]** An argument left out is inferred from the types of the other
  arguments.
- A value parameter is an immutable value. Its type is its annotation, or inferred from the module's
  uses the way a function parameter's is.
- A parameter of Module type is how a module takes another module. The argument is an import name
  or a run name, and Module subtyping is the check ([9.8 Module types](#98-module-types)). The
  parameter is a qualifier: `audit::events` reaches the argument's member.
- A parameter's type is the only thing checking reads about its argument
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)). An interface is an
  alias of a Module type, usually exported by a library both sides import.
- A parameter is in scope throughout its module. A member with the same spelling is an error naming
  both sites. A default is evaluated before the module's members, so it is an expression over the
  module's import names and the parameters declared above it. A local may shadow a value
  parameter, except one of Module type ([9.6 Qualified references](#96-qualified-references)). A
  type parameter follows the scoping of a type alias
  ([6.7 Type-alias statements](#67-type-alias-statements)).
- A `param` stands at a module's top level, as an `import` does.
- The root module has no required parameters. The engine runs it, and no `run` statement supplies
  arguments, so a root parameter takes its default. A root with a parameter that has no default is
  an error that says to run the module from a root instead. Running one module alone takes a root of
  one `run` statement, so what runs, and with which arguments, is always source that a reload
  replaces.

### 9.5 Visibility

`pub` prefixes the statement that introduces a member:

```python
pub def quote(item, qty): …
pub limit: Int = 10
pub Qty = {Int where _ >= 0}
pub type Price = {amount: Int}
pub def discounted(self: Price, pct: Int) => Price: …
pub stock: Mut(Map(String, Int), Txn) := []
```

A declaration loaded with `@LoadFrom` is an ordinary declaration without an initializer
([8.8 `@LoadFrom`](#88-loadfrom)), so its `pub` stands at the head of the declaration's line, below
the decorator:

```python
@LoadFrom(qty)
pub held: Int
```

- A member without `pub` is private. Only its own module can name it.
- `pub` on `:=` is accepted on the statement that introduces a `Txn` mutable variable and refused on
  a later write to it. It is refused on an induction variable
  ([9.10 Induction variables stay in their module](#910-induction-variables-stay-in-their-module)).
- `pub` is refused on `import`, `run`, `param`, `op=`, `<<=`, `for`, `if`, `match`, `with`,
  expression statements, and anywhere but a module's top level.
- A public name is bound exactly once at its module's top level. A later binding of the same
  spelling, public or private, is an error naming both sites. Without this rule the exported binding
  would be whichever one was in scope at the end of the module, and a shadowing edit far from the
  `pub` would change the module's interface.
- Private names keep the ordinary top-level shadowing of
  [5. Scoping and binding](#5-scoping-and-binding).
- `pub` on a `type` declaration exports the nominal type. `pub` on a method's `def` exports the
  method, and a method without `pub` is reached only from its own module, in either spelling
  ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). A method binds
  no module-level name, so the bound-once rule above does not apply to it.
- Types need not be annotated on public members. An unannotated member's contract is its inferred
  type ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)).

### 9.6 Qualified references

Three kinds of name reach another module's members: an import name, a run name, and a parameter of
Module type. `::` separates the name from the member, and `.` stays record projection
([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)). With
`import shop::cart`, `run shop::cart as c`, and `param p: Module{count: Mut(Int, Txn)}`:

| Written | Position | Means |
| --- | --- | --- |
| `cart::total` | value | the public member `total` of `shop::cart`'s shared run |
| `cart::Item` | type | the public type member `Item` of `shop::cart`, an alias or a nominal type |
| `c::count` | value, write target | the public member `count` of the run `c` |
| `c::total` | value | the public member `total` of the run `c`, a copy distinct from `cart::total` |
| `p::count` | value, write target | the member `count` of the run passed as `p` |
| `cart` | value | `shop::cart`'s shared run, as a value of its Module type ([9.8 Module types](#98-module-types)) |
| `c` | value | the run `c`, as a value of its Module type |
| `cart::hidden` | any | error: `hidden` is private to `shop::cart`, with a secondary label at its declaration |
| `cart::missing` | any | error: `shop::cart` has no member `missing` |

- Import names, run names, and Module-typed parameters cannot be shadowed. A binder anywhere in the
  module spelled like one of them is an error. `m::f` names a module, so a value binder spelled `m`
  would give one spelling two meanings in one scope.
- An import name is in scope throughout its module, including above the statement: an import is a
  static fact rather than an evaluation, so no order constrains it. A run name is in scope from its
  statement down ([9.3 Runs](#93-runs)).
- A qualified member is a named callee. `cart::total(x)` is a call to the member it resolves to,
  including the special forms and `Mut`-parameter call shapes that dispatch on the callee. Through
  a parameter, `p::f(x)` takes its call shape from `f`'s type in the parameter's Module type.
- A qualified generic member keeps its polymorphism: `n::id(1)` and `n::id("a")` both check.
- A name an import's `use` clause binds is in scope throughout its module, including above the
  statement, as the import name is. One a run's `use` clause binds is in scope from the `run`
  statement down, as the run name is. A local may shadow either. A member of the module with the
  same spelling is an error naming both sites.

### 9.7 Importing asserts no IO and no state

Importing a module asserts that the module performs no IO and declares no mutable state. A module
performs IO when it opens a source or binds a sink, or when it runs a module that performs IO. It
declares mutable state when its top level introduces a mutable variable, writes one, or loads one
with `@LoadFrom`. Importing either kind of module is an error at the `import`, with a secondary
label at the IO site or the state. Such a module is run instead. The check is per module: a module
that serves a route or holds state is run, whatever else it exports.

State therefore belongs to runs. Every piece of state has a run that a `run` statement names, so the
source says which modules reach it: the module that runs it, and the modules that run handed to.

An imported module's top level is evaluated once for each distinct set of arguments, however many
modules import it with those arguments, because its members are values it computes. That evaluation
is the module's **shared run** at those arguments. Every import passing them reaches the same
members. Its run path is the module path with its arguments, so it never collides with a run a
`run` statement names.

```python
# inventory.cambra: declares state, so it is run and not imported
stock: Mut(Map(String, Int), Txn) := []
pub def reserve(sku, qty) requires Transaction:
    …
pub InStock = {String where _ in stock.keys()}   # intended; not supported today
```

`InStock` is intended and not supported today, in one file as across modules: the compiler cannot
name a mutable map's key set in a type. `run inventory as inv` and `run inventory as eu_inv` are two
runs, each with its own `stock`, and `inv::InStock` is a different type from `eu_inv::InStock`.

### 9.8 Module types

A **Module type** is the structural type of a module's public members. It is written like a record
type, with `Module` before the braces:

```python
pub AuditLog = Module{events: Feed(Event)}
param payments: Module{Receipt <: {id: String}, charge: {amount: Int} => Receipt}
```

| Public member | Entry |
| --- | --- |
| value, `def` | `name: T`, at its contract, which may be polymorphic |
| feed | `name: Feed(T)` |
| `Txn` mutable variable | `name: Mut(V, Txn)` |
| type alias | `Name = T` for an exact type, or `Name <: T` for one known through a bound |
| nominal type | `Name = T`, where `T` is the nominal type |
| private member | none |

A capitalized entry is a type member. Its `<:` is the bounded form of a type parameter
([9.4 Parameters](#94-parameters)), and it is the one place `<:` appears inside a type literal
([Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded)).

`Module{…}` 𝐴 is a subtype of `Module{…}` 𝐵 when 𝐴 has every member 𝐵 names. A value member's type
in 𝐴 is a subtype of its type in 𝐵, a `Mut` member's type is equal, since `Mut` is invariant, and a
type member satisfies 𝐵's bound. Width subtyping lets a consumer name only the members it uses:

```python
# storefront.cambra
param audit: audit_api::AuditLog     # Module{events: Feed(audit_api::Event)}

# deploy.cambra
run audit
run storefront(audit=audit) as eu    # the run `audit` has `events` and may have more
```

An import name or run name denotes its run as a Module value in one position only: a run argument.
A Module value stored in data or returned from a function is **[Open]**
([9.19 Open questions](#919-open-questions)). A Module-typed parameter therefore names exactly one
run in each run of its module. A `Txn` member reached through it is a bare variable reference, as
through a run name.

### 9.9 Running

Each run performs its module's top level, with its parameters bound to its arguments:

- Its mutable variables and feeds are its own. `eu::stock` and `us::stock` are two variables.
- Its sources open and its routes serve while it runs. The `(port, method, path)` triple of every
  route is unique across all runs. A conflict is an error at both `run` statements.
- Its own runs run with it, and their run paths extend its own.

State is shared between runs in two ways. Every module that imports a module reaches its one shared
run, and a module passes one run to others as an argument:

```python
run audit
run storefront(port="8080", audit=audit) as eu
run storefront(port="8081", audit=audit) as us   # eu and us feed one `audit::events`
```

A program of modules means what the same code means written in one file, with each member spelled
by its qualified name. For mutable state, modules add visibility and nothing else:

- A public mutable variable is a `Txn` variable. It is read and written through a qualified
  reference inside a `with begin():` block ([8.3 Reads](#83-reads)).
- A qualified reference is a bare variable reference, so `eu::stock` may be passed to a `Mut`
  parameter under the downward-only discipline of
  [8.1 Mutation is explicit: the `:=` operator](#81-mutation-is-explicit-the--operator).
- A public feed is fed and read through a qualified reference. Append merges commutatively, so
  several writers are a feed's semantics.
- A module that keeps its state private and exports functions over it relies on functions that
  capture mutable variables ([4.1 `def` — function definition](#41-def--function-definition)) and
  that run inside their caller's transaction
  ([8.7 Direction [Decided]: transactions as contextual parameters](#87-direction-decided-transactions-as-contextual-parameters)).
  Exporting only functions that read is how a module publishes state other modules cannot write.

### 9.10 Induction variables stay in their module

An induction variable is read and written only in the module that declares it. `pub` on one is
refused.

An induction variable's history is ordered by its writes in program text, and a read sees the value
at its own position in that text:

```python
cnt := 0
for x in [1, 2]:
    cnt += x
mid = cnt          # 3
for y in [10, 20]:
    cnt += y
cnt                # 33
```

Within one module the source is that order. Between modules no source order exists
([9.11 The module graph](#911-the-module-graph)), so a read or a write of another module's
induction variable would have no defined position in its history. A `Txn` variable has no such
problem: its order is the commit order the transaction engine decides at run time, not program text.

- A module passes its own induction variable to another module's function, `lib::bump(cnt)`. The
  call sits in the caller's program order, so the writes it makes have their place.
- A module publishes an induction variable's progression by feeding it out, `pub counts: Feed(Int)`
  with `counts << cnt` in the loop. A feed's order is its own, and several readers are its
  semantics.
- A module publishes an induction variable's value at one position by binding it to an immutable
  public member there. The member is an ordinary value, read like any other:

  ```python
  cnt := 0
  for x in xs:
      cnt += x
  pub total = cnt    # the value after the loop
  ```

### 9.11 The module graph

The **module graph** has an edge from each module to every module it imports or runs. The graph must
be acyclic. A cycle is an error listing the statements that form it, each labeled in its own file. A
module that runs itself, directly or through others, is such a cycle. Mutually recursive modules
wait on `rec` ([4.3 Assignment forms](#43-assignment-forms)).

Modules have no order among themselves. Members of different modules never share a scope, and
neither the order of statements nor the order in which files are found affects what a program means.

### 9.12 Field labels and tags belong to a module

A record field label and a variant tag belong to a module. An unqualified label or tag always means
the current module's: `f1` written in `mod1` is `mod1`'s `f1`, which `this::f1` also spells.
`mod2::f1` is `mod2`'s label, a different field:

```python
# in mod1
r: {f1: Int, mod2::f1: String, this::f2: Bool} = …
r.f1           # Int; the same field as r.this::f1
r.mod2::f1     # String
```

A tag's qualifier precedes its backtick, so the backtick still opens the tag: `` mod2::`some(1) ``
constructs `mod2`'s `` `some ``, `` {mod2::`some{Int} | `none} `` is a variant type over it, and
`` case mod2::`some(v): `` matches it.

The qualifier is `this`, an import name, or a run name. Record and variant types stay structural
([3.15 Variant constructors](#315-variant-constructors)), and two modules agree on a type by naming
the same labels. `{audit_api::app: String}` written in `storefront` is the type `audit_api` writes
as `{app: String}`. Within one file this changes nothing.

- **[Open]** — a syntax that aliases another module's label or tag, so the importer writes it
  unqualified.
- **[Tentative]** — **nominal variants**, whose tags live inside the nominal type and follow its
  scoping rather than the module's. Their syntax is **[Open]**. The built-in `Option(T)` waits on
  them: its `` `some `` and `` `none `` belong to the std root, so a user module that writes
  `` `some(1) `` builds its own tag, which no `Option` admits.
- **[Open]** — which module owns the labels of data from outside the program, such as the fields
  of an HTTP request body.

A module's type members are its type aliases and its nominal types
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). Exporting an
alias exports a spelling for a structural type, and the user's type is the same type. Exporting a
nominal type exports the type itself: `mod::Price` is one type in every module that names it, and
distinct from every other type of its shape.

### 9.13 Private-in-public

A public member's type may mention private members. A public alias's refinement may name a private
value, and a public function's inferred type may carry a refinement over one:

```python
catalog = ["tee" -> 25, "mug" -> 12]          # private
pub SKU = {String where _ in catalog.keys()}  # public, over a private value
```

An importer writes `inventory::SKU` and cannot write `inventory::catalog`. The alias's predicate was
resolved in `inventory`, so it still refers to `inventory`'s `catalog`. Diagnostics render it as
`inventory::catalog`. Visibility restricts which names a module's source may write. It does not
restrict what a type may mention.

### 9.14 Checking a module on its own

A module is checked once, alone, with no root and nothing that uses it. `cambra check lib.cambra`
runs that check and prints the module's interface.

- **Parameters are typed binders.** A value parameter has its annotated type or the type its uses
  infer. A type parameter is opaque apart from its bound.
- **Imports are read through interfaces.** A module sees another module's public contracts and
  whether it performs IO, never its bodies.
- **A public member's contract is its type.** An annotated member's contract is the annotation,
  checked against the body. An unannotated member's contract is its inferred type, refinements and
  all.
- **A run is checked at the `run` statement.** Each argument is checked against its parameter's
  type. An argument's Module type is built from its members' contracts, so passing a module compares
  contracts with the parameter's type, and no body is involved.

The check covers parsing, name resolution, and typing, plus the module's own `run` statements:
their argument types ([9.3 Runs](#93-runs)). Its guarantee: **a module
that checks cannot be made to fail by a use that checks, in any of these.** Every error a use causes
there is reported at the use, against a contract, with a secondary label at the library line the
requirement comes from.

Some checks run only once the program is assembled from its root, because they need the bodies of
called functions or the full set of runs: the mutable-variable and transaction rules of
[8. Mutability, transactions, and feeds](#8-mutability-transactions-and-feeds), feed routing, the
dataflow shapes the compiler can emit, and route uniqueness across runs. One of these can refuse
code inside a module that checked. The error is reported at the code it names, with the run whose
copy failed, and with a secondary label at the `run` statement that created that run, or at each
`import` that reaches a shared run.

**[Planned]** — the guarantee needs every inferred type to state each requirement its body imposes.
A trait requirement on a generic parameter is the exception today: it is enforced only when a
concrete type reaches the parameter.

An inferred contract changes when its body changes. Every user in the engine is rechecked on reload,
so a breaking change surfaces there. A library author sees it in the interface `cambra check`
prints. An annotation is how an author fixes the contract.

### 9.15 Module files

- The **module root** is the directory containing the root file.
- The root file's name is `<name>.cambra`, and the root's module path is `<name>`, a segment under
  the rule below. A module whose statement names that path reaches the root, which is a cycle
  ([9.11 The module graph](#911-the-module-graph)).
- Module path `a::b::c` names the file `<root>/a/b/c.cambra`, unless it begins with `std`
  ([9.16 The std root](#916-the-std-root)). A directory is not a module.
  `a.cambra` and `a/b.cambra` are two independent modules, and importing `a` does not make `a::b`
  available.
- A submodule is not a member of its parent, and no statement makes it one, since there is no
  re-export. A module that uses `a::b` imports it by its own path. Importing a module loads no file
  that no statement names.
- Each segment is a lowercase-initial identifier. `Caps` means type
  ([6.1 Direction: term/type syntax split [Decided]](#61-direction-termtype-syntax-split-decided)),
  so `m::X` is a type member and `X` is never a module. A segment beginning with `__` is refused,
  since user code cannot bind that namespace.
- A missing file is an error at the statement naming it.
- The match is case-sensitive, including on a case-insensitive file system. `import cart` does not
  load `Cart.cambra`.
- Two module paths resolving to one file, through a symlink for example, are refused. The file would
  have two identities, and two shared runs.

### 9.16 The std root

The compiler's own modules live under a **std root**, and every std module's path begins with `std`:
`import std::http` binds `http`, then `http::serve(…)` and `http::ok(…)` ([7.4 Sources](#74-sources)).
A path beginning with `std` names a module of the std root and never a file under the module root,
so `std` is the only name the std root reserves, and adding a std module changes no user module's
meaning. `std` alone names no module, and a root file named `std.cambra` is refused.

A builtin source, sink, or special form a std module provides is recognized by what a name resolves
to, not by how it is spelled. After `import std::http as web`, `reqs, resps = web::serve(…)` is the same
form as `http::serve(…)`, and the bare name `http_serve` is gone. Its address arguments are string
literals. **[Planned]** — an address passed as a parameter, fixed per run, needs a link-time
constant, a value fixed once a run's arguments are bound, which the language does not define yet.
Until it does, two runs of a module that serves a route serve the same address and conflict.

The prelude (`sum`, `max`, `groupby`, `stdin`, `defer`, `box`, `begin`, …) stays unqualified and in
scope in every module.

### 9.17 No trailing expressions

A trailing value expression is an error in every module, since what a module does is its sinks. A
script-shaped root therefore needs an output sink, which [10. Sinks](#10-sinks) does not yet define.

### 9.18 Reloading a program of modules

A reload replaces the source of every module, the root's included, and the running program carries
its state across ([8.8 `@LoadFrom`](#88-loadfrom)):

- **State belongs to runs.** Each run's state is its own, and a shared run holds none
  ([9.7 Importing asserts no IO and no state](#97-importing-asserts-no-io-and-no-state)). A reload
  pairs the runs of the two versions by run path. A run the new version adds starts from its
  declared initial values. A run present in both takes over its state, whether its module's source,
  its arguments, or both changed.
- **Removing a run is deleting stateful code.** A reload that drops a run holding state is refused
  unless the new version marks the removal with `@Discard`
  ([8.9 `@Discard` [Decided]](#89-discard-decided)), as it must for any deleted variable:

  ```python
  @Discard
  run storefront as us          # everything `us` held is intentionally gone
  ```

- **Renaming a run is marked with `@RenamedFrom`.** `@RenamedFrom(eu)` on a `run` statement moves
  the whole run's state to the new name. `@LoadFrom` decorates only a declaration
  ([8.8 `@LoadFrom`](#88-loadfrom)), so a run takes its own decorator:

  ```python
  @RenamedFrom(eu)
  run storefront(port="8080", region="eu") as eu_west
  ```

- **`@LoadFrom` names a qualified variable.** `@LoadFrom(eu::stock)` loads a variable of another run
  of the predecessor. An unqualified `@LoadFrom(x)` resolves within its own run first, then outward
  as [8.8 `@LoadFrom`](#88-loadfrom) describes.
- **Moving a stateful member to another module moves it to another run.** It needs `@LoadFrom`
  naming its old run path, or the reload is refused as for any variable the new version does not
  declare.
- **Renaming a module file** renames every run that relies on the default run name, which moves its
  state. A run named with `as` is unaffected.

### 9.19 Open questions

- **Read-only export.** A public `Txn` variable is writable by every module that reaches it. A
  modifier such as `pub(read)` would let a module publish it for reading while its writes, and so
  its invariants, stay local. Until then a module exports functions that read.
- **An induction variable's final value.** `pub` on an induction variable could export the value
  after all its writes, which has a position independent of program order. Refused for now. A module
  binds the value at a position to an immutable public member instead
  ([9.10 Induction variables stay in their module](#910-induction-variables-stay-in-their-module)).
- **Packages.** Dependencies outside the module root, a search path of roots, versioning, and a
  manifest. The rules of [9.15 Module files](#915-module-files) extend to several roots with a
  collision between roots refused.
- **Givens and instances across modules.** Transactions as contextual parameters are locally scoped.
  General typeclass instances will need a rule for which module's instances are visible where, and a
  coherence rule.
- **Discarding and redeclaring one address.** A version that both writes `@Discard stock` and
  declares `stock` could mean a reset to the declared initial value, or be an error.
- **Constants.** An import's arguments are constants, fixed when the program is linked, and so is
  a route address passed as a parameter. Every expression whose value is fixed at link time is a
  constant, along the lines of C++'s `constexpr`: a literal, a type, an import name or run name,
  arithmetic over constants, a record or a list of them, and a member or an alias bound to one.
  The rule that recognizes them is open.
- **First-class Module values.** A Module value is written only as an argument or as a member
  bound to a run name or an import name. Storing one in data, returning one from a function, or
  choosing between two at run time would make a qualified reference's target depend on a value,
  which static resolution does not cover.

---

## 10. Sinks

Sinks can be declared anywhere in the program, but all external side
effects are lifted to the boundary of the program.  The program returns
a Record of collections that need to be bound to each sink.  That Record is
the whole of what the program produces: the value of its trailing expression
is discarded.

Sinks may observe the indices of collections passed to them if needed.

## 11. Errors and recovery

### 11.1 Lex errors

The lexer reports six error kinds and stops emitting tokens at the
first one:

- **`InvalidToken`** — no token rule matched at the position.
- **`UnterminatedString`** — a string literal's line ended before its closing
  quote ([1.7 Literals](#17-literals)). The span is the opening quote.
- **`DetachedBacktick`** — a backtick not immediately followed by an
  identifier ([1.8 Operators and punctuation](#18-operators-and-punctuation)).
  The span is the backtick.
- **`UnmatchedClose`** — `)`, `]`, or `}` with no matching open.
- **`UnclosedBracket`** — EOF reached with at least one open `(`/`[`/`{`.
- **`InconsistentIndent`** — dedented to a level not on the indent
  stack.

### 11.2 Parse errors and recovery

The parser uses chumsky's error-recovery infrastructure to produce
multiple diagnostics per file. Two recovery layers:

- **Bracket-level recovery** — a failure inside `(…)`, `[…]`, or `{…}`
  produces an `Expr::Error` placeholder spanning the bracketed region.
- **Statement-level recovery** — a failure at the statement level
  skips tokens to the next `NEWLINE` (and any following balanced
  `INDENT…DEDENT` block) and produces a `Stmt::Error` placeholder.

A parse always returns a `ParseResult<T>` carrying *both* a partial AST
(possibly containing recovery placeholders) and a list of errors. See
[chl-parser/design-chl-parser.md](../chl-parser/design-chl-parser.md)
for the recovery design and error-rendering details.

### 11.3 Semantic errors

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

## 12. Examples

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

## 13. Reserved for future work

The following are deliberately omitted from CHL today, in some cases
with parser-level support that lowering rejects:

- **`while` loops** — currently a parse error (the `while` keyword is
  not yet recognised). Tracked as future work under mutability
  ("while loop lowering").
- **A nested `for` loop that writes no mutable variable declared outside
  it** — rejected at lowering: it has no recurrence of the loops around
  it to fold.
- **A mutable variable introduced inside a transaction block** — a `with
  begin():` block may write mutable variables declared outside it but not
  introduce its own, which would need a sequencing domain nested inside commit
  time. A loop body may introduce one (§4.6); commit time is what the loop
  around it does not supply.
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
- **Imports / multiple files** — CHL is single-file today. Modules,
  imports, runs, and parameters are **[Decided]** and specified in
  [9. Modules [Decided]](#9-modules-decided).
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
- **Pattern matching** beyond a `match` arm's single tag — `match` / `case`
  tag dispatch over a variant is implemented (§4.10), in both the indented and
  the one-line form, but patterns are shallow: no nesting, no literal patterns,
  and no per-arm guard.
- **Destructuring patterns** beyond tuples — record, variant, and
  wildcard patterns in assignment targets and `for` binders (a `match`
  arm's tag pattern is §4.10), and per-component annotations with `:`
  binding tighter than `,` (**[Decided]**, §4.3.1).
- **Unit values do not run** — the type surface is settled (`{}` for the type,
  `()` for the value, §6.6) and both typecheck, but a unit-valued program
  output cannot be materialized by the interpreter: it has no column
  representation, so `x = ()` compiles and then fails at runtime. This is a
  runtime gap, not a surface one.
- **The term-level delimiter migration** — record values are `(f=1, …)`, and `{…}` no longer
  denotes a term-level value (it is record-type / tuple-type / unit syntax,
  [2.4 Atoms](#24-atoms)). The map literal `[k -> v, …]` parses; reading it as a `Map` without
  `map([…])` remains **[Decided]**. Earlier plans to spell the entries `[k: v, …]`, `[k=v, …]`,
  or Unicode `[k ↦ v, …]` are superseded by the map-literal decision.
- **Map comprehensions** — `[k -> v for …]` parses as a comprehension of pairs
  ([3.12 Comprehensions](#312-comprehensions)); reading the result as a `Map` follows the
  map-literal decision above and is **[Decided]**, unimplemented. The north-star `storefront`
  `/stats` rollup uses it.
- **The target syntax at large** — the mutation and transaction **core is implemented** (`:=`,
  `with begin():`, `Mut(…, Txn)` mutable variables, feeds — §8), now spelled in the canonical target
  syntax: parenthesised type application (`Mut(V, Txn)`, `List(T)`) and capitalized primitive names
  (`Int`, `Bool`, `String`), with record types `{name: T, …}` and tuple types `{T, U}` writable in
  annotation position (§6.1), and variants writable in all three positions — type, term and pattern
  (§6.5, §3.15, §4.10). The remaining **Direction** notes are unimplemented: `rec` bindings (§4.3),
  destructuring patterns ([4.3.1 Destructuring patterns](#431-destructuring-patterns)), membership
  `in` ([3.4 Comparisons](#34-comparisons)), refinements
  ([6.4 Refinement syntax](#64-refinement-syntax)), the `Feed(_)` forward-declaration surface (§3.7,
  §6.2), and transactions-as-contextual-parameters (§8.7). The north-star programs pin the target;
  the sequencing is tracked

When each lands, this spec will be updated alongside the lowering and
the demo programs.

---

## See also

- [docs/design.md](design.md) — overall Cambra architecture.
- [chl-parser/design-chl-parser.md](../chl-parser/design-chl-parser.md) — the parser implementation.
- [src/ccl/design/](../src/ccl/design/README.md) — the CCL IR and the
  lowering/inference/optimization passes.
- [docs/operational-semantics/summary.md](operational-semantics/summary.md) — CCL's operational semantics.
- [docs/demo-programs.md](demo-programs.md) — runnable examples and their status.

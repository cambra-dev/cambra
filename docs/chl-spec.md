# CHL Language Specification (Draft)

This is the working specification of the **Cambra High-Level Language
(CHL)** — the surface language a Cambra programmer writes. The
specification describes CHL directly: what each construct *denotes*
(the value it computes) and, where applicable, what *effects* its
evaluation has on the program's feeds.

Compilation lowers CHL to the Cambra Core Language (CCL), where the
program is type-checked and run as producer/consumer dataflow. This
document mentions the lowering only when it makes a behavioural rule
easier to understand or pins down a corner case; the lowering itself
is specified in [src/ccl/design/lowering.md](../src/ccl/design/lowering.md)
and the operational semantics in [docs/operational-semantics/](operational-semantics/).

CHL today **looks** like Python, but it is not Python. Several Python
tokens are re-purposed (`<<`, `<<=`, `&`, `|`, `^`), one is new (`++`),
and Python features that don't fit the dataflow model (mutable identity,
exception handlers looked up at run time, classes, true division, etc.) are
absent.

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

An open bracket the source never closes is a lexical error (`UnclosedBracket`).
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
forall requires causes only   nothing except
type   impl   instance   trait
import use    as     pub    run    param  const  this
```

`where` is the refinement predicate separator (§6.4). It is lexed so the name is
**reserved**: a bare `where` is a keyword rather than an identifier. The refinement
syntax itself is parsed, in every annotation position that takes a type (§6.4).

`with` is a keyword: it introduces a transaction block, `with begin():`
(§8.2). It does **not** carry Python's general context-manager meaning.

A lambda is written `\x -> body` (§3.10); `\` and `->` are punctuation
(§1.8), not keywords, so `lambda` is an ordinary identifier — it, along with
`while`, `class`, `try`, `global`, `nonlocal`,
`del`, `assert`, `raise`, `is`, are **not** keywords in CHL today. Some are
reserved for future use. `raise` and `try` are **[Decided]** keywords
([Exceptions](#exceptions)), not lexed yet.

`import`, `use`, `as`, `pub`, `run`, `param` and `this` are the module keywords
([9. Modules](#9-modules)). `const` marks a parameter whose argument is a link-time constant
([9.19 Constants](#919-constants)).

`match` and `case` introduce tag dispatch over a variant (§4.10).

`type` declares a nominal type, `impl` its associated functions, `instance` an instance of a
trait, and `trait` a trait ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided),
[Declaring a trait](#declaring-a-trait), [Declaring an instance](#declaring-an-instance)).

`forall` begins a polymorphic type (**[Planned]**,
[Polymorphic type annotations](#polymorphic-type-annotations)), and in a `requires` clause a
requirement at every value of a type ([Family parameters](#family-parameters)).
`requires` begins a `requires` clause and `causes` a `causes` clause, which end a `def` signature
or a function type, and `only` and `nothing` bound one
([Writing requirements and effects](#writing-requirements-and-effects)).

> **Direction.** Planned binder/keyword vocabulary, not lexed today:
> `rec` (recursive binding — §4.3, **[Decided]**), and
> `assert` and its `static assert` form (function contracts — §6, **[Decided]** as the
> surface, **[Open]** as to what `static` demands). Avoid taking these names for other purposes.
> (`with`, `:=`, `match`, `case`, `where`, `forall`, `requires`, `causes`, `only`, `nothing`,
> `except`, `type`, `impl`, `instance`, `trait` and the module keywords are **already** lexed —
> the first two carry today's transactions and mutation, §8, `match`/`case` carry tag dispatch,
> §4.10, `where` separates a refinement's predicate, §6.4, `forall` and `requires` begin a
> polymorphic type and a `requires` clause, §6.10, `causes`, `only`, `nothing` and `except`
> write the other clause, bound both and take capabilities out of one, §6.9, and `type`,
> `impl`, `instance` and `trait` declare nominal types, their functions, instances and traits,
> §6.8 and §6.10 — so they are not in this list.)

### 1.7 Literals

| Form | Token | Notes |
|---|---|---|
| `0`, `42`, `1_000_000` | `Int(i64)` | Decimal only; no hex/bin/oct, no negation in the token (`-3` is `UnaryOp(Neg, 3)`). A `_` digit separator stands between two digits and does not change the value, as in Python and Go: `1_000` is `1000`. A misplaced separator (`1_`, `1__0`) makes the run of digits and separators one invalid token ([11.1 Lex errors](#111-lex-errors)). |
| `"hello\n"`, `'world'` | `String` | Double- or single-quoted. Escapes: `\n \t \r \\ \" \' \0`. Unknown escapes are preserved verbatim (the `\` is kept). A literal closes on the line it opens on: a raw newline before the closing quote is the lex error `UnterminatedString` ([11.1 Lex errors](#111-lex-errors)), so there are no multi-line strings. No triple-quoted `"""..."""`, no f-strings, no raw `r"..."`. |
| `True`, `False` | `Bool` | |

There are no floating-point literals — CHL has no `f64` type at the
surface level.

### 1.8 Operators and punctuation

```
+  -  *  **  //  ++  ->  =>  |=>
&  |  ^
== != <  <= >  >=
=  += -= *= //=
:=  <:  ::
<<  <<=
(  )  [  ]  {  }  ,  :  .  ;  \  `  !  @
```

`::` separates a qualifier from the name it qualifies: a module or a run from its member
(`cart::total`, [9.6 Qualified references](#96-qualified-references)), a module from its label or
tag (`r.mod2::f1`, `` mod2::`some ``, [9.12 Field labels and tags belong to a
module](#912-field-labels-and-tags-belong-to-a-module)), a nominal type from its method
(`Price::discounted`, [6.8 Nominal types and methods
[Decided]](#68-nominal-types-and-methods-decided)), and an instance of a trait from its function
(`a::area`, `summon(Area(_))::area`, [Summoning an instance](#summoning-an-instance)). A qualified
name parses wherever a name does.

Postfix `!` unwraps an `Option` proven not to be `Option::none`
([Subscript and unwrap syntax [Decided]](#subscript-and-unwrap-syntax-decided)). `!=` is one token,
so `x! == y` needs the space.

`:=` is the **mutation** operator (§4.3, §8.1) — it introduces and writes
a mutable variable. It is *not* Python's walrus operator: it is an
Algol-tradition assignment **statement**, and there is still no
assignment-as-expression.

`<:` is the bounded annotation: `x <: T` bounds the binder's inferred type
by `T` where `x: T` fixes it
([Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded)).

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

`|=>` is the data-function-type arrow: `D |=> V` is a collection over the domain `D`, writable
wherever `T => U` is
([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)).

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
([9.18 Reloading a program of modules](#918-reloading-a-program-of-modules)), `Discard`
([8.9 `@Discard` [Decided]](#89-discard-decided)) and `Builtin`
([9.16 The std root](#916-the-std-root)), so `@` never appears in any other position.
`@RenamedFrom` and `@Discard` parse, and lowering refuses them. `@Builtin` is **[Decided]**
and does not parse yet.

**[Decided]** — `@RenamedFrom` also decorates a `type` declaration and a constructor line inside
one ([Reloading a nominal type](#reloading-a-nominal-type)). Its argument there is a path:
`@RenamedFrom(Price)`, `@RenamedFrom(old_mod::Price)`, `@RenamedFrom(circ)`.

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
> asserts that it is shareable (§9.7) and reaches the shared import of its arguments;
> running one creates a run of its own. The engine runs one root module. Modules are
> specified in [9. Modules](#9-modules), whose statements (`import`, `run`, `param`,
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
                 |  decl_stmt
                 |  mut_assign_stmt
                 |  aug_assign_stmt
                 |  define_stmt
                 |  expr_stmt

return_stmt     ::= "return" [ expression ]
pass_stmt       ::= "pass"

assign_stmt     ::= assign_target "=" expression
ann_assign_stmt ::= assign_target ":" expression "=" expression
decl_stmt       ::= assign_target ":" expression
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

block_value     ::= if_stmt | match_stmt | try_stmt | with_stmt

aug_op          ::= "+=" | "-=" | "*=" | "//="

assign_target   ::= pair_target
                 |  pair_target ( "," pair_target )+ [ "," ]
pair_target     ::= target_atom [ "->" target_atom ]      -- a pair: the two-tuple (k, v)
target_atom     ::= ident                          -- `_` binds nothing
                 |  "(" assign_target ( "," assign_target )* [ "," ] ")"
                 |  type_path "::" ident [ "(" ident ( "," ident )* [ "," ] ")" ]  -- constructor

compound_stmt   ::= if_stmt | match_stmt | for_stmt | with_stmt | def_stmt
                 |  load_from_stmt | renamed_from_stmt | discard_stmt | pub_stmt

if_stmt         ::= "if" expression ":" block
                    ( "elif" expression ":" block )*
                    [ "else" ":" block ]

match_stmt      ::= "match" expression ":" NEWLINE INDENT case_arm+ DEDENT
case_arm        ::= "case" case_pattern ":" ( block | expression NEWLINE )
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

`assign_target` is a name, `_`, a nested tuple of targets, or a constructor pattern
([4.3.1 Destructuring patterns](#431-destructuring-patterns)) — **no
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
`expression` in the grammar, but lowering accepts only `begin()`. The optional `ident "="`
prefix names the block's transaction, which a program uses only before `::` (§8.7,
**[Decided]**). `with` does
**not** provide Python's general context-manager statement. A `try_stmt` and a `with_stmt`
as a `block_value` are **[Decided]**.

`decl_stmt` declares a feed with no value, `h: Feed(V)`
([Declaring a feed](#declaring-a-feed)); every other binding takes a value.

> **Direction.** Planned statement forms, not in today's grammar: `rec x = e` recursive bindings
> (**[Decided]**, §4.3), and out-of-line collection definition through a subscript target,
> `c[i] = v` (**[Tentative]**, §6.3 — this would relax the no-subscript-target rule above). A
> `type` declaration, a `def` whose name is qualified by a type (`def Price::discounted(…)`), and
> `@RenamedFrom` on either a `type` or one of its constructors are **[Decided]**, with their grammar
> in [6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided).
> (`mut_assign_stmt` and `with_stmt` above are already implemented — §4.3, §8; they are in the
> grammar, not this list.)

The module statements `import_stmt`, `run_stmt`, `param_stmt`, `renamed_from_stmt`, `discard_stmt`
and `pub_stmt` parse, with the productions of [9. Modules](#9-modules), and so does `const` before a
`param` ([9.19 Constants](#919-constants)).

### 2.3 Expression precedence

From lowest to highest; all binary operators are left-associative unless
noted:

| Level | Operator(s) | Notes |
|---:|---|---|
| 1 | `\x -> …` (lambda), `yield` | prefix forms; non-associative |
| 2 | `=>`, `\|=>` | function type and data-function type; *right*-associative — the codomain is the whole expression to its right ([1.8 Operators and punctuation](#18-operators-and-punctuation)) |
| 3 | `<<` | feed operator (right-associative is not meaningful — see [3.7 Feed operator `<<`](#37-feed-operator-)) |
| 4 | `->` | pair; non-associative — `a -> b -> c` is a parse error. The value admits a lambda, the key does not ([2.4 Atoms](#24-atoms)) |
| 5 | `e₁ if cond else e₂` | ternary; *right*-associative |
| 6 | `or` | short-circuit; n-ary flattening |
| 7 | `and` | short-circuit; n-ary flattening |
| 8 | `not` | prefix |
| 9 | `==` `!=` `<` `<=` `>` `>=`, and `in` `not in` (**[Decided]**) | chained, *not* left-fold (see [3.4 Comparisons](#34-comparisons)); `in` and `not in` do not chain ([Membership expressions](#membership-expressions-decided)) |
| 10 | `\|` | logical or |
| 11 | `^` | logical xor |
| 12 | `&` | logical and |
| 13 | `++` | collection union |
| 14 | `+` `-` | additive |
| 15 | `*` `//` | multiplicative |
| 16 | unary `-` | prefix |
| 17 | `**` | exponentiation; *right*-associative. It **straddles** the unary `-` at 16 rather than sitting under it — see below |
| 18 | postfix: `f(args)`, `x[i]`, `x.attr`, `x.0`, `summon(T)::f` | left-fold. The method call `x.m(args)` ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)) and the unwrap `e!` ([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)) join this level (**[Decided]**) |
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
perform an **effect** when evaluated. An effect is an output: a write to a
mutable variable, a contribution to a feed, a commit, an output outside the
program, or an exception
([6.9 Capabilities](#69-capabilities)).
The effecting forms:

- **Feed `<<`** (§3.7) appends its right-hand side to a feed.
- **A call to an effecting function** — one that writes a `Mut(…)` parameter (pass-by-reference,
  §6.2) or writes a transactional mutable variable in a `with begin():` block of its own or in the
  block that calls it (§8, §8.7, **[Decided]**) — performs that function's writes. A function's
  effects are always visible in its type: its `causes` clause states them, written or inferred.
  There are **no
  implicit-effect functions**, so an inert expression statement (§4.9) stays detectable and
  rejected.
- **`raise`** (**[Decided]**), a call that may raise, and an output outside the program, such
  as binding a
  sink ([6.9 Capabilities](#69-capabilities)).

`yield` (§3.13) is not an effect in this sense: it adds its operand to the
collection the enclosing generator function returns, which is that
function's result.

Mutation of a *variable* is a property of statements, not expressions:
`x := e` (§4.3, §8.1) writes a mutable variable, and loop accumulation
(§4.6) and transactions (§8.2) are the statement contexts that give those
writes their sequencing. A bare *reference* to a mutable variable is a
read — a dereference of its current value. It causes nothing; the effect
is carried by the `:=` write and the effecting call, never by the read.

Every other expression form is *pure*: it causes nothing, and its value depends only on its inputs.
What it requires does not make it impure: a read of an induction variable requires `Read(x)`, a read
of a transactional one `ReadTxn(x)` and `Transaction`, and a reading requires `ObserveWorld`,
but each has one value at each position ([6.9 Capabilities](#69-capabilities)). A
pure expression is safe to evaluate zero, one, or many times, and it is only over pure
sub-expressions that the freedoms below (unordered collections, unspecified evaluation order) apply.
Ordering *between* effects is not free-for-all: it is governed by the dependency-edge model of §8.5
— effects are ordered exactly by the data dependencies among them, and unordered (freely
interleaved) otherwise.

### Collections are unordered

A pervasive property of CHL semantics is that **collections are
unordered**. A list literal, a comprehension result, a generator's
yields, a feed stream — all denote *bags* (finite multisets) of
elements. Two collections with the same elements (with the same
multiplicities) are indistinguishable.

The consequence at the operational level: a `for` loop's iterations
may run in **any order, including in parallel**, unless they interact
([Ordered loops](#ordered-loops)).

Every collection is indexed by some type, the type of its **positions**: a list's positions are its
indices, a set's and a map's are its keys, and a comprehension result's are its generators'
([3.12 Comprehensions](#312-comprehensions)). Positions are generally not visible to users. They
fix the order of an ordered loop, and they match up data between coupled source/sink pairs like
`http_serve`.

The single way to introduce inter-iteration ordering is an **ordered loop**: one whose iterations
interact through a loop-carried accumulator (§4.6) or an exception escaping its body. It runs in
its source's position order ([Ordered loops](#ordered-loops)). No other construct sequences
iterations: the transactions of a loop's iterations are ordered by commit, not by position
([8.5 Ordering and concurrency](#85-ordering-and-concurrency)).

Lists do retain an integer-indexed *addressing* structure (a list is
a finite function from `0..n` to values, so `xs[i]` is well-defined
— §3.9). A list's indices are its positions, so an ordered loop over a list runs in index order.

### Ordered loops

**[Decided]** — the rules of this section.

A loop is **ordered** when its iterations interact: its body causes `Write(x)` for an induction
variable `x` bound outside the loop, an accumulator update made directly or by a call (§4.6), or a
`Raise(E)` that escapes the body ([Exceptions](#exceptions)). A body that may cause a top holding
either, `Effect`, `Write(*)` or `Raise(*)`, is ordered. A comprehension whose element, generator or
guard may raise is ordered the same way. Appends, reads, commits and `WriteTxn(x)` order
nothing: appends commute, and a read of an accumulator is sequenced by the writes it reads. A
`with begin():` block in the body commits by the event that triggers it, and its writes to
transactional variables take effect in commit order, which the transaction engine decides at run
time, not in the source's position order
([8.5 Ordering and concurrency](#85-ordering-and-concurrency)). A read of a transactional variable
sees whichever commits come before it in that order, as an as-of read does ([8.3 Reads](#83-reads)).
So a loop whose iterations only run blocks over transactional variables is unordered, and its
source's positions need no order:

```python
hits: Mut(Int, Txn) := 0
for x in a ++ b:
    with begin():
        hits := hits + x
```

A write to a non-transactional variable bound outside the loop orders it wherever the write
stands, beside a block or inside one. The iterations of every other loop are unordered.

An ordered loop runs its iterations one after another, in its source's **position order**:

| Source | Positions | Order |
| --- | --- | --- |
| `List(T)`, `Array(n, T)` | its indices | ascending |
| `Set(K)`, `Map(K, V)`, `FullMap(K, V)`, a `groupby` result | its keys, of type `K` | `K`'s order |
| a comprehension result | the tuples of its generators' positions ([3.12 Comprehensions](#312-comprehensions)) | lexicographic, the first-written generator's position first |
| a source | its arrivals | arrival order |

**The positions must be orderable.** An ordered loop requires `Orderable(P, P)` of its source's
position type `P`. A loop walks the collection its source's `Iterable` instance returns
([4.6 `for` — iteration](#46-for--iteration)), so a source of a nominal type has that collection's
positions. A loop over `Map(K, V)` that accumulates is accepted where `K` is orderable and rejected
otherwise, and a polymorphic `def` running an ordered loop over a parameter requires `Orderable` of
the parameter's positions in its type. A loop is ordered by what its body causes, not by what its
writes compute: `total += x` over a set whose elements have no order is rejected although `+`
commutes.

**A concatenation has no order between its parts.** `a ++ b` holds each part's positions tagged
with its part, and nothing about a union puts one part first, so an ordered loop over a
concatenation is rejected. So is one over a feed fed from more than one `<<`, which is the
concatenation of what each `<<` contributes. **[Open]** — how a program states the order such a
loop runs in.

The order is a fact about the source, not about the run, so two equal collections give an ordered
loop the same result. A position decides it, not an element: `last := v` over a map ends at the
value of the map's greatest key. A write to a variable bound outside two nested loops orders both.

#### Conditional ordering requirements

**[Decided]** Each loop places `OrderableFor(P, E)` on its source position type `P` and the
capabilities `E` of its body that escape an iteration. This built-in requirement is satisfied when
`E` excludes every effect that orders the loop. Otherwise it requires `Orderable(P, P)`.
`OrderableFor` has no user-declared instances and cannot be summoned. A contract may state it in a
`requires` clause. Its second argument is an effect clause, including clause variables and
`except`, rather than a value type.

An abstract clause that may contain an ordering effect retains `OrderableFor(P, E)` in the
function's inferred requirements. Each use substitutes its position type and effect clause into
the requirement. A callback that only appends admits unordered positions; one that may raise an
exception escaping the iteration requires orderable positions. Forwarding a callback retains the
requirement through each intervening function and module interface. A fully written function type
must state the requirement or bounds that imply it. Establishing `Orderable(P, P)` permits an
ordered iteration; the body's effects still determine whether the loop is ordered.

**Each nested loop has its own requirement.** Its body excludes writes to variables declared in
that iteration and exceptions caught within it. Discharging a capability outside that body does
not discharge the loop's ordering requirement. A write to an accumulator declared in an outer
iteration orders the inner loop but does not order the outer loop. An exception caught between
the two bodies has the same effect. A write to a variable declared outside both loops, or an
exception escaping both bodies, orders both. Evaluating an inner loop's source belongs to the
outer body; it does not belong to the inner body.

An inner loop's position type and effect clause are interpreted under the enclosing iteration's
binders. Generalization and substitution preserve those binders and retain each requirement
independently of the capabilities that escape the enclosing function.

### Evaluation order is unspecified

Most CHL expressions are *pure* (see the effect inventory above): a pure expression has no
observable effect, so the order in which the sub-expressions of a compound expression evaluate is
**not specified** by this document. Argument evaluation order in a call, operand order in a binary
operator, the relative order of two independent feeds in the same loop body — none of these are
sequenced unless they interact through effects (below). The append effects (`<<`, `yield`)
contribute to bag-valued feeds and generator results and commute, so they too impose no order among
themselves beyond data dependencies. The one place order *is* observable — effecting calls and
transactional writes — is governed by the dependency-edge model of §8.5, in which source position
decides only which way an edge points between two pieces of one evaluation that interact.

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
- written order within one evaluation, between statements, arguments or operands that
  interact through effects ([8.5 Ordering and concurrency](#85-ordering-and-concurrency)): one
  writes a variable the other reads or writes, or one may raise and the other causes something,
- sink contracts (e.g. `http_serve`'s response-paired-with-request
  rule — §7.3), which fix ordering at the boundary between the
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
equality. A wider record is not compared only on its shared fields. A tuple orders
lexicographically: by its first components, then, where they are equal, by its second, and so on,
each component supporting the ordering comparators. A record does not order, since its fields have
no order. Collection elements are not product fields, so these rules do not provide collection
equality or order. A nominal type compares as its declaration states
([Equality and order](#equality-and-order)).

`is` and `is not` are not operators. Membership `in` and `not in` are specified in
[Membership expressions](#membership-expressions-decided).

#### Membership expressions [Decided]

`e in c` is true when some item that iterating `c` yields equals `e`, and `e not in c` is
`not (e in c)`. Both answer `Bool`. Membership has no trait of its own; it places the iteration
and equality requirements ([Trait requirements](#trait-requirements)):

```
_ in _ : forall (C, E) {e: E, c: C} => Bool requires r: Iterable(C), r::Elements <: _ |=> E, Equatable(E, E)
```

- **`in` tests what iteration binds** ([4.6 `for` — iteration](#46-for--iteration)): the key of a
  `Set`, the value of an `Array`, `List` or `Collection`, and the entry `(k, v)` of a `Map` or
  `FullMap`. Key membership in a map is `k in m.keys()`. `k in m` with `k: K` is a type error,
  since the items of `m` are `(K, V)`.
- **The item type is `Equatable`.** A nominal item type has membership only through an
  `Equatable` instance ([Equality and order](#equality-and-order)). A collection whose items are
  collections has no membership test. A type with an `Iterable` instance has `in` with no further
  instance.
- **A wider `e` widens the collection.** `List`, `Set` and `Map` are covariant, so with
  `ks: List(Key)` and `Key` a refinement of `String`, `"x" in ks` is checked at `List(String)`.
- **Readiness follows checked lookup**
  ([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)). `true` can be
  answered once an equal item is present, and `false` requires the final collection. Over a live
  feed with no final domain, `false` may never be answered.
- **A true key-membership guard refines the key.** Under a true `k in s`, `k` is refined to the
  domain of `s`; under a true `k in m.keys()`, to the domain of `m`, so `m[k]!` checks there
  ([Subscript and unwrap syntax [Decided]](#subscript-and-unwrap-syntax-decided)). Value
  membership in a `List` gives no index evidence.

`in` and `not in` share level 9 with the comparators
([2.3 Expression precedence](#23-expression-precedence)), Python's placement, so an expression
groups as it does in Python. Unlike the comparators they do not chain: an `in` or `not in`
shares no chain with a comparator or with another `in`, and such a chain is a parse error that
asks for parentheses. Python's chain `x in s == t` means `x in s and s == t`, which no reader of
the first form expects.

| Source | Reads as |
|---|---|
| `k in s` | `k in s` |
| `i + 1 in ks` | `(i + 1) in ks` |
| `x in a ++ b` | `x in (a ++ b)` |
| `not k in s` | `not (k in s)`, which is `k not in s` |
| `k in m.keys() and m[k]! > 0` | `(k in m.keys()) and (m[k]! > 0)` |
| `a if k in s else b` | `a if (k in s) else b` |
| `\r -> r.key in allowed` | `\r -> (r.key in allowed)` |
| `{String where _ in ks}` | the strings `ks` holds |
| `u -> u in admins` | `u -> (u in admins)`, a pair whose value is a `Bool` |
| `x in s == true` | parse error; `(x in s) == true` |
| `a < b in s` | parse error; `(a < b) and (b in s)` |
| `x in s \| y in t` | parse error: `\|` binds tighter, so this is `x in (s \| y) in t`; `(x in s) or (y in t)` |

`for x in xs` and a comprehension's `for x in xs` keep `in` as a keyword. What stands between
`for` and that `in` is an `assign_target`, a name or a tuple of names, which holds no
expression, so its `in` is never read as membership. A pair target `for k -> v in m` is a tuple
target. The iterated expression after that `in` is an ordinary expression, so `for x in a in b`
iterates `a in b`.

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

`target` must be a **feed**, a value of type `Feed(V)`: a name declared
`h: Feed(V)` ([Declaring a feed](#declaring-a-feed)), a `Feed(V)`
parameter, or the response half of `http_serve` (§7.3). Feeding any
other value is a compile-time error.

Feeds against a given target are visible to anything that consumes
that target: a downstream comprehension iterating the stream, a sink
that dispatches the stream to an HTTP response, etc. The stream's
element type is the type of `value`, or where several feeds target one
feed, the join of their value types
([Joining the types of several values](#joining-the-types-of-several-values)).

A feed inside a loop contributes once per position of the loops between the target's declaration
and the `<<`, and the stream holds each contribution at its position. The element at a position is
typed there, so its type may read the loop variables, and the contributions of one `<<` are not
joined across positions:

```python
o: Feed(_)
for r in [1, 2]:
    o << [v for v in [1, 2, 3] if v > r]   # the row at r's position has the keys v > r
```

The two rows are collections over different keys, which have no join, and they need none: each is
typed at its own position. `box` (§7.4) is needed where a value's type does not follow from its
position, as between the values of two `<<` statements.

A stream fed from more than one site holds each contribution at its site paired with its position.
A site is a `<<` together with the calls that reached it, so one `<<` in a function called from two
places is two sites. A site that never fires is still one of the stream's sites. A program reads the
contributions and never a site. An edit moves a site only when it adds or removes a `<<` of the same
target, or a call spelled the same way, earlier under the same bindings, or renames a binding around
it. The bindings around a site are the `def`s and the assignments to a single name that enclose it.

The collection a feed accumulates is, like any CHL
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

#### Declaring a feed

A declaration with an annotation and no value introduces a feed:

```python
out: Feed(Int)
for x in [1, 2, 3]:
    out << x * 10
sum(out)                 # 60
```

The feeds of `out`, or its one `<<=` (§4.4), give it its value. A declaration is a statement, so a
feed may be declared wherever a statement stands, a function body included, and a function may
return the feed it declares. A declaration introduces a feed each time it runs: one per iteration of
the loops around it and one per call of the function it is in. `Feed(_)` infers the value type; a
written one is exact, the type every contribution has. The declaration is written with `:`: `Feed`
is invariant in its value type, so `out <: Feed(V)` would claim nothing `:` does not, and is a
compile-time error. Any annotation other than `Feed(…)` needs a value: `x: Int` with nothing after
it is a compile-time error.

`Feed(V)` is written at a binder, as `Mut(V)` is (§6.2): a declaration, a parameter, or an
annotated binding of a feed, `log: Feed(_) = out`. At a parameter or a binding it is optional: a
feed is a value, so a parameter bound to one is fed as the feed it names is:

```python
def fanout(a, b):
    h: Feed(_)
    for x in h:
        a << x
        b << x
    h
```

> **Direction.** **[Tentative]**: `<<` additionally becoming the general
> append operator for lists/sets/collections. **[Open]**: whether the
> `<<=` define-statement (§4.4) survives alongside declared feeds.

#### A deferred collection inside a data structure [Open]

A feed handle is a value: `http_serve` returns one as half of a tuple (§7.3), and a program can
put one in a tuple of its own, pass that tuple to a function, or build it in a loop body, then
feed the handle wherever it lands. A deferred collection's contributions are gathered where it
is declared, and a handle that travels inside another value can reach a feed from code its
declaration does not enclose, or be copied so that two places feed it at once. What such a
program means is open. Giving it a meaning needs a mechanism that follows where a handle goes,
such as an effect system or affine or linear types for feed handles.

Until then, a handle in a data structure has a meaning in one shape: a tuple literal bound by
`=`, each of whose elements is a literal, a source or a feed handle, taken apart by projection
or a tuple pattern (§4.3.1), as `requests, responses = http_serve(…)` is.

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

The callee is a name, a field of a product (`(r.f)(x)`), a call
(`add(1)(2)`), or a lambda (`(\x -> x + 1)(41)`). Any other callee
expression, such as `(f if c else g)(x)`, is a compile-time error.

A function is a value: it may be bound, passed as an argument, and held
in a tuple or record field. Every call must resolve to one function at
compile time. A program in which the function a call reaches depends on
run-time data is a compile-time error, whatever spelling reaches it:
`pick(c)(x)` where `pick` returns `inc if c else dbl`, or `g = inc if c
else dbl` followed by `g(x)`.

**No default values**, **no `*args`/`**kwargs`**, **no positional-only /
keyword-only markers**. A call's arguments are a parenthesised,
comma-separated list of expressions, or of `name=value` fields, which
build the record argument below: `f(x=1, y=2)` is `f((x=1, y=2))`. A
field's name may carry the module its label belongs to, `shop::amount=3`
([9.12 Field labels and tags belong to a module](#912-field-labels-and-tags-belong-to-a-module)).
A call that mixes expressions and fields is an error.

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

A function may declare no parameters (**[Decided]**), and a call of it passes no arguments:
`f()` applies `f` to
the unit, the product of no components. `def zero() => Int:`, `\ -> 3`, an associated function
`def Price::zero() => Price:` and a trait's `def one() => S` each take the unit. A call with no
arguments also opens a registered **data source**, `stdin()` (§7.3), and builds the empty map,
`empty_map()` (§3.11), and `begin()` is the context of `with begin():` (§8.2).

A pure function of no parameters returns one value at every call. One that requires or causes
something returns what its effects give at each call
([6.9 Capabilities](#69-capabilities)): `time::now()` takes
a reading at each position and call path
([Inputs from outside the program](#inputs-from-outside-the-program)).

> **Direction [Decided].** `empty_map()` becomes the values `Map::empty` and `Set::empty`
> ([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)).

### 3.9 Subscript and attribute access

Lookup and projection use the following syntax forms:

| Form | Meaning | Result |
|---|---|---|
| `c[k]` | Check a compatible key for membership and return the value if present. | `Option` of the value type. |
| `r.name` | Project a record field. | The named field's type. |
| `t.0` | Project a tuple field. | The positional field's type. |

A missing product field is a type error. Product projection and collection lookup are distinct:
`t[0]` is rejected, not interpreted as `t.0`. Projections compose, as in `r.p.1` and `t.0.b`.
An identifier cannot begin with a digit, so named and positional field syntax do not collide.

Checked lookup `c[k]` returns `Option::some` with the value when the key is present and `Option::none`
when absent. For a set, the value is unit. Presence can be established before the domain is final;
absence requires the final domain. A live feed with no final domain may never answer an absent-key
lookup.

The `!` operator can be used with lookup (as `c[k]!`) to return a non-option-wrapped value,
requiring a proof that `k` is in the domain of `c`.  A `FullMap(K, V)` accepts a key of type `K`; a
refined present-key domain instead requires membership in that refinement. Proven lookup does not
define an absent-key runtime result. `!` can be used generally as a postfix operator to unwrap
`Option` when it can be proven that it is an `Option::some`.

#### Subscript and unwrap syntax [Decided]

`c[k]` is the optional lookup. Its result is an `Option` refined by whether the key is present, and
postfix `!` takes an `Option` refined to exclude `none`:

```
_[_] : {m: Map(K, V), k: K} => {Option(V) where _.is_none() == (k not in m.keys())}
_!   : {Option(T) where not _.is_none()} => T
```

`Option` is a nominal type ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)),
so presence is stated by a term predicate over it rather than by a subtype naming one constructor.
`is_none` is a method of `Option` declared with it, and the predicate calls it because a nominal
type has no `==`. A lookup into a `Set` has the same type at `Option(unit)`. A lookup into an
`Array(n, T)` states presence as `i < n`, and a `FullMap` lookup's result is
`{Option(V) where not _.is_none()}` for every key. **[Open]** — the predicate a `List(T)` lookup
states presence by. An index drawn from iterating `xs` is present.

`c[k]!` is accepted exactly where the refinement on `c[k]` entails `not _.is_none()`: under an
`in` guard, for a key drawn from iterating `c`, or for a `FullMap`. Failure to establish presence
is a type error at `!`, not a runtime unwrap failure. `!` has postfix precedence;
`!=` remains one token, so `x! == y` requires a space before `==`.

> **[Interim]** The compiler accepts `!` only directly after a subscript, as `c[k]!`. A `!` after
> any other expression is a parse error.

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

An unpinned live feed still cannot establish absence. A provisional `Option::none` followed by a
correction would require incremental view maintenance, not an irrevocable answer.
A timeout-based answer would depend on wall-clock timing. These alternatives do not change
the current rule: a lookup decides absence only once the collection's domain is final.

### 3.10 Lambda

```
\x -> body
\x, y, z -> body
\x: T -> body                    -- a typed parameter
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

A parameter may state its type, `\x: T -> body` or `\x <: T -> body`, as a `def`'s parameter
does (§4.1), refinements included: an argument outside it is refused at the call. The annotation
ends at the `->` that ends the binder list, so a function type in it is parenthesised,
`\f: (Int => Int) -> f(1)`. In a type, a lambda is a family
([Family parameters](#family-parameters)). `\x -> x -> 1` (a lambda returning a pair, §2.4) is
unambiguous: the first `->` closes the binder list, and the rest is the body.

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
see [Re-keying is explicit](#re-keying-is-explicit-decided).

#### Empty forms

`[]` supplies no element type. Its uses or annotation constrain the type; an otherwise
unconstrained element type becomes unit. For example, `xs: List(Int) = box([])` selects `Int`.
A value it is joined with is a use: in `box([1]) if c else box([])`, `[]` takes the other
branch's element type, so the empty branch is an `Array(0, {Int where _ == 1})`.
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

#### Re-keying is explicit [Decided]

A literal is a positional collection, and a pair literal is a list of pairs. Only an explicit
constructor re-keys one: `set([…])` by the element, and `map([…])` by each pair's first component.
Neither an annotation nor a use inserts a constructor, so `m: Map(K, V) = [k -> v, …]` is a type
error pointing at `map([…])`, and a keyed lookup on a list of pairs does not make it a `Map`.
`Set`, `Map` and `FullMap` are nominal types
([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)), so a literal
reaches one of their types only as the argument of a function that answers it.

The constant-map rule rejects duplicate keys at compile time, applying the immutable
non-overlap rule described under [Collection types](#63-direction-collection-types-decided).
Mutable or fed collections instead use their declared merge law. The key type must support
equality; general discharge through contextual parameters remains planned.

The delimiter split retains `(…)` for products, `[…]` for collections and `{…}` for types.
Whether a future empty constructor can cover all collection kinds remains open; `empty_map()`
is the current keyed constructor, not a general empty-collection term. The values `Set::empty`
and `Map::empty` replace it ([3.8 Function calls](#38-function-calls)).

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
guard holds.

The result's **positions** (**[Decided]**) are those of the tuples it is taken over: the tuple `(p₁,
…, pₙ)` of the position `pᵢ` of each `xᵢ` in `xsᵢ`, or `p₁` alone for one `for` clause. A guard
drops a position and leaves the others as they are. The output's elements are a bag (§3), and
downstream consumers must not rely on the order in which the tuples were enumerated. An ordered loop
over the result runs in the lexicographic order of its positions ([Ordered loops](#ordered-loops)).

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

> **Direction — comprehensions and entry iteration [Decided].** A comprehension's result is a
> structural collection over its sources' domains, whatever its element and whatever its sources.
> It is never a `Set`, `Map` or `FullMap`. `[k -> v for …]` is a comprehension of pairs, the
> element `k -> v` being the 2-tuple `(k, v)`
> ([3.11 List, tuple, record literals](#311-list-tuple-record-literals)), and reading it as a `Map`
> is `map([k -> v for …])`. A set comprehension is `set([e for …])`.
>
> Iterating a **keyed** collection yields its *entries* as pairs, destructured with the 2-tuple
> pattern in the `for` binder: `for k -> v in m` (≡ `for (k, v) in m`), and likewise
> `for k -> g in groupby(c, key)`. A single binder takes the whole entry rather than the group
> ([4.6 `for` — iteration](#46-for--iteration)), so iterating the groups alone is
> `groupby(c, key).values()`.
>
> The `->` in a binder and the `->` in an element are both the 2-tuple, so
> `[k -> v for k -> v in m]` and `[e for e in m]` denote one collection. With `m: Map(K, V)`,
> both are a collection of `{K, V}` entries over `m`'s key domain: a lookup at a key of `m` answers
> that key's entry, and iteration yields the entries. `map(…)` of either is a `Map(K, V)` again.
> The group-by rollup composes as `map([k -> agg(g) for k -> g in groupby(c, key)])`.

### 3.13 `yield`

```
yield expression
```

`yield` is valid only inside the body of a `def` function. A function
containing any `yield` is a **generator function** (§4.2); `yield`
outside a `def` is a compile-time error.

Evaluating `yield e` adds `e` as one element of the collection that
the enclosing generator function returns. The
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
value is usable as a ``{`some{Int} | `none}``, a variant type and not `Option(Int)`, which is
nominal ([6.5 Variants](#65-variants)). Two consequences worth stating
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
> Within one file this changes nothing. A sum shared across modules is declared as a nominal type,
> whose constructors belong to the type rather than to a module
> ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)).

This is the polymorphic-variant model, and the **backtick** plays the role
capitalization plays in languages that capitalize constructors. Tags are
structural and undeclared, so name resolution cannot tell `some(v)` from a
call to a function named `some`, nor bare `none` from a variable read. The
backtick resolves that, and it is the *same* mark in every position — term,
pattern (§4.10) and type — so a tag never has to be recognised from
context.

A constructor is an ordinary atom, so it takes a postfix chain:
`` `some(r).x `` is the attribute `x` of `` `some(r) `` (§3.9).

An annotation writes the arms out, and a constructor flows into any variant type whose tags
include its own:

```python
x: {`some{Int} | `none} = `some(1)
z: {`ok{Int} | `err{String}} = `err("nope")
```

**Variants are structural, so a constructor synthesizes its own type.** `` `sme(1) ``
is the type ``{`sme{Int@1}}``, whatever the writer meant, and the payload type is
whatever term sits in the parens. A tag mismatch is therefore reported where the
constructor meets a counterpart that lacks the tag — an annotation, a `match` arm's
expected type, a join — rather than at the constructor.

**`Option` is a nominal type, not a variant.** `Option(T)` is a `type` declared in a std module,
with constructors `Option::some(T)` and `Option::none`
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)) and the method
`Option::is_none` that a lookup's refinement tests
([Subscript and unwrap syntax [Decided]](#subscript-and-unwrap-syntax-decided)). A structural
variant with the same arms is a different type, so `` y: Option(Int) = `some(1) `` is a type
error and `y: Option(Int) = Option::some(1)` is the spelling.

---

## 4. Statement semantics

A CHL program is a [top-level block](#21-top-level-block) of statements. Nonterminal statements
introduce bindings, perform effects ([feeds and effecting calls](#49-expression-statement)), or
contribute nothing (`pass`). A value-producing
block takes its value from its final contributing statement. A program that registers sinks,
such as `http_serve`, instead has an implicit record of those sinks as its program value.

For example:

```python
x = e₁
y = e₂
e₃
```

The block evaluates `e₃` with `x` bound to `e₁` and `y` bound to `e₂`. A binding is visible
from the statement after it to the end of its block, never before it. Evaluation order is
constrained only by data dependencies ([Evaluation order](#evaluation-order-is-unspecified)),
so this rule does not order independent bindings.

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

A non-generator function's body is a non-empty block whose last contributing statement supplies its
result. That statement may be an expression, `return`, a terminal `if`, `match` or `try`
(**[Decided]**), or a value-producing `with begin():` block (**[Decided]**). Each follows the
[block-value rule](#a-block-is-also-the-value-it-computes).

A function value captures the values of free names in its surrounding
scope at definition time (lexical capture). A captured mutable variable is
the exception: a call reads it at the call's own position in its history.

```python
cnt := 10
def f(x):
    cnt + x
cnt := 20
f(0)          # 20
```

A function cannot rebind a captured immutable name. It may read a captured induction variable while
inside its scope, or read and write a captured transactional variable. A transactional read or write
requires `Transaction`, which an enclosing `with begin():` block supplies, either in the function or
at its call (**[Decided]**). The function's contract records its reads and writes
([Capabilities](#69-capabilities)).

Recursion through self-reference is **[Planned]**; each function must be definable without referring
to its own name.

`=>` is the function-type arrow. `f: (T => U) = \t -> …` checks a lambda against the function type
`T => U`, which requires and causes nothing. A `def f(t: T) => U:` fixes its parameter and result
types but infers omitted capability clauses. An annotated binding admits capabilities only where its
function type states them ([Writing requirements and effects](#writing-requirements-and-effects)).
Recommended style annotates parameters and the result type of top-level `def`s.

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
| `target <<= value` | Gives the feed `target` the value `value` (§4.4). |

`target` is an `AssignTarget` (§2.2). Tuple destructuring:

```python
a, b = pair
(x, (y, z)), w = nested
```

is supported at any nesting depth, with or without parentheses around the pattern. A tuple
expression keeps its parentheses. `value` is evaluated in the scope before the statement, so
`b, a = (a, b)` exchanges the two names.

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
being bound. Patterns appear in four positions — an assignment target
(§4.3), a `for` binder (§4.6), a comprehension binder (§3.12), and a `case`
arm (§4.10) — and the same grammar serves all four.

```ebnf
pattern      ::= ident
              |  pattern ":" type                              -- annotated
              |  "(" pattern ( "," pattern )* [ "," ] ")"       -- tuple, parenthesised
              |  pattern ( "," pattern )+ [ "," ]               -- tuple, bare
              |  "(" field_pat ( "," field_pat )* [ "," ] ")"   -- record
              |  "`" tagname [ "(" pattern ( "," pattern )* [ "," ] ")" ]  -- variant (§6.5)
              |  type_path "::" ident [ "(" pattern ( "," pattern )* [ "," ] ")" ]  -- constructor
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

A **constructor** pattern mirrors a call of a nominal type's constructor
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)): one pattern
per declared parameter, in order, so `Shape::rect(w, h)` binds `rect`'s two parameters. `type_path`
is the type's name, qualified as anywhere else (`shop::Shape`). A constructor that declares no
parameters takes no parentheses, `Option::none`.

The wildcard `_` matches any value and binds nothing, so outside a refinement predicate (§6.4),
where `_` is the refined value, no term reads it. `_ := e` declares no mutable variable: it is
`_ = e`, which computes `e` and keeps nothing.

A **tuple** pattern takes apart a tuple of exactly its width ([Tuple width](#tuple-width)):
`a, b = (1, 2, 3)` is an error.

Patterns are still **static** — which names a binding introduces is
decidable from the syntax alone (§2.2). A pattern binds each name once: `a, a = p` is an error. A variant pattern and a constructor pattern are the forms
that can *fail* to match, which is why they appear only in a `case` arm or where the match is
exhaustive: a variant pattern against a single-tag variant type, and a constructor pattern against
a type that declares one constructor (`Price::new(r) = p`).

Today's grammar accepts the tuple forms, unannotated, with the annotation restricted to the whole
target (`ann_assign_stmt`, §2.2), the wildcard `_`, and a constructor pattern whose parameters are
names or `_`, alone or as a component of a tuple pattern (`(Price::new(p), q) = …`), on the left
of `=`, in a `for` binder and in a comprehension binder. Record and variant patterns, and
per-component annotations, are unimplemented.

### 4.4 Define statement `<<=`

```python
result <<= computation
```

`<<=` gives a feed its value outright. Semantics:

- The name on the LHS must be a feed (§3.7): a name declared
  `result: Feed(V)`, or the response half of `http_serve` (§7.3).
- `<<=` ties the feed to the RHS: from this point on, every consumer of
  the feed sees the value computed by `computation`.
- It is a compile-time error to `<<=` a name that is not a feed, or to
  `<<=` the same feed twice.

`<<` and `<<=` are the two ways to give a feed its value: `<<` *feeds*
elements into it during a streaming computation; `<<=` *defines* it
outright as a specific value. A single feed takes exactly one of these
forms.

`<<=` is **not** an augmented assignment — the grammar recognises it
as its own statement form.

> **Direction.** Whether the define-outright form survives beside
> declared feeds, and under what spelling, is **[Open]**.

### 4.5 `if` / `elif` / `else`

```python
if cond₀:
    block₀
elif cond₁:
    block₁
else:
    block_else
```

An `if` chain selects the first branch whose guard holds, in source order. If none holds,
it selects `else` when present; otherwise it produces no value or binding. Guards after the
selected branch need not be defined, and unselected blocks contribute no effects. These are
semantic selection rules, as for [short-circuit Boolean operators](#35-short-circuit-not-and-or).

An `if` chain produces a value when used as a block's final contributing statement or on an
[assignment's right-hand side](#43-assignment-forms). In those positions it requires an `else`,
and every branch must end in a value-producing statement. The chain's value is the selected
branch's value. The [ternary expression](#36-ternary) provides the one-line form of this choice.

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
| `Map(K, V)` / `FullMap(K, V)` | the entry `(K, V)` |

A **single** target binds the whole element; a **tuple / `->`** target
destructures it, so a map iterates entries unpacked as `for k -> v in m:` (the
north-star `storefront` rollup, §7.2). The keyed element carries its membership
proof, so for a key from `for k -> v in m` (or `for k in s`) the refinement on `m[k]` excludes
`Option::none`, and `m[k]! : V` type-checks (§3.9). Reaching a map's keys or values as their own
collections is `m.keys()` / `m.values()` / `m.items()` (§6.3).

**A loop walks its source's `Elements`.** `for x in c` places the built-in requirement `i:
Iterable(C)` on `c`'s type `C`, iterates `summon(Iterable(_))::elements(c)`, and binds `x` to each
value of `i::Elements` ([Trait requirements](#trait-requirements)). A structural collection,
including every comprehension result ([3.12 Comprehensions](#312-comprehensions)), is its own
`Elements`, so it yields its values. A nominal type yields what its module's instance returns. A
polymorphic `def` that iterates a parameter carries the requirement in its type: `def f(c): for x in
c: …` requires `Iterable(C)` of its parameter's type `C`, so each call iterates its argument by the
argument's own instance. An ordered loop requires `Orderable` of its source's positions
([Ordered loops](#ordered-loops)).

> **Direction [Decided] — the element is chosen per collection type.** `Set`, `Map` and `FullMap`
> are nominal builtins
> ([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)), and each
> satisfies `Iterable` through an instance the compiler provides, whose `Elements` yields what the
> table above lists.

> **[Interim].** Today `for`-in binds the **value** (codomain) for every
> collection — so a map iterates its values (as `groupby` results do) and a set
> iterates `unit`. A destructuring target takes the element apart, in either
> spelling, `(k, v)` and `k -> v` alike. Entry/key iteration is the [Planned]
> work; it only *adds* the type-directed element choice, so `for k -> v in m` is
> the form to write once it lands. Design:
> [collections.md, "Operations: how the trait layer dispatches [Planned]"](../src/ccl/design/collections.md#operations-how-the-trait-layer-dispatches-planned).

**Iterations are unordered and may run in parallel** (§3) unless the loop is ordered: a
loop-carried accumulator (below), or an exception escaping the body, sequences them in the
source's position order ([Ordered loops](#ordered-loops)).

A bare `for` loop in a non-generator context is an **effect
statement**: its purpose is to feed values into feeds as it
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

**Loop-carried accumulators.** A `:=` write (§4.3, §8.1) to a non-transactional name introduced
*before* the loop — a pre-loop `:=`, a function argument, or any binding from an enclosing frame —
is an **accumulator update**, not a per-iteration shadow. A write to a transactional variable inside
a `with begin():` block is not one: it commits in commit order (§8.5), so it orders no loop
([Ordered loops](#ordered-loops)). It introduces an inter-iteration data dependency that **forces
the loop to run sequentially**, in its source's position order ([Ordered loops](#ordered-loops)):

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

`pass` contributes no binding, value or effect. For example, it can leave one match arm empty:

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

An `if` with no `else` does nothing where its guards fail. A `match`'s arms partition the
scrutinee's tags, so a tag handled with no action still has an arm, and `pass` is its body.

Removing `pass` does not change a block's meaning, including when it is the last statement.
A value-producing block uses its last remaining statement. A function body containing only
`pass` is therefore rejected: it has no result.

Loop bodies, transaction bodies, and statement-position branches within them do not require
a result value. A loop containing only `pass` has no body effect and still iterates over its
source. A transaction containing only `pass` is rejected because a transaction must write or feed
([8.2 Transactions: `with begin():`](#82-transactions-with-begin)).

### 4.8 `return`

In a non-generator function:

```python
return                # equivalent to `return ()`
return expression
```

`return e` supplies a function result; bare `return` supplies unit. It does not perform an
early exit. It must be the final contributing statement of the function body or of each branch
of a terminal `if`/`else`. Further contributing statements after `return` are rejected.

The continuation is an explicit alternative rather than an early return followed by fallthrough:

```python
def choose(cond, a, b):
    if cond:
        return a
    else:
        return b
```

Generator functions have a separate rule for bare `return`, specified under
[generator functions](#42-def--generator-function).

### 4.9 Expression statement

A final expression statement supplies its block's value. A nonterminal expression statement is
evaluated only for what it causes
([6.9 Capabilities](#69-capabilities)), so one that causes
nothing is inert and is rejected. A statement that writes a variable, appends to a feed, commits a
transaction, causes `AffectWorld` or may raise an exception is not inert. What it requires does not
count: a call that only reads the clock is inert. In a polymorphic `def`, a statement calling a
function parameter causes whatever that function does, which each use decides, so the definition
does not reject it. See [Mutability, transactions, and feeds](#8-mutability-transactions-and-feeds).

---

### 4.10 `match` — tag dispatch

`match` selects a block by a variant's tag. Each tagged `case` names one tag and optionally
binds its payload within that arm:

```python
match x:
    case `some(v):
        v + 1
    case `none:
        0
```

A tag uses the same backtick spelling as a [variant constructor](#315-variant-constructors).
The payload forms are:

| Pattern | Means |
|---|---|
| `` case `tag(v): `` | the tag carries a payload; bind it to `v` |
| `` case `tag(_): `` | the tag carries a payload this arm does not read |
| `` case `tag: `` | the tag carries nothing |

A named payload binder is local to its arm. `_` discards the payload and cannot be referenced
by the body. Omitting the payload pattern is different: `` case `some: `` requires a
payload-less tag and does not match `` `some{Int} ``. Use `` case `some(_): `` to ignore a
payload without requiring its absence.

Each tag may appear in at most one arm. Tagged-arm order does not affect selection because
the arms partition tags, rather than testing overlapping patterns in priority order.
Patterns are shallow: there are no nested patterns, literal patterns or per-arm guards.

`case _:` is an optional default arm, without a backtick. It handles tags not named by other
arms and binds no payload, since those tags can carry different payload types. It must be
unique and last. A default-only match returns that arm's value without requiring a variant
scrutinee; the scrutinee is still checked for name resolution and type correctness.

> **Direction [Decided] — matching a nominal type.** An arm may name a constructor of a nominal
> type, `case Shape::rect(w, h):`, with one binder per declared parameter
> ([4.3.1 Destructuring patterns](#431-destructuring-patterns),
> [6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). The
> constructors are the tags the arms partition, so every rule above holds with "constructor" for
> "tag": each constructor is handled by one arm, and `case _:` covers the rest. The arms of one
> `match` name constructors of one type, and that type is the scrutinee's type, so a constructor
> pattern determines the scrutinee's type without an annotation. Tag arms and constructor arms do
> not mix in one `match`.

In a value position, including an assignment's right-hand side, every arm must produce a
value. A statement-position match is also allowed in a loop or transaction body. An arm may
contribute a yield or feed where the enclosing context permits it; the value can use the
payload binder and enclosing loop accumulators.

#### An arm on its `case` line

An arm whose body is one expression may write it on the `case` line, after the `:`, in place of
the indented block:

```python
match x:
    case `some(v): v + 1
    case `none: 0
```

The line break ends the arm, and arms of both shapes mix in one `match`. Such an arm means the
indented arm whose block is that one expression. The body is an expression, not a statement:
an assignment or a `:=` write takes the indented block. A line indented past the arm's `case`
line after a body on it is an error.

The `match` around such an arm is still the indented form, with one arm per line, so it needs no
bracket. Its arms stay unambiguous: an expression cannot derive a `match` outside a bracket
([The one-line form](#the-one-line-form)), so a `match` written after `` case `p: `` carries its
own bracket and its own arm list.

#### The one-line form

```
(match scrut: case `foo(x): x case `bar(y): to_x(y))
```

The one-line form uses one expression per arm instead of an indented block. `case` separates
the arms; no additional separator is used. The arm list consumes consecutive `case` clauses.

A one-line match requires enclosing parentheses, brackets or braces. It can occur within a
call argument, list or tuple element, subscript, record field, comprehension clause or
refinement predicate. Add parentheses when the surrounding position has no delimiter:

```python
n = (match msg: case `ping(seq): seq case `close: 0)
```

Nested one-line matches require their own delimiters. Without them,
`` match a: case `p: match b: case `q: 1 case `r: 2 `` does not identify which match owns
the final arm. Restricting only the immediate arm expression would not resolve this ambiguity:
lambda bodies and function-type codomains accept full expressions and could reintroduce it.

The indented and one-line forms use the same pattern, selection and value rules. An indented
`match` whose arms sit on their `case` lines
([An arm on its `case` line](#an-arm-on-its-case-line)) is the indented form.

**[Tentative]** Extending unused-binder `_` from patterns to lambda parameters requires a
binder-position rule distinct from the type-position wildcard in [Atoms](#24-atoms).

**[Tentative]** Per-arm guards, such as `` case `some(v) if v > 0: ``, would permit repeated
tags and make arm order observable. This extension requires a combined tag-and-guard selection
rule; it is not part of the guard-free match defined here.

---

## 5. Scoping and binding

CHL is lexically scoped. Each binding is visible only within its scope:

| Scope | Bindings and visibility |
| --- | --- |
| Top-level block | Value bindings are visible after their introduction. |
| Function or lambda | Parameters are visible in the body; free names refer to the enclosing scope. |
| Comprehension | Each generator binder is visible to subsequent clauses, guards and the element expression. |
| `for` body | The loop binder is visible only inside the body. |
| Match arm | Tag-payload and constructor-pattern binders are visible only in that arm. |

A binding statement (`=`, `x: T = e`, a `:=` introduction, `def`) binds its name from the next
statement to the end of its block.

A loop binder is not available after the loop. Iterations are unordered, so there is no final
iteration value to bind there. Results needed outside a loop must be carried by a loop-carried
accumulator or fed to a feed; see [iteration](#46-for--iteration).

An immutable binding shadows an earlier binding with the same name for the rest of its scope.
The earlier value is no longer accessible through that name. A write to an existing mutable
binding advances its history rather than introducing a shadowing binding. Defining a feed with
`<<=` resolves an existing feed's name; it does not introduce another name.
See [Assignment forms](#43-assignment-forms), including the open question about shadowing
under the decided timeless-equation model.

There is no `global` or `nonlocal` declaration. Functions access enclosing value bindings
through lexical capture, whose current write restrictions and decided extension are specified
under [function definitions](#41-def--function-definition).

> **Direction [Decided].** The top-level scope is its module's. Import
> names, run names, and parameters are in scope throughout the module,
> and another module's member is reached by a qualified name, `m::f`,
> including through a parameter of `Module{…}` type
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
- `List(T)` — finite collection of `T`-values, indexed by `0..n`.
  The index → element mapping is part of the value (so `xs[i]` is
  well-defined); iteration order, however, is unspecified (§3). Written
  `List(T)` or `List(_)`.
- `{T₀, T₁, …}` — tuple type (structural `{…}` type syntax — §6.1). The
  one-element case is `{T,}`, with the comma required, and a comma-free
  `{T}` is a parse error (§2.4, §3.11). The zero-element case is `{}`
  itself — the unit type ([The empty product is unit](#66-the-empty-product-is-unit)). Its width
  is part of the type ([Tuple width](#tuple-width)).
- `{T₀, …, Tₖ, ..}` — open tuple: every tuple of at least these positions. It is written only
  as a bound ([Tuple width](#tuple-width)).
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
  entry pairs that `map([…])` re-keys.
- `FullMap(K, V)` — *total*-map type (§6.3): every value of `K` is a key. `K` is the finite domain
  of keys present in what built the map, and only `groupby` builds one, so a lookup always finds
  its key. Today the proven lookup `m[k]!` answers `V`, and the key's type is its proof. Under
  [Subscript and unwrap syntax [Decided]](#subscript-and-unwrap-syntax-decided) the checked
  lookup `m[k]` answers `{Option(V) where not _.is_none()}`, which `!` unwraps without a proof at
  the call.
- `Time` — a position in the commit order (**[Tentative]**). A transaction's time is one, which
  `txn::now()` answers for a transaction named `txn` (**[Decided]**, §8.7).
- `{T₀, T₁, …} ⇒ U` — function type. A function takes exactly one
  argument (§3.8): an n-parameter function's domain is the
  corresponding tuple type, and a keyword-argument function's domain
  is a record type — `{x: T, y: U} ⇒ V`. Surface syntax uses the `=>`
  function. A `def` or a lambda has a function type, and a comprehension or a literal is a
  collection: the construct decides, and an annotation states it.
- `D |=> V` — data-function type: a collection over the domain `D` (§6.3).
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
> (§7.3).
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
> draws its cut points) need elaboration. A recurring contract is factored into a nominal type
> whose constructor's parameter type carries the refinement, `type Price = {Int where _ >= 0}`,
> so every construction discharges it and no function repeats it
> ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)).
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
so they are lowercase — `` `ok ``/`` `err ``, `Option::some` — and
only the type (`Option(T)`) is capitalized. `Caps` means *type*, without
exception (unlike ML and Rust, which capitalize constructors). A
**variant tag** additionally carries the `` ` ``
prefix in every position (§6.5); the capitalization rule is
what fixes their case, and the backtick is what marks them as tags rather
than ordinary names. A nominal type's constructors are lowercase for the same reason, and take no
backtick: they are declared names, reached through their type as `Option::some`
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)).

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

`Mut(V)`, `Mut(V, Txn)` and `Feed(V)` are **implemented**. Mutation and
transactions are specified in §8, feeds in §3.7, and the two supporting
rules below hold. `Feed(V)` is written at a binder: a declaration, a
parameter, or an annotated binding
([Declaring a feed](#declaring-a-feed)).

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
| a feed (§3.7) | every `<<` statement's contribution, each typed at its loop position |

The join keeps what every value establishes and drops the rest, so a refinement
survives only where all of them carry it: `1 if c else 2` is `Int`, `5 if c else 5` is
`Int@5` (§3.1), and `[5, 5]` has element type `Int@5` where `[5, 6]` has `Int`.

**Where the values establish nothing in common there is no join, and the construct is
a compile-time error.** `1 if c else "x"` is rejected rather than given some
`Int`-or-`String` type, and the same holds for a `match` whose arms disagree or a
mutable variable written at two unrelated types. Cambra has no anonymous union type to
fall back on; to carry values of several types in one place, say which by tagging them
— a variant (§6.5) if the tags are meaningful to the program, `box` (§7.4) if they
are not.

> **Direction [Planned] — joining two collections.** Two collections that are not the
> same collection — `xs if c else ys` over lists of different length — establish
> nothing in common either, because a collection's elements are indexed and the two
> disagree about which indices exist. The two answers a program might want differ: one
> keeps both possibilities and which occurred, the other forgets which collection it is
> and with it the length. Neither is the default, so the program says which. `box` asks
> for the first (§7.4); a `List(T)` or `Collection(T)` annotation asks for the second
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
present in its producer, not every value of the key's base type. **[Decided]** — `groupby` is
the only operation that builds a `FullMap`. No annotation converts another collection to one, so
a `FullMap`'s key type is always such a finite present-key domain. A `List` hides its domain
length in a sum witness; it does not store a separate length field in a product representation.
The current representations are specified in
[The six collection types](../src/ccl/design/collections.md#the-six-collection-types).

The implemented annotation forms are not six nominal types. `Set(K)` and `Map(K, unit)` lower
to the same representation. `Array` and `FullMap` have explicit domains; the other four are
dependent sums. Introducing one of those sums from a concrete collection requires `box`.
Existing sums can widen under the sum-kind relation; that relation is not automatic insertion
of a constructor into an unboxed term.

**A data-function type `D |=> V`** is a collection over `D` with values of type `V`.

- **A bare `_` domain admits a sum.** A sum is a collection whose domain is its witness, so
  `_ |=> V` accepts a plain collection and a `List`, `Collection` or boxed value alike. It is an
  inferred annotation, so it admits more than `Collection(V)`, which is exact and requires `box`.
  An instance's associated type is one type at every use, so there `_ |=> V` is a plain
  collection.
- **A written domain names a plain collection.** `String |=> Int` is a collection over every
  `String`, and no sum is one. A type parameter is a written domain: in
  `def both(D, a: D |=> Int, b: D |=> Int)`, `a` and `b` are plain collections over one domain,
  and two different domains are refused. A parameter that names a sum's witness is **[Open]**.

#### Collection operations

- Arrays and lists have positional order. Sets, maps and generic collections have no
  implicit order. Ordering follows from the type and is not stored. Order-dependent operations
  over unordered collections take an explicit
  ordering instance. Default parallel iteration and loop-carried dependencies are specified in
  [Iteration](#46-for--iteration); storage order does not establish a source-language ordering.
- Membership `in` tests the items iteration yields, so a map's keys are tested through
  `m.keys()` ([Membership expressions](#membership-expressions-decided)). A true key-membership
  guard refines the key for proven access.
- Maps iterate entries, sets keys, and arrays/lists/collections values. The methods
  `m.keys()`, `m.values()` and `m.items()` of a `Map` or `FullMap`, and `s.keys()` of a `Set`,
  expose lazy collection views. Numeric `sum(m)` rejects entries; `sum(m.values())` requests
  value aggregation.
- Arrays and lists share the `[…]` literal, chosen by annotation or usage. A set or a map is
  always built by `set([…])` or `map([…])`, since nothing re-keys a literal implicitly. The
  constructors and constant-element rule are in
  [List, tuple, record literals](#311-list-tuple-record-literals).
- Immutable collections support non-overlapping element-wise definitions `c[i] = v`.
  Feed uses `c << v`, and keyed mutation uses `c[i] := v`. Their current supported forms
  belong to [Mutability, transactions, and feeds](#8-mutability-transactions-and-feeds).

**`Set`, `Map` and `FullMap` are nominal builtins [Decided].** Each is a nominal type
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)) that the
compiler provides, so `Set(K)` and `Map(K, unit)` are distinct types. Nothing relates one of the
three to a structural collection type: none widens to `Collection`, and the methods `keys`,
`values` and `items` are the written route. `FullMap` has every operation `Map` has, and differs
only in how it is built and in its lookup's refinement. The operations of all three are built in:
lookup, iteration, the methods `keys`, `values` and `items` (`keys` alone for a `Set`), and the
re-keying constructors `set([…])` and `map([…])`. Membership `in` is not one of them: it comes from
the `Iterable` instance ([Membership expressions](#membership-expressions-decided)). The
representation is
[Telling `Set` and `Map` apart](../src/ccl/design/collections.md#telling-set-and-map-apart-decided).

A builtin differs from a declared nominal type in four ways:

- **No constructors or `extract`.** A program builds one through `set`, `map`, `groupby` or an
  empty value, and takes it apart through its operations.
- **Associated values.** `Set::empty` and `Map::empty` are values of the builtin, whose type
  parameters are determined by their use ([Type parameters](#type-parameters)). A declared type
  has no spelling for an associated value
  ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)).
- **Trait instances.** All three satisfy `Iterable` through instances the compiler provides
  ([Trait requirements](#trait-requirements)). A declared type satisfies the traits its module
  declares instances of ([Declaring an instance](#declaring-an-instance)).
- **Stated variances.** A declared type's variance is read off its constructors' parameter types,
  and a builtin has none to read, so each is stated. `Set(K)` is covariant in `K`, and `Map(K, V)`
  in both `K` and `V`: a map over keys below `K` is a map over keys below any supertype of `K`.
  `FullMap(K, V)` is invariant in `K`, since its key type is its domain and a collection's domain
  is its data. Two `FullMap`s over one key type relate key by key: `FullMap(K, V₁)` is a subtype
  of `FullMap(K, V₂)` when, at every key `k`, `V₁` at `k` is a subtype of `V₂` at `k`.

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
is **[Decided]** ([Membership expressions](#membership-expressions-decided)):

```python
ks = ["a", "b"]
Key = {String where _ in ks}    # the strings `ks` holds, and no others
```

A refined key type of that shape is what a total map's domain is (§6.3). A
refinement with nothing in scope but `_` speaks only about its one anonymous
subject. A refinement inside a `type` declaration names only `_` and constants
([9.19 Constants](#919-constants)), since the declaration's values keep its type for as long as
they live ([Nominal type identity](#nominal-type-identity)). **[Planned]** — it may also call a
function that may be called in a constant.

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

What a checked lookup returns
([3.9 Subscript and attribute access](#39-subscript-and-attribute-access),
[6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)) is `Option(T)`,
a nominal type and not a variant
([3.15 Variant constructors](#315-variant-constructors)): the variant language privileges no tag,
so ``{ `some{T} | `none }`` is an ordinary variant type and a different type from `Option(T)`. A
sum that several modules share, such as a `Result`, is declared as a nominal type the same way
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). Within one
module a sum such as ``{ `ok{T} | `err{E} }`` may be written as its arms, or named by a type alias
(§6.7) at a fixed payload type.

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

### Tuple width

A tuple's width is part of its type. `{T₀, …, Tₙ₋₁}` is a subtype of `{U₀, …, Uₘ₋₁}` exactly when
`n = m` and each `Tᵢ` is a subtype of `Uᵢ`. Tuples differ from records here: a record with extra
fields is a subtype of one without them
([The empty product is unit](#66-the-empty-product-is-unit)), and a tuple with extra positions is
not a subtype of a shorter one.

- A tuple pattern takes apart a tuple of its own width
  ([4.3.1 Destructuring patterns](#431-destructuring-patterns)). `a, b = (1, 2, 3)` is an error.
- Tuples of two widths have no join ([Joining the types of several values](#joining-the-types-of-several-values)).
  `(1, 2) if c else (1, 2, 3)` and `[(1, 2), (1, 2, 3)]` are errors.
- A key of a map keyed by pairs is a pair. `m[(1, 2, 3)]` on a `Map({Int, Int}, V)` is an error.

**An open tuple** `{T₀, …, Tₖ, ..}` is every tuple of at least `k + 1` positions whose position `i`
is a subtype of `Tᵢ` for each `i ≤ k`. It lists at least one position: `{..}` is an error. An open
tuple is a subtype of another when it lists at least the other's positions, each a subtype of the
one listed there, and it is a subtype of no tuple of a fixed width.

No value has an open tuple type, because a tuple value has one width. An open tuple is written
only as an upper bound, after `<:`:

- on a value parameter, `t <: {A, ..}`, or a binding, `x <: {Int, ..} = e`
  ([Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded)). Inside
  that bound it may also be a tuple or record component or a function's result:
  `r <: {p: {Int, ..}}`.
- as a type parameter's bound, `T <: {A, ..}` ([Kinds and bounds](#kinds-and-bounds)). There it
  is the whole bound. A definition reads a value of a type parameter through its bound, so with
  `R <: {p: {Int, ..}}`, `r.p` on `r: R` would have an open tuple's type, which no value has. A
  nested open tuple bounds a type parameter of its own instead: `B <: {Int, ..}, R <: {p: B}`.

Anywhere else it is an error: an exact annotation, a result annotation, a function's domain, a
`Mut(…)`, a collection's element.

A projection `t.i` requires a tuple of at least `i + 1` positions, so its type is
`forall (A₀, …, Aᵢ, T <: {A₀, …, Aᵢ, ..}) T => Aᵢ`. Each use fixes `T`, and with it the width:

```python
def first(A, t <: {A, ..}) => A:
    t.0

first((1, 2)) + first((10, 20, 30))   # 11
```

**The program fixes every width.** A tuple has the width it is built with, and a parameter has the
width of its argument at each call. A tuple that only projections reach, such as the parameter of
`\t -> t.0` where nothing applies the lambda, has no width, and the program is an error.

A diagnostic printing an inferred polymorphic type
([Polymorphic type annotations](#polymorphic-type-annotations)) writes an open tuple as a type
parameter's bound: `def first(t): t.0` prints as `forall (A, B <: {A, ..}) B => A`.

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

A `type` declaration binds a capitalized name to a new **nominal** type by listing its
**constructors**:

```python
type Option(T):
    some(T)
    none

type Shape:
    circle(radius: Int)
    rect(w: Int, h: Int)
```

`Shape` is distinct from every other type, including a structural variant with the same arms, which
is the difference from an alias ([6.7 Type-alias statements](#67-type-alias-statements)). When two
spellings name the same nominal type is
[Nominal type identity](#nominal-type-identity).

#### Declaring a nominal type

```ebnf
type_stmt   ::= "type" Ident [ "(" type_param ( "," type_param )* [ "," ] ")" ] ":"
                NEWLINE INDENT ctor_line+ DEDENT
             |  "type" Ident [ "(" type_param ( "," type_param )* [ "," ] ")" ] "=" expression
                NEWLINE
type_param  ::= Ident [ ":" expression ]   (* the expression is a kind *)
ctor_line   ::= [ "@" "RenamedFrom" "(" ident ")" NEWLINE ]
                ident [ "(" ctor_param ( "," ctor_param )* [ "," ] ")" ] NEWLINE
ctor_param  ::= [ ident ":" ] expression

-- A type the version this source replaces held under another name or in another module.
renamed_type_stmt ::= "@" "RenamedFrom" "(" type_path ")" NEWLINE type_stmt
```

`type_path` is in [Associated functions and methods](#associated-functions-and-methods), and
`@RenamedFrom` on a type and on a constructor is
[Reloading a nominal type](#reloading-a-nominal-type).

- **A `type` is declared at a module's top level, once.** A `type` inside a `def`, a loop or any
  other block is an error, and so is a second binding of its name in the module, public or private,
  with both sites named.
- **Each constructor line declares a function that builds the type's values.** `Shape::rect` has type
  `{Int, Int} => Shape`, and `Option::some` has type `forall (T) T => Option(T)`. A constructor that
  declares no parameters is a value: `Option::none` has type `forall (T) Option(T)`, its `T`
  determined by the use ([Type parameters](#type-parameters)). The constructor set is closed.
- **A constructor's parameter names are not record labels.** `radius` names the parameter for
  documentation and diagnostics, and a call is positional: `Shape::circle(1)`. A call from another
  module therefore writes no qualified label
  ([9.12 Field labels and tags belong to a module](#912-field-labels-and-tags-belong-to-a-module)).
- **Constructors are lowercase and take no backtick.** They are declared names that belong to their
  type, reached as `Shape::circle`, or `shop::Shape::circle` from a module that imports `shop`.
- **A parameter type may name the type being declared and the module's other types**, so recursive
  and mutually recursive types are written directly:

  ```python
  type Tree:
      leaf
      node(Tree, Tree)
  ```

- **A parameter type may carry a refinement** ([6.4 Refinement syntax](#64-refinement-syntax)), and
  each construction discharges it. This is how a nominal type states a domain invariant once, for
  the contracts direction of [6. Types (informal sketch)](#6-types-informal-sketch):
  `type Price = {Int where _ >= 0}`. The predicate names `_` and constants,
  `type Capped = {Int where _ <= limit}` under `limit = 10`
  ([9.19 Constants](#919-constants)). **[Planned]** — a constant whose value is a tuple, a record
  or a list, and a call to a function that may be called in a constant.
- **Each type parameter's variance is computed from the parameter types of the constructors.** A
  parameter that appears only in covariant positions, such as `some(T)` or a field of a product, is
  covariant. One that appears only in contravariant positions, such as the domain of
  `on(T => Int)`, is contravariant. One that appears in both, or under an invariant constructor
  such as `Mut(T)`, is invariant. `Option`'s `T` is covariant, so `Option({a: Int, b: Int})` is a
  subtype of `Option({a: Int})`. A parameter's kind is `Type`, written or not, or a family's,
  `K => Type` ([Family parameters](#family-parameters)). A bound on a declaration's parameter is
  **[Open]**.
  - **A position inside a position composes their variances.** Covariant inside contravariant is
    contravariant, contravariant inside contravariant is covariant, and invariant inside anything
    is invariant. `T` is covariant in `on((T => Int) => Int)`. A collection's domain is its data,
    so a parameter in one, as `K` in `FullMap(K, Int)`, is invariant.
  - **A parameter inside another nominal type takes that type's parameter variance**, composed by
    the same rule. `T` in `wrap(Option(T))` is covariant, and the builtins' variances are listed in
    [6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided).
  - **A recursive declaration's variance is the least fixpoint.** Every parameter starts with no
    variance. Each round computes the variance of every occurrence, reading a recursive occurrence
    at the previous round's answer, and the rounds repeat until no answer changes.
    `type Stream(T): cons(T, Stream(T))` settles at covariant. In
    `type Ping(T): p(T, Ping(T) => Int)`, the direct `T` gives covariant and the next round adds
    contravariant through the domain, so `T` settles at invariant.
  - **A join of two values of one type joins argument by argument.** A covariant argument joins
    and a contravariant one meets. An argument invariant because its parameter appears at both
    polarities joins where the parameter is read and meets where it is written, so
    `Cell::cell(1, f) if c else Cell::cell(2, g)`, for `type Cell(T): cell(T, T => T)`, has a type
    both arms have: what it holds reads as `Int`. An argument invariant because its parameter
    appears at an equality position, as `K` in `index(FullMap(K, Int))`, has no join unless the
    two arguments agree, as two collections over different domains have none.
  - **The variance is part of the type's interface.** Adding `on(T => Int)` to a covariant type
    makes it invariant, which changes subtyping at every use, so the interface a module check
    prints states each parameter's variance
    ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)).
- **Every type parameter appears in some constructor's parameter type.** One that no constructor
  uses is an error at the declaration. Its variance could not be read off the constructors, and
  distinct nominal types already keep values such as `UserId` and `OrderId` apart.

#### The single-constructor form

`type N(P…) = R` declares `N` with the one constructor `new(R)`, and also declares the method
`N::extract` of type `N(P…) => R`. `N::extract(n)` means `(match n: case N::new(r): r)`, and
`n.extract()` is the same call ([Associated functions and methods](#associated-functions-and-methods)).

```python
type Price = {amount: Int}

p = Price::new(amount=3)    # the call's parentheses build the record argument
p.extract().amount          # 3
```

Only this form declares `extract`. A type declared by a constructor list takes its values apart
with patterns, even when it has one constructor.

**[Tentative]** — the name `extract`. The method shares the type's namespace with its own
associated functions, so whatever name it takes is unavailable to every type declared with `= R`.

#### Family parameters

A parameter whose kind is a kind arrow, `V: K => Type`, is a **family parameter**: it takes a type
for each value of `K`. The declaration applies it to the value binders of the types it writes,
`(k: K) |=> V(k)`. In the kind, `=>` is the kind arrow, not a function type: `K` is the type of the
values `V` is indexed by, and `Type` is what `V` gives at each
([Kinds and bounds](#kinds-and-bounds)).

```python
type Groups(K, V: K => Type) = (k: K) |=> V(k)

gs = Groups::new(groupby([1, 2, 3], \x -> x > 1))
# gs's type, as a diagnostic writes it:
#   Groups({Bool where _ in [1 > 1, 2 > 1, 3 > 1]},
#          \k: {Bool where _ in [1 > 1, 2 > 1, 3 > 1]} ->
#              {UInt where _ < 3 and ([1, 2, 3][_]! > 1) == k} |=> Int)
```

- **A family is indexed by values.** `V: {K₁, K₂} => Type` takes a type for each pair of
  values and is applied as `V(a, b)`, as a function over `{K₁, K₂}` takes two arguments
  ([3.8 Function calls](#38-function-calls)). The index types name the declaration's other
  parameters. A kind's domain is a type, so `V: Type => Type` is an error: no parameter is
  indexed by a type. A curried kind, `K₁ => K₂ => Type`, is an error.
- **A kind may name its domain's value, `V: (k: K) => Type`.** Nothing reads the name, so the
  kind is `K => Type`.
- **A parameter that is not a family is one type at every value.** A value whose type differs
  with a binder outside the parameter does not fit it: `type M(K, V) = K |=> V` admits no
  group-by, whose groups' domains differ by key, and `V: K => Type` admits one.
- **A function type names its domain's value as `(k: K) |=> T`**, which `T` reads in refinements
  and family applications, in any annotation: `def f(g: (k: _) |=> (_ |=> Int))`.
- **A family parameter is applied to distinct binders in scope.** `V(k)` names a binder of a type
  around it, and `V(k, k)`, `V(k + 1)` and a bare `V` are errors. Passing it to another family
  parameter, or as `FullMap`'s value type, passes the family:
  `type Outer(K, V: K => Type) = Groups(K, V)`, and `FullMap(K, V)` is `FullMap(K, \k -> V(k))`,
  which is `(k: K) |=> V(k)`.
- **A family parameter's index types are its binders' types.** The binder it is applied to, the
  family parameter it is passed to, and the map key it is read at range over its index type, up
  to refinements: `V: String => Type` is not applied to `(k: Bool)`.
- **A family is written as a lambda, `\k: K -> T`**, a type `T` for each value `k` of `K`, which
  `T` reads in refinements and family applications. A binder written without its type, `\k -> T`,
  ranges over the type the family is taken at, and a family over two values is `\a, b -> T`. A
  family stands only where one is taken: as a family parameter's argument, and as `FullMap`'s
  value type, whose binder is the key, `FullMap(K, \k -> V)`. A `forall` binding a value,
  `forall (k: K)`, writes no family: it states a requirement at every value of `K`, below.
- **Any other type where a family is taken is the family constant at it**: one type for every
  value, whose holes read no binder. `Groups(_, _ |=> Int)` refuses a group-by, whose groups'
  domain reads the key; `Groups(_, \k -> _ |=> Int)` names the binder its holes read, and
  `Groups(_, _)` infers the whole family.
- **Two families relate value by value.** `\k: K -> T₁` is a subtype of `\k: K -> T₂` when `T₁`
  is a subtype of `T₂` at every `k`. A family parameter's variance is computed from the
  constructors as any parameter's is, and an index type is invariant.

A polymorphic type's and a `def`'s type parameter may be a family parameter too. Two parameters of
one family state that two values share it, and inside the body an application of it is opaque, as
a type parameter is:

```python
def first(K, V: K => Type, a: Groups(K, V), b: Groups(K, V)) => Groups(K, V):
    a
```

A bound on a family's values is a requirement in the definition's `requires` clause, under a
`forall` that binds the family's index:

```ebnf
requirement ::= …
             |  "forall" "(" ident ":" expression ( "," ident ":" expression )* [ "," ] ")"
                ( requirement | "(" requirement ( "," requirement )* [ "," ] ")" )
             |  expression "<:" expression
```

```python
def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) V(k) <: _ |=> Int:
    sum([sum(grp) for grp in g])
```

- **`forall (k: K)` binds `k`, a value of `K`, over exactly one requirement.** Parentheses group
  several: `requires forall (k: K) (V(k) <: U, W(k) <: X)`. Braces in a type never group
  ([2.4 Atoms](#24-atoms)), so a bound is written bare, as above, or in parentheses.
- **`forall` means every value.** A use is checked with `k` abstract, so the requirement holds at
  every value of `K`, not only at the values the use's arguments hold.
- **`V(k) <: U` bounds the family's values.** Every value of the family is a subtype of `U`, the
  call is rejected where one is not, and the body uses `V(k)` as a `U`, as it uses a bounded type
  parameter ([Kinds and bounds](#kinds-and-bounds)). `V` is a family parameter of the definition,
  applied to the `forall`'s binders, each once, and bounded once. Each binder ranges over the
  index type `V` takes it at, up to refinements.
- **A hole in a requirement under `forall` is inferred separately at each value of `k`.** It is a
  family parameter of the definition, a type for each `k`, where a hole in an unquantified clause
  is a type parameter ([Trait requirements](#trait-requirements)). So `_ |=> Int` admits groups
  whose domains differ by key.

**[Planned]** — a bound that reads a `forall`'s binder,
`requires forall (k: K) V(k) <: {Int where _ <= k}`; a trait requirement under `forall`,
`requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int)`; a subtype requirement on
anything but a family parameter's values; and a `requires` clause on a type declaration, which has
none.

#### A nominal type is opaque

- **Subtyping relates a nominal type only to itself and its refinements.** Nothing relates `N` to
  its constructors' parameter types, to `R` in the single-constructor form, or to another nominal or
  structural type, in either direction. Within one nominal type:
  - A type without parameters is related only by reflexivity: `Price <: Price`.
  - A type with parameters relates two applications argument by argument. `N(a…) <: N(b…)` holds
    when each pair of type arguments is related as its parameter's variance requires: `a <: b` for
    a covariant parameter, `b <: a` for a contravariant one, and `a = b` for an invariant one.
    `Option`'s `T` is covariant, so `Option(A) <: Option(B)` exactly when `A <: B`.
  - The implicit arguments of [Nominal type identity](#nominal-type-identity) are compared for
    identity, not by variance: `eu::Order` and `us::Order` are unrelated even where
    `stripe::Receipt <: paypal::Receipt`.
  - A refinement of a nominal type is related to it by the ordinary refinement rule
    ([6.4 Refinement syntax](#64-refinement-syntax)): `{Option(V) where not _.is_none()}` is a
    subtype of `Option(V)`, which is what a lookup's result relies on
    ([Subscript and unwrap syntax [Decided]](#subscript-and-unwrap-syntax-decided)).

  A join of two different nominal types, or of a nominal type and a type that is neither it nor a
  refinement of it, is an error at the join.
- **A nominal value is built only by its constructors and taken apart only by them.** A `match` over
  its constructors ([4.10 `match` — tag dispatch](#410-match--tag-dispatch)), a constructor pattern
  ([4.3.1 Destructuring patterns](#431-destructuring-patterns)), `extract`, and the type's own
  functions are the only ways in. A nominal value has no fields: `p.amount` is an error, and
  `p.extract().amount` is the projection.
- **A declared nominal type satisfies the traits its module declares instances of**
  ([Declaring an instance](#declaring-an-instance)), and no other. None is inherited from the
  constructors' parameter types: `type Price = {Int where _ >= 0}` is not `Addable` because `Int`
  is. An instance of an arithmetic operator's trait defines the operator on its values, and an
  instance of `Equatable` or `Orderable` lets them be compared and makes them keys of a `Set`, a
  `Map` or a `groupby` ([Equality and order](#equality-and-order)). Deriving an instance from the
  constructors, as with Rust's `#[derive]`, is **[Open]**. The nominal builtins `Set`, `Map` and
  `FullMap` satisfy the built-in instances of `Iterable`, which the compiler provides.
- **The type of a nominal value is fixed by the expression that produced it.** Every producer of a
  value names the same nominal type, so a method and a trait requirement resolve the same way
  wherever the value flows.
- **A value identifies its constructor by name.** A value is held as the name of its constructor
  and that constructor's arguments. The name, and not the constructor's position in the
  declaration, identifies the constructor, so reordering a declaration's lines changes nothing.
- **A value names its declaration** (**[Decided]**). A value of a declared nominal type carries the
  declaration its constructor belongs to, as the version of the program that built it defines it,
  and compares in that declaration's order ([Equality and order](#equality-and-order)).
- **[Open] — erasure after inference.** The first implementation keeps a declared nominal type
  until operator conversion, which reads a value's shape off its constructors' parameter types, and
  erases the nominal builtins once inference has resolved their operations. Whether a value keeps
  the whole type, its arguments included, past inference, which could bound the data it holds, is
  not decided.

#### Associated functions and methods

```ebnf
def_stmt    ::= "def" ( ident | Ident "::" ident ) "(" [ params ] ")"
                [ "=>" expression ] [ requires_clause ] ":" block
type_path   ::= [ module_path "::" ] Ident
```

`type_path` names a type where another production takes one, such as a constructor pattern
([4.3.1 Destructuring patterns](#431-destructuring-patterns)); `module_path` is
[9.2 Imports](#92-imports)'s.

A `def` whose name is qualified by a type declares an **associated function** of that type. It binds
no module-level name, and is reached through its type:

```python
def Price::of_cents(c: Int) => Price:
    Price::new(amount=c)

Price::of_cents(250)
```

**A method is an associated function whose first value parameter is `self`.** For a type without
parameters `self` is the type and takes no annotation. For a parameterised type, `self` is annotated
with the type applied to the function's own type parameters
([Type parameters](#type-parameters)):

```python
def Price::discounted(self, pct: Int) => Price:
    …

def Option::or_else(T, self: Option(T), d: T) => T:
    match self:
        case Option::some(v):
            v
        case Option::none:
            d
```

A method is reached two ways:

| Written | Means |
| --- | --- |
| `p.discounted(10)` | the method call: `discounted` of `p`'s type, with `p` as `self` |
| `Price::discounted(p, 10)` | the same call, naming the type, with `self` passed first |
| `Price::discounted` | the method as a function value, of type `{Price, Int} => Price` |

`Price::discounted` names the method without an instance. It is how a call states which type's
method it means, and the method as an unapplied value has no other spelling.

- **A type's constructors, its associated functions, and the `new` and `extract` of the
  single-constructor form share one namespace.** Two entries of one type with one name are an error
  naming both sites. Two types in one module may each have a `discounted`.
- **An associated function may declare no parameters** (**[Decided]**). `def Price::zero() =>
  Price:` is called `Price::zero()` ([3.8 Function calls](#38-function-calls)). A constructor that
  declares no parameters is a value instead, written without parentheses.
- **An associated function reaches nothing a run gives its module.** Every run of a module shares a
  type that reaches none of the module's parameters
  ([Nominal type identity](#nominal-type-identity)), so each run's copy of the type's functions must
  be one function. An associated function reads no mutable variable, feed or source of its module,
  no value parameter, no member of a Module-typed parameter, and no member of a run the module
  declares, directly or through the module's bindings and functions, and an error names what it
  reads. A run's type's functions and constructors are not such members: every run shares the
  type, whose own module holds its functions to this rule. A type parameter of the module that it
  reaches the same way, or through a run's type whose identity takes it, is part of the type's
  identity instead. So is a `const` parameter it reaches ([9.19 Constants](#919-constants)), so the
  value parameters it may not read are those without `const`.
- Whether a module other than the type's own may declare an associated function of it is **[Open]**.

**An `impl` block declares a type's associated functions together.** It is shorthand for writing
each `def` with the type's name:

```ebnf
impl_stmt   ::= "impl" Ident [ "(" Ident ( "," Ident )* [ "," ] ")" ] ":"
                NEWLINE INDENT ( [ "pub" ] def_stmt )+ DEDENT
```

```python
impl Option(T):
    def or_else(self, d: T) => T:
        match self:
            case Option::some(v):
                v
            case Option::none:
                d

    pub def is_none(self) => Bool:
        …
```

- **Each `def` in the block is the `def` qualified by the type.** `def or_else(…)` inside `impl
  Option(T):` declares `Option::or_else`, and every rule above applies to it unchanged. A `def` in
  the block names no type of its own: `def Other::f` inside `impl Option(T):` is an error. The block
  binds no value names: its functions reach each other as `Option::f` or `self.f()`, and `pub`
  stands on each `def`.
- **A parameterised type binds its parameters once.** `impl Option(T):` names the type's
  parameters, and each `def` in the block takes them as type parameters
  ([Type parameters](#type-parameters)), with `self` of type `Option(T)` unannotated. A `def` may
  add type parameters of its own.
- **The block names a type of its own module.** `impl shop::Price:` from another module is the
  spelling an extension would take, and is **[Open]** with extensions. An `impl` head naming a trait
  is an error: an instance of a trait is declared with `instance`
  ([Declaring an instance](#declaring-an-instance)).

**Methods and fields are separate namespaces, and the parentheses decide which is meant.**
`r.f(args)` is a method call, and `r.f` is a field and never a method. A nominal value has no
fields, and a structural record has no methods, so `r.f(args)` on a record whose field `f` holds a
function is an error. Calling the function a field holds is written `(r.f)(args)`
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

**A method call needs its receiver's type.** `x.m()` resolves `m` from the type of `x`, which
anything in the program may determine, before or after the call. Where that type is part of a
polymorphic binding's type, only the binding's definition determines it, since each use instantiates
the binding's type at its own types ([6.10 Polymorphic types](#610-polymorphic-types)). In
`[p.cents() for p in prices]`, the type of `prices` determines the type of `p`. In
`apply_to(\p -> p.cents(), price)`, where the first parameter of `apply_to` is declared
`Price => Int`, passing the lambda does. A `def inner(u): p.cents()` nested in a `def outer(p)` has
a type that does not contain the type of `p`, so a statement of `outer` after `inner` may determine
it. When nothing determines that type to be a nominal type, the call is a type error that asks for
an annotation on `x`. A polymorphic `def` therefore calls no method on a value whose type is one of
its type parameters, or on one only its uses would determine. An operation that works across types
is a trait's function, read from an instance, `summon(Area(_))::area(s)`
([Summoning an instance](#summoning-an-instance)).

- **A trait's functions are not methods.** `x.m()` names only a method of `x`'s type, so a type's
  method and a trait's function may share a name, and two traits may declare functions of one
  name: `c.area()`, `summon(Area(_))::area(c)` and `summon(Surface(_))::area(c)` are three calls.

### 6.9 Capabilities

**[Decided]** — refusing a function that outlives a variable it names, and a nested transaction, by
their capabilities; `Transaction` in a function a block calls ([8.7 Transactions as contextual
parameters](#87-transactions-as-contextual-parameters)); readings ([Inputs from outside the
program](#inputs-from-outside-the-program)); exceptions ([Exceptions](#exceptions)); naming another
module's public transactional variable, `WriteTxn(inv::stock)`; sink functions and calls made
outside the program ([Output outside the program](#output-outside-the-program)); and keeping
readings across a reload and a restart ([Inputs from outside the
program](#inputs-from-outside-the-program)). The rest of this section is implemented.

A function's type states what a call reads from its context, in its **`requires` clause**, and what
the call contributes besides its result, in its **`causes` clause**. A requirement is an input that
the context supplies. An effect is an output.

| Context requirement | Supplied by | Required by |
| --- | --- | --- |
| `Transaction` | a `with begin():` block, for its body ([8.7 Transactions as contextual parameters](#87-transactions-as-contextual-parameters)) | a read or a write of a transactional mutable variable |
| `ObserveWorld` | the run, at every position ([Inputs from outside the program](#inputs-from-outside-the-program)) | opening a source, a reading |
| `ReadTxn(x)` | the run, at every position | a read of the transactional mutable variable `x` |
| `Read(x)` | the scope binding `x`, to every call inside it | a read of the induction variable `x` |

| Effect | Caused by |
| --- | --- |
| `WriteTxn(x)` | a write to the transactional mutable variable `x`: `x := e` or a compound assignment, passing `x` to a `Mut` parameter, or a call to a function that writes `x` |
| `Write(x)` | a write to the induction variable `x`: `x := e`, a compound assignment, passing `x` to a `Mut` parameter, or a call to a function that writes `x` |
| `Append(f)` | a contribution to the feed `f`: `f << e`, `f <<= e`, passing `f` to a `Feed` parameter, or a call to a function that appends to `f` |
| `RunTransaction` | a `with begin():` block ([8.2 Transactions: `with begin():`](#82-transactions-with-begin)) |
| `AffectWorld` | an output outside the program ([Output outside the program](#output-outside-the-program)) |
| `Raise(E)` | `raise e` with `e` of type `E` ([Exceptions](#exceptions)) |

`yield` is not an effect: what a generator function yields is its result
([3.13 `yield`](#313-yield)).

**A context requirement and an effect are capabilities.** Each states what a call does
besides computing its result, and they differ only in direction: a requirement is an input the call
takes from its context, and an effect an output it gives its context. `Read(x)` and `Write(x)` are
the two directions of an induction variable, `ReadTxn(x)` and `WriteTxn(x)` the two directions of
a transactional one, `ObserveWorld` and `AffectWorld` the two directions of
the world outside the program, and `Transaction` and `RunTransaction` the two directions of a
transaction. A capability passes from a callee to each of its calls, whichever direction it has,
and leaves only at the construct that discharges it ([Discharging requirements and
effects](#discharging-requirements-and-effects)). Where direction matters, in which pieces of an
evaluation are ordered ([8.5 Ordering and concurrency](#85-ordering-and-concurrency)) and in whether
a statement is inert ([4.9 Expression statement](#49-expression-statement)), each capability's own
direction decides, not the clause that lists it.

The capabilities in the tables are every capability there is, and a program declares none of its
own: `Raise` takes a type, so each type a program raises gives one more effect, such as
`Raise(Negative)`. `Read`, `Write`, `ReadTxn`, `WriteTxn` and `Append` take a variable.

A trait requirement stands in the same `requires` clause and is not a capability. It is a parameter
of a polymorphic definition, and each use passes the instance its types pick ([Trait
requirements](#trait-requirements)), so it is resolved where a function value is made, and no
construct discharges it. Elsewhere in this section a requirement is a capability: `Transaction`,
`ObserveWorld`, `ReadTxn(x)` or `Read(x)`.

**Capabilities form sets.** A `causes` clause states a set of effects. The context requirements of a
`requires` clause form a set too; its trait requirements state instance obligations separately.
Listing a capability twice, or listing capabilities in another order, gives the same set. `nothing`
is the empty set. A clause is not a type: no value has a clause as its type, and the join of
[Joining the types of several values](#joining-the-types-of-several-values) never applies to one. A
**clause variable** stands for a clause, as does an associated type that a trait bounds by `Effect`
or `Context` ([Effects in traits](#effects-in-traits)). One stands in a clause beside its
capabilities, and that clause is the union of the clause it stands for with the rest. `Effect` is
the clause of every effect and `Context` the clause of every requirement, and each clause variable
is bounded by one of them ([Kinds and bounds](#kinds-and-bounds)). Written in a clause, each stands
for that clause, so a function of type `Int => Int requires Context causes Effect` may require and
cause anything. A family's **top** is the clause of every capability of the family: `Write(*)` of
every write to an induction variable, `WriteTxn(*)` of every write to a transactional one,
`Append(*)` of every append, `Read(*)` and `ReadTxn(*)` of every read of an induction and a
transactional variable, and `Raise(*)` of every exception. A **run's top** is the clause of every
read, `ReadTxn(inv::*)`, or every write, `WriteTxn(inv::*)`, of a transactional variable of the run
`inv` or of a run it declares ([Transactional state belongs to the
run](#discharging-requirements-and-effects)). `Effect` and `Context` are tops too, and a top stands
in a clause as a capability does. A top is written with `*`, since `_` in a clause is a hole that
inference fills ([Writing requirements and effects](#writing-requirements-and-effects)): `Write(_)`
is an error.

An expression requires and causes what its parts and the calls it makes require and cause. A
block, a function body and a module's top level require and cause what their statements do, less
what they discharge ([Discharging requirements and effects](#discharging-requirements-and-effects)).

#### Writing requirements and effects

```ebnf
def_stmt        ::= "def" ident "(" [ params ] ")" [ "=>" expression ]
                    [ requires_clause ] [ causes_clause ] ":" block
fun_type        ::= expression "=>" expression [ requires_clause ] [ causes_clause ]
requires_clause ::= "requires" ( "nothing" | [ "only" ] requires_item ( "," requires_item )*
                                [ except_requires ] )
causes_clause   ::= "causes" ( "nothing" | [ "only" ] causes_item ( "," causes_item )*
                              [ except_causes ] )
requires_item   ::= requirement | "(" requirement except_requires ")"
causes_item     ::= effect | "(" effect except_causes ")"
except_requires ::= "except" ( requirement | "(" requirement ( "," requirement )* ")" )
except_causes   ::= "except" ( effect | "(" effect ( "," effect )* ")" )
requirement     ::= … | [ ident ":" ] "Transaction" | "ObserveWorld" | "ReadTxn" "(" states ")"
                 |  "Read" "(" variables ")" | "Context" | Ident | "_"
effect          ::= "Write" "(" variables ")" | "WriteTxn" "(" states ")"
                 |  "Append" "(" variables ")" | "RunTransaction" | "AffectWorld"
                 |  "Raise" "(" raised ( "," raised )* ")" | "Effect" | Ident | "_"
variables       ::= ( variable | "*" ) ( "," ( variable | "*" ) )*
states          ::= state ( "," state )*
state           ::= variable | "*" | ident "::" "*" | "Module" "::" "*"
raised          ::= expression | "*"
variable        ::= ( ident "::" )* ident
```

`requirement`'s other alternatives are those of [Trait requirements](#trait-requirements).
`txn: Transaction` names the transaction a call's block supplies `txn`, which the body uses only
before `::`, as in `txn::now()` ([8.7 Transactions as contextual
parameters](#87-transactions-as-contextual-parameters)). A
capitalized name standing alone in a clause, other than the built-in `Transaction`, `ObserveWorld`,
`RunTransaction`, `AffectWorld`, `Context` and `Effect`, is a clause variable or an associated type
standing for a clause. One in a `causes` clause is bounded by `Effect`, and one in a `requires`
clause by `Context` ([Kinds and bounds](#kinds-and-bounds),
[Effects in traits](#effects-in-traits)). Any other is an error, so a raised type is written
`Raise(NotFound)`, never `NotFound` alone.

A capability that takes an argument takes a list: `WriteTxn(stock, orders)` is
`WriteTxn(stock), WriteTxn(orders)`, and `causes Effect except WriteTxn(inv::*, stock)` takes both
away. A list that names a top beside a capability the top holds, as `WriteTxn(*, stock)` does,
is an error, as an `except` item that takes nothing away is.

- **An omitted clause in a `def` is inferred.** `def total(xs): …` requires and causes what its
  body does.
- **A written clause in a `def` is a lower bound.** `def lookup(k) causes Raise(NotFound):` states
  that a call may raise `NotFound`, and inference adds the rest of what the body causes. A call sees
  every written requirement and effect whether the body has it or not, so a library may state an
  effect its body does not cause yet. A `@Builtin` function has no body to add to its clauses, so
  they are exact ([9.16 The std root](#916-the-std-root)).
- **`only` also bounds what the body may add.** The listed capabilities remain in the contract,
  even where the body does not require or cause them. Under
  `causes only WriteTxn(stock), Raise(NotFound)`,
  an effect the body causes beyond those listed is an error at the line that causes it, with a
  secondary label at the clause. `nothing` is the empty upper bound:
  `def norm(v) requires nothing causes nothing:`.
- **A trait requirement on a type parameter is always written.** A type parameter is opaque
  ([Type parameters](#type-parameters)), so inference adds no requirement on one, whether the
  clause is a lower or an upper bound ([Trait requirements](#trait-requirements)).
- **A written type's clauses are exact.** A function type `A => B` with no clause requires nothing
  and causes nothing, in an annotation, a parameter's type, a Module type's entry and a trait's
  signature alike. `_` in a clause stands for what inference supplies, as it does in a type:
  `A => B causes _`.
- **A clause runs on through each item that may belong to it.** Each item of a clause begins with
  a capitalized name, `_` or `(`, so a clause could run on into a parameter after it: in
  `def g(E <: Effect, F <: Effect, f: Int => Int causes E, F, s: Int)`, `F` would be a second
  item. A function type with a clause is therefore parenthesized in a parameter list, last
  parameter included, `def apply(f: (Int => Int causes E), xs)`, and an unparenthesized one there is
  an error. One that another type follows, in a tuple or a type's arguments, is parenthesized
  too: `{(Int => Int causes E), Int}`.
- **A hole that a `def`'s body leaves open is a variable.** In
  `def apply_all(f: (Int => Int causes _), xs): [f(x) for x in xs]` nothing fixes the hole, so
  `apply_all` has type
  `forall (E <: Effect) {(Int => Int causes E), List(Int)} => List(Int) causes E`, as a type that a
  body leaves open makes a `def` polymorphic ([6.10 Polymorphic types](#610-polymorphic-types)). A
  variable is written where an upper bound relates two positions:
  `def apply_all(E <: Effect, f: (Int => Int causes E), xs) causes only E`.
- **A hole that a bounded clause reaches takes its bound.** A `_` in a parameter's type whose
  capabilities the `def`'s bounded clause receives admits what that clause does, besides what
  the body discharges on the way: in
  `def p(f: (Int => Int causes _), x: Int) => Int causes nothing: f(x)`, `f`'s clause is
  `causes nothing`, so `p` has type `{Int => Int, Int} => Int`, and a use passing a function
  that appends is refused at the call.
- **A function type that requires and causes less is a subtype.** `A => B requires R₁ causes E₁`
  is a subtype of `A => B requires R₂ causes E₂` when every item of `R₁` is an item of `R₂`, and
  every item of `E₁` is an item of `E₂` or a `Raise(S)` below one, `Raise(T)` with `S <: T`
  ([Exceptions](#exceptions)). A clause variable is an item like any other. A top in `E₂` or `R₂`
  holds every capability of its direction or family that its `except` list does not take away, so
  `Write(x)` is below `Write(*)` and `Write(*)` below `Effect`. A run's top holds the family's
  capabilities for the run's variables and its runs': `WriteTxn(inv::stock)` is below
  `WriteTxn(inv::*)`, which is below `WriteTxn(*)`. A top in `E₁` or `R₁` is below only
  a top holding all it holds, and a clause variable is below a top only where its bound takes away
  all the top does: `E <: Effect except RunTransaction` is below `Effect except RunTransaction`,
  and `E <: Effect` is not.
- **`except` takes capabilities out of a clause's variables and tops.** A clause ending in
  `except c`, or in `except (c₁, …, cₙ)` for several, holds the capabilities it lists, and what its
  clause variables and its tops stand for less each `cᵢ`: `causes Effect except RunTransaction` is
  every effect but `RunTransaction`, and `causes Raise(NotFound), Effect except Raise(*)` raises
  only `NotFound`. A listed `Raise(T)` takes away each `Raise(S)` with `S` a subtype of `T`, and a
  listed top all it holds, so `causes Effect except (Write(*), Raise(*))` writes no variable and
  raises nothing. Each `cᵢ` is taken from each top only as far as the top holds it, and one that a
  clause without variables holds none of is an error. A clause variable may stand before `except`
  as `Effect` does: a `try` around a call of `f: Int => Int causes E` that catches `Int` causes
  `E except Raise(Int)`, and a parameter `f: (Int => Int causes E except RunTransaction)` takes only
  a function that does not commit. A top or a clause variable in parentheses with an `except` of
  its own takes it away from that item alone: `causes E, (Write(*) except Write(x))` may write `x`
  if `E` does, and `causes (E except Raise(Int)), F` raises `Int` only if `F` does.
- **A monomorphic function type requires only context requirements.** A function value's trait
  requirements are resolved where it is made, so its type's `requires` names only `Transaction`,
  `ObserveWorld`, `ReadTxn(x)`, `Read(x)`, the tops `Context`, `ReadTxn(*)`, `ReadTxn(inv::*)` and
  `Read(*)`, and clause variables bounded by `Context`. A polymorphic type has one
  clause after its function type's codomain, holding its trait requirements and its context
  requirements together ([Polymorphic type annotations](#polymorphic-type-annotations)).
- **An arrow takes the clauses written after its codomain.** `=>` groups to the right, so in
  `A => B => C causes E` the clause is `B => C`'s, and `A => (B => C) causes E` gives it to the
  outer arrow.
- **A diagnostic and `cambra check` print each clause in full,** inferred parts included
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)).

The three forms relate the body's inferred effects `E` to the stated set `X` as follows:

| Definition's clause | Contract |
| --- | --- |
| omitted | Infer `E` from the body. |
| `causes X` | State `X` and add `E`. |
| `causes only X` | State `X` and require every effect in `E` to be held by `X`. |

A stated `WriteTxn(stock)` executes no assignment of its own. It counts as a write for transaction
footprints and `await_final` dependencies even when the body makes no assignment
([Discharging requirements and effects](#discharging-requirements-and-effects)).

#### Discharging requirements and effects

| Construct | Discharges |
| --- | --- |
| `with begin():` | `Transaction`, in its body |
| `try` with `except T` | each `Raise(S)` with `S` a subtype of `T`, in its `try` block |
| the end of a scope | `Write(x)`, `Append(x)` and `Read(x)` for a variable `x` it binds, under the rules below |

- **A scope ends the history of each variable it binds.** A scope is a `def` body, a loop body, a
  block, or a module's top level. At its end, `Write(x)`, `Append(x)` and `Read(x)` for each `x`
  the scope binds are dropped: every write to `x` stands inside the scope, so nothing outside it
  observes one, and every call inside the scope has a position in `x`'s history to read at.
- **Transactional state belongs to the run.** A transactional mutable variable is declared at a
  module's top level, and declaring one in a `def` body, a loop or a block is an error. Its history
  grows as transactions commit after the top level has run, so no scope ends it: a read of `x`
  requires `Transaction` and `ReadTxn(x)`, a write requires `Transaction` and causes `WriteTxn(x)`,
  and no construct discharges `ReadTxn(x)` or `WriteTxn(x)`.
- **A block's transactional capabilities are its footprint.** The `ReadTxn(x)` and `WriteTxn(x)`
  of a `with begin():` block's body name the variables the block reads and writes, which decide
  the blocks it commits in an order with ([8.5 Ordering and
  concurrency](#85-ordering-and-concurrency)) and the blocks an `await_final` waits for
  ([8.6 `await_final`](#86-await_final)). A body holds no `RunTransaction`, so its capabilities are
  one block's, while a function's clause holds those of every block it runs. A written clause
  counts as the body does: a call of a function whose clause states `WriteTxn(x)` writes `x` for
  these rules whether or not its body does, and one whose clause holds a top writes every variable
  the top holds.
- **A public feed belongs to the run too.** A feed is the run's when other modules may append to
  it: a public feed, or a private one that a public function appends to. No scope's end drops
  `Append` of it.
- **A `Mut` or `Feed` parameter's reads and writes are the caller's.** A call passing `a` to a `Mut`
  parameter requires `Read(a)` and causes `Write(a)`, or `ReadTxn(a)` and `WriteTxn(a)` for a
  transactional `a`, and one passing `a` to a `Feed` parameter causes `Append(a)`, whether or not
  the callee reads or writes it. The callee's reads and writes of its own `Mut` or `Feed` parameter
  are not in its type, since the parameter's type states them.
- **Nothing that leaves a scope names a variable whose history the scope ends.** A scope drops the
  capabilities of a variable `x` it binds only where nothing it hands outward names `x`: no function
  in the type of its result, of an exception it raises out of the scope, or of a value it writes or
  appends to a variable bound outside it, requires `Read(x)` or causes `Write(x)` or `Append(x)`. No scope ends a transactional variable's
  history, so `ReadTxn(x)` and `WriteTxn(x)` leave any scope. A top holding writes or reads of
  induction variables, such as `Effect`, `Context` or `Write(*)`, names every one, and one holding
  appends every feed, since it holds their capabilities, so a function whose type holds one leaves
  no scope that binds what it names; one of type
  `Int => Int causes Effect except (Write(*), Append(*))` names none. A result, an exception, a
  write or an append that hands out such a function is an error there. At a module's top level a public
  member is what leaves, and this rule is
  [9.10 Induction variables stay in their module](#910-induction-variables-stay-in-their-module).
- **Nothing that leaves a block or a function names its transaction.** A function value whose
  body names `txn`, a block's transaction named by `with txn = begin():` or a caller's named by
  `requires txn: Transaction`, needs that transaction, which only that block or that call
  supplies. A result, an exception, a write or an append that hands such a function out of the
  block, or out of the function whose requirement names `txn`, is an error there, as one that hands
  out a function naming a variable whose history the scope ends is. **[Decided]**
- **Another module writes a run's state through the run.** A module calling `inv::reserve`, which
  writes `inv`'s private `stock`, cannot write `WriteTxn(inv::stock)`, though its diagnostics print
  it. It writes `WriteTxn(inv::*)`, `inv`'s top, which loses only what it cannot name. A public
  variable is named as it is reached, `WriteTxn(inv::stock)` for `pub stock`
  ([9.5 Visibility](#95-visibility)). A Module type's entry writes the private state of the module
  it describes as `Module::*`, so
  `Module{reserve: Int => {} causes WriteTxn(Module::*), RunTransaction}` is met by a run whose
  `reserve` commits a write to its own state, and a call through a parameter `counter` of that type
  causes `WriteTxn(counter::*)`: the state of the run the parameter takes, which stays abstract
  where the module is checked on its own. The interface `cambra check` prints writes a module's own
  private state as `Module::*` too
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)). `Module::*` stands only
  in a Module type and in that interface, and `inv::*` names a run or a Module-typed parameter.
- **The run supplies `ObserveWorld` and `ReadTxn(x)`,** at every position. No construct in a module
  discharges either, so a top level that requires one is run
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)).
- **`RunTransaction` and `AffectWorld` are never discharged.** A `with begin():` block whose body
  causes `RunTransaction`, or a top holding it, is a nested transaction
  ([8.2 Transactions: `with begin():`](#82-transactions-with-begin)).
- **A construct discharges from `Context` and `Effect` what it discharges from its items.** A
  `with begin():` block around a call requiring `Context` requires `Context except Transaction`.
- **A function value's requirements are supplied at each call.** A lambda that requires
  `Transaction` reads the transaction of the block it is called in, not the block it was made in.

#### Inputs from outside the program

`ObserveWorld` is the requirement of every input from outside the program:

- **Opening a source requires `ObserveWorld`** ([7.3 Sources](#73-sources)). The source's elements
  are values, so a function that reads a captured source requires nothing further.
- **A reading requires `ObserveWorld`.** A reading is a call whose value comes from outside the
  program: the clock, a random value, or the reply to a call made outside the program. Its function
  is a `@Builtin` function a std module declares with `requires ObserveWorld`, whose value the
  compiler supplies ([9.16 The std root](#916-the-std-root)), or a function that calls one:
  `time::now()` reads the clock through `std::time`'s `clock`
  ([7.5 Time [Decided]](#75-time-decided)).

The run supplies `ObserveWorld` at every position, and no construct in a module supplies it. A top
level that requires it is therefore run, not imported ([9.7 Importing asserts a shareable
module](#97-importing-asserts-a-shareable-module)), and no constant reads one ([9.19
Constants](#919-constants)). `ObserveWorld` has no parts: no construct supplies one kind of input
without the others.

The **position** of an evaluation is the run's start at the top level, extended by one iteration
for each loop around the evaluation. A **call path** is the sequence of call sites, outermost first,
through which an evaluation reaches an operation. Every call, a call of a function value included,
is resolved when the program is compiled, so each call path is fixed.

- **A reading has one value at each position and call path.** Two calls at one position may return
  different values, two clock readings included, and one call evaluated again at its position
  returns its value again. Every reading is keyed this way: the clock, a random value and the reply
  to a call made outside the program differ only in where the value comes from.
- **The run records each reading** the first time its key is evaluated and returns the recorded
  value at every later evaluation, so a retried transaction reads what the first evaluation read.
- **A reading has a fixed history,** as a mutable variable does: an evaluation that reaches its
  position and call path again reads the value it took there. The run keeps a reading only while
  an evaluation can still reach its key: a transaction that may be retried, or a call that a reload
  or a restart after a crash continues ([8.8 `@LoadFrom`](#88-loadfrom),
  [9.18 Reloading a program of modules](#918-reloading-a-program-of-modules)). So
  `t = time::now()` at a module's top level keeps its instant across both, as
  `t: Mut(time::Instant) := time::now()` does. A reload keeps the readings of each call of the new
  version that continues a call of the old one, and a call that continues none takes new readings.
  A reload whose new version would evaluate a reading at a past position the run keeps no reading
  for fails the compatibility check. Which call continues which is **[Open]**.

#### Output outside the program

`AffectWorld` is the effect of every output outside the program. A **sink** is an operation that
hands data out: binding a feed to a sink, as `http_serve` binds its responses ([7.3
Sources](#73-sources)), or calling a sink function, which takes a collection and writes it out. Each
causes `AffectWorld`. A call that sends a request out and returns the reply causes `AffectWorld` and
requires `ObserveWorld`.

No construct discharges `AffectWorld`. An output inside a `with begin():` block is sent only if the
block commits ([8.4 Feeds are the second form of
mutability](#84-feeds-are-the-second-form-of-mutability)).

#### Exceptions

```ebnf
raise_stmt  ::= "raise" expression
try_stmt    ::= "try" ":" block ( "except" expression [ "as" ident ] ":" block )+
```

An **exception** is a value a `raise` raises. Its type is the parameter of the
`Raise` effect it causes, so `Raise(Negative)` and `Raise(Timeout)` are two effects:

```python
type Negative = {qty: Int}

def checked(qty):
    if qty < 0:
        raise Negative::new((qty=qty))
    qty

def checked_or_zero(qty):
    try:
        checked(qty)
    except Negative:
        0
```

- **`raise e` causes `Raise(E)`,** where `E` is the type of `e`, so `raise 2` causes
  `Raise(Int@2)`. `raise` is a statement.
- **Every type is raised.** `E` is any type, a collection, a function and a type parameter among
  them, and `Raise` in a `causes` clause, and an `except` clause, take any type. **[Planned]** — an
  exception whose type holds a function, a `Mut` or a `Feed`.
- **`Raise` is covariant.** An exception is an output, so a function that may raise an `Int@2` may
  raise an `Int`: `Raise(Int@2)` is a subtype of `Raise(Int)`
  ([Writing requirements and effects](#writing-requirements-and-effects)).
- **A path that raises contributes no value.** An `if` arm, a `match` arm or a branch of a function
  body that raises is left out of the join
  ([Joining the types of several values](#joining-the-types-of-several-values)).
- **An exception ends its path.** The statements after a statement that raises run only on the path
  where it did not raise. The statements before it are unaffected, and their outputs stand.
- **Within an expression, the first exception in written order escapes.** An argument or operand
  that causes anything is evaluated only where none of the arguments or operands written before it
  raised, so in `f(a) + g(b)`, where both calls may raise, `g(b)` runs only if `f(a)` did not raise.
  This is the written order of one evaluation ([8.5 Ordering and
  concurrency](#85-ordering-and-concurrency)), which leaves an operand that causes nothing
  unordered.
- **A call causes each `Raise(E)` its callee causes** and does not catch.
- **An exception is an output.** An expression that may raise raises whether its value is used or
  not, and a statement whose only effect is an exception is not inert
  ([4.9 Expression statement](#49-expression-statement)).
- **`try` catches by type.** `except T` catches each `Raise(S)` its `try` block causes with `S` a
  subtype of `T`. Where the block raises such an exception, the first clause catching it runs, with
  the exception bound to the name after `as` at type `T`, and its value is the statement's. The
  statement causes what its `try` block causes, less what its clauses catch, and what its clauses'
  blocks cause. In value position its type is the join of its blocks' values, as an `if`'s is. A
  clause that catches nothing its `try` block causes is an error.
- **A clause takes an exception type whole or not at all.** For each `Raise(S)` a `try` block
  causes, the first clause `except T` whose `T` does not exclude `S` covers it, `S <: T`, and a
  clause that would catch some exceptions of type `S` and not others is an error. To tell such
  exceptions apart, catch a type covering `S` and test the value in the clause, raising it again
  where it should go on. Two types **exclude** each other by these rules alone, and any other two
  overlap:
  - Two different base types, two nominal types of different declarations, and two types of
    different kinds among base types, tuples, records, variants, nominal types and functions, a
    collection being a function.
  - Two tuples of different widths ([Tuple width](#tuple-width)), and two tuples with a position,
    or two records with a field, whose types exclude each other. Two records with no field in
    common overlap, since a record with both fields has both types.
  - Two variants whose tags in common, if any, carry payloads of types that exclude each other.
  - Two refinements of one base type whose predicates no value satisfies together, such as
    `Int@2` and `{Int where _ > 5}`.
- **Catching is decided by type, not by value.** `except {Int where _ > 0}` catches `raise 2`,
  whose type is `Int@2`. Around `raise n` with `n: Int` it is an error, whatever value `n` holds,
  since it takes part of `Int`. A raise is seen at its own type or a supertype of it, and a type
  below one a clause covers is covered too, as one below one it excludes is excluded, so the
  type a call is seen at never changes which clause catches what it raises.
- **A type parameter is caught by itself.** `except A` catches `raise x` with `x: A` whatever type
  a use instantiates `A` at. A parameter overlaps every type, so around `raise x` a clause whose
  type `A` is not a subtype of takes `A` in part: `except Int` there is an error.
- **A `try` around a top holding `Raise(*)` catches nothing.** `Raise(*)`, and `Effect` that does
  not take it away, hold a `Raise(S)` for every type `S`, and each clause takes some of those in
  part, so an `except` clause whose `try` block causes such a top is an error. A function whose
  exceptions a caller catches states them, as `causes Raise(NotFound), Effect except Raise(*)`
  does.
- **An exception escaping a `with begin():` block aborts the transaction.** None of the block's
  writes commits and no output inside it is sent, and the exception continues outward. An exception
  caught inside the block does not abort it.
- **An exception escaping an iteration orders the iterations.** A `for` loop, or a comprehension
  whose element or condition may raise, raises the exception of its first raising iteration in
  position order, and nothing after that iteration takes effect. This is a dependency from one
  iteration to the next, as an accumulator's is ([4.6 `for` — iteration](#46-for--iteration)). The
  loop is ordered, so its source's positions must be orderable
  ([Ordered loops](#ordered-loops)); over positions with no order, the loop or comprehension catches
  inside its body. Whether this rule stands is **[Open]** until partiality is decided
  ([Partiality is not yet defined [Open]](#partiality-is-not-yet-defined-open)): were division by
  zero or a missing key to raise, most loops would be ordered and so run one iteration at a time.
- **No exception escapes the program.** An exception that a module's top level causes is an error
  at the statement it escapes from, with a secondary label at the `raise`.
- **Catching is resolved when the program is compiled.** A function that causes `Raise(E)` returns
  its result or an `E`, and each caller passes the `E` on or catches it. No handler is looked up at
  run time ([8.7 Transactions as contextual
  parameters](#87-transactions-as-contextual-parameters)).

**[Open] — partial operations.** Whether division by zero, a missing key or an out-of-range index
raises an exception is part of
[Partiality is not yet defined [Open]](#partiality-is-not-yet-defined-open).

**[Open] — crash handling.** What a program does when an operation outside it fails at run time,
and in particular whether the dataflow downstream of the failure pauses, is undecided.

#### Effects in traits

- **A trait's signature is a written type.** A `def` line in a trait with no clause requires
  nothing beyond its trait requirements and causes nothing.
- **The signature is every instance's contract.** An instance's function writes no clause of its
  own, its body causes nothing beyond what the signature states, and every call of it, through a
  summon or a requirement, sees the signature ([Declaring an instance](#declaring-an-instance)).
- **A trait's signature names no variable.** An instance may be declared in another module than the
  trait, so `Write(x)`, `WriteTxn(x)`, `Append(f)`, `Read(x)` and `ReadTxn(x)` in a signature are
  errors, while the tops, such as `WriteTxn(*)`, which name none, may be stated; what an instance's
  functions cause beyond the signature is an associated type's. An instance's function reaches no
  variable of its module
  ([Traits and instances across modules [Decided]](#traits-and-instances-across-modules-decided)),
  so the state it writes is a `Mut` or `Feed` parameter's, which the caller passes
  ([Declaring a trait](#declaring-a-trait)).
- **A trait's signature has no hole.** `_` in a signature's clauses, or in the clauses of a
  function type in it, is an error: inference fills a hole at each call, so what an instance does
  would reach no call's type. A signature polymorphic in what an argument does names a bounded
  variable instead, of the trait or of the function. **[Planned]** — a trait function's bounded
  type parameter, `def app(E <: Effect, …)`.
- **An associated type lets instances differ.** `Name <: Effect` in a trait declares an associated
  type that a `causes` clause names, and `Name <: Context` one that a `requires` clause names:

  ```python
  trait Sink(T):
      Writes <: Effect
      def put(t: T, v: String) causes Writes
  ```

  An instance writes no definition of such a type: it is what the instance's functions cause, or
  require, beyond what their signatures list otherwise. A bound may end in `except` as a clause
  variable's does ([Kinds and bounds](#kinds-and-bounds)): under
  `Writes <: Effect except RunTransaction`, no instance's function commits beyond what its signature
  lists. Under `requires s: Sink(T)`, `s::Writes` is the clause of the instance each call passes,
  and a call of `s::put` causes it.

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
  annotation, or in the bound of a determined type parameter, or it is the associated type of a
  requirement whose other positions are determined
  ([Trait requirements](#trait-requirements)). Any other type parameter is an
  error at the definition. In `def stamp(B, T <: {at: B}, a: T) => {B, T}`, `a` determines `T`
  and `T`'s bound determines `B`.

  > **Direction [Decided] — determined by the use.** A type parameter may instead appear only in
  > the result, and each use determines it from the type the use requires. `Map::empty` has type
  > `forall (K, V) Map(K, V)`, so `m: Map(String, Int) = Map::empty` determines `K` and `V`, and
  > `Option::none` is the same case
  > ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). A use that
  > determines none is an unresolved-type error at the use, as an unannotated `empty_map()` is
  > today ([3.11 List, tuple, record literals](#311-list-tuple-record-literals)).
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
  `T: SubtypesOf(U)`. An open tuple `U` is not itself among them, no value having its type
  ([Tuple width](#tuple-width)).
- `K => Type` is every family over the values of `K`, a type for each value. `=>` is the kind
  arrow and `K` is a type. A parameter of this kind is a family parameter, declared in a type
  declaration's, a `def`'s or a `forall`'s parameter list
  ([Family parameters](#family-parameters)).

A clause variable of [6.9 Capabilities](#69-capabilities) is written in the bound form, though a
clause is not a type: `E <: Effect` ranges over `causes` clauses and `R <: Context` over `requires`
clauses. A bound may end in `except` as a clause does: `E <: Effect except RunTransaction` ranges
over the `causes` clauses without `RunTransaction`, so a function passed as
`f: (Int => Int causes E)`
does not commit, and each use is checked against it.

Any other kind, such as a listing `T: [Int, String]`, is **[Open]** and an error.

**Case decides what a binder binds, and its annotation agrees.** A capitalized name binds a type
and a lowercase name a value
([6.1 Direction: term/type syntax split [Decided]](#61-direction-termtype-syntax-split-decided)).
In a parameter or binder list, the name before `:` is the variable bound, and its annotation is a
kind for a type and a type for a value: `V: K => Type` is a type parameter whose kind is
`K => Type`, and `k: K` in `forall (k: K)` binds a value of `K`
([Family parameters](#family-parameters)). A type written as a kind, `T: Int`, and a kind written
as a value's type, `t: Type`, are errors.

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
requirement     ::= [ ident ":" ] trait_type | ident "::" Ident "<:" expression
                 | "OrderableFor" "(" expression "," effect_clause ")"   (* [Decided] *)
effect_clause   ::= "nothing" | causes_item ( "," causes_item )* [ except_causes ]
trait_type      ::= trait_name [ "(" expression ( "," expression )* ")" ]
trait_name      ::= ( ident "::" )* Ident   (* a qualified name is [Decided] *)
```

A **trait** is a type whose values are **instances**. `Area(Circle)` is the type of an instance that
gives `Circle` the functions `Area` declares, and a trait with operands is a family of such types,
one for each list of operand types. A **trait requirement** in a definition's `requires` clause is a
parameter of such a type that no call writes: each call passes the instance its types pick
([Summoning an instance](#summoning-an-instance)). Each operator places a requirement on its
operand types. A module declares traits of its own ([Declaring a trait](#declaring-a-trait)), and a
trait requirement names one as it names these, which are built in:

| Trait | Required by | Operands | Associated type | Function | Satisfied by |
| --- | --- | --- | --- | --- | --- |
| `Addable` | `+` | 2 | `Output` | `add` | `Int`, `UInt`, `String` |
| `Subtractable` | `-` | 2 | `Output` | `sub` | `Int`, `UInt` |
| `Multipliable` | `*` | 2 | `Output` | `mul` | `Int`, `UInt` |
| `Divisible` | `//` | 2 | `Output` | `div` | `Int`, `UInt` |
| `Exponentiable` | `**` | 2 | `Output` | `pow` | `Int`, `UInt` |
| `Negatable` | unary `-` | 1 | `Output` | `neg` | `Int` |
| `Equatable` | `==`, `!=`, `in`, `not in` | 2 | none | none | `Int`, `UInt`, `String`, `Bool`, and a tuple or record whose fields are `Equatable` |
| `Orderable` | `<`, `<=`, `>`, `>=`, `max`, `min` | 2 | none | none | `Int`, `UInt`, `String`, `Bool`, and a tuple whose components are `Orderable` |
| `Iterable` | `for`-in, a comprehension's `for` clause | 1 | `Elements` | `elements` | every collection, as its own `Elements` |

`max` and `min` place `Orderable(T, T)` on their element type `T`. A binary trait is satisfied by
two operands of one listed type. A tuple or record satisfies `Equatable` only against the same
product, and a tuple satisfies `Orderable` only against a tuple of the same length
([3.4 Comparisons](#34-comparisons)). A listed instance's `Output` is its operand type, so the sum
of two `Int`s is an `Int`. A nominal type satisfies these traits where its module declares an
instance ([Equality and order](#equality-and-order)).

- **An operator calls its trait's function.** `a + b` is `summon(Addable(_, _))::add(a, b)`, and
  `-a` is `summon(Negatable(_))::neg(a)`. The compiler's instances run the built-in operation:
  `add` of two strings joins them.
- **A comparison calls no function.** `Equatable` and `Orderable` compare values by value
  ([Equality and order](#equality-and-order)), so an instance of either defines nothing.
- **A loop calls `Iterable`'s `elements`.** `for x in c` walks `summon(Iterable(_))::elements(c)`
  and binds `x` to each of its values ([4.6 `for` — iteration](#46-for--iteration)). A collection is its own
  `Elements`, and `elements` returns it. An instance defines it for a nominal type:
  `instance Iterable(Bag)` with `Elements = List(Int)` and `def elements(b): b.extract()`. An
  instance's `Elements` is a structural collection: a nominal `Elements` is an error at the
  instance.

- **A named requirement binds its instance.** In `def total(S, s: S) => Int requires a: Area(S)`,
  `a` is the instance each call passes, and `a::area(s)` calls its `area`
  ([Summoning an instance](#summoning-an-instance)). A requirement without a name passes an
  instance too, which the body reaches with `summon`.
- **A named requirement's associated types are types.** Under `requires a: Addable(A, B)`,
  `a::Output` is `Addable`'s `Output` at `A` and `B`, the type of `a + b`, and the signature and
  the body may write it: `def add(A, B, x: A, y: B) => a::Output requires a: Addable(A, B)`. Each
  call's types decide it.
- **A clause bounds an associated type it names.** `a::Output <: T`, written in the clause after
  the requirement that names `a`, states that the instance's `Output` is below `T`, so `a + b`
  under `requires a: Addable(T, T), a::Output <: T` is a `T`. A call whose instance's `Output` is
  not below `T` is rejected at the call. A bound no instance's associated type meets is an error
  at the bound.
- **A trait's bound holds of its associated type in every requirement.** Where the trait declares
  one with a bound ([Declaring a trait](#declaring-a-trait)), a requirement's associated type is
  below that bound at the requirement's operands, unless the clause bounds it itself. A
  requirement with no name has it too, so under `requires Iterable(C)`, `C`'s collection is some
  collection of some type, and a loop over a `C` types. A hole in a bound, the trait's or the
  clause's, is a type parameter of the definition, and one in a requirement under `forall (k: K)`
  is a family parameter of it, a type for each `k` ([Family parameters](#family-parameters)).
  Under
  `requires i: Iterable(C), i::Elements <: _ |=> T`, `C`'s collection has values of type `T`,
  whatever its domain.

  ```python
  def largest(C, T, c: C) => T requires i: Iterable(C), i::Elements <: _ |=> T, Orderable(T, T):
      max([x for x in c])
  ```
- **A requirement's arguments are any types.** `Equatable` reads a product componentwise, as `==`
  does ([3.4 Comparisons](#34-comparisons)), so `requires Equatable({T, U}, {T, U})` also states
  `Equatable(T, T)` and `Equatable(U, U)`. `requires Describe(Two(T))` states `Describe` of the
  nominal type `Two(T)`, which a definition needs where the instances are at particular arguments,
  as `instance Describe(Two(Int))` is ([Declaring an instance](#declaring-an-instance)).
- **A requirement no instance can satisfy is an error at the requirement.**
  `requires Orderable(List(T), List(T))` is rejected where it is written: no `List` is `Orderable`,
  so no call could satisfy it.
- **A requirement on types without type parameters states nothing about a parameter.** It must be
  satisfiable, and it has no other effect than the associated types it names.
- **One clause holds every requirement.** `Transaction`
  ([8.7 Transactions as contextual parameters](#87-transactions-as-contextual-parameters))
  is written in the same clause: `requires Transaction, Orderable(T, T)` (**[Decided]**).
- **The body uses only what the clause states.** An operator whose operand type involves a type
  parameter is an error unless a requirement or the parameter's bound covers it. Where both do, the
  requirement decides: `x + y` under `T <: Int` and `requires a: Addable(T, T), a::Output <: T` is
  an `a::Output`, which is a `T`.
- **Context requirements stand in the clause too.** `Transaction`, `ObserveWorld`,
  `ReadTxn(x)` and `Read(x)`, a written clause as a lower bound, and `only` and `nothing`, are
  specified in [Writing requirements and effects](#writing-requirements-and-effects).
- **Each call satisfies each requirement at its own instantiation,** and passes the instance that
  satisfies it. A call that does not is rejected at the call. A secondary label at the requirement
  is **[Decided]**.

> **Direction [Decided] — collection types.** `Set`, `Map` and `FullMap` satisfy `Iterable`
> through instances the compiler provides
> ([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)). Each
> instance's `Elements` yields what [4.6 `for` — iteration](#46-for--iteration) lists for its
> type.

> **Direction [Open] — a nominal `Elements`.** An instance's `Elements` may be a nominal type
> with an `Iterable` instance of its own, and a loop walks through instances until it reaches a
> structural collection:
>
> ```python
> trait Iterable(C) requires it: Iterable(Elements):
>     Elements
>     Walked                      # the compiler's: it::Walked, or C under the collection rule
>     def elements(c: C) => Walked
> ```
>
> - An instance writes `Elements` and an `elements` that returns an `Elements`, one step. The
>   compiler composes it with `it::elements`, so a loop's one `elements` call reaches a
>   structural collection, and instance search does the recursion.
> - The collection rule is the only base case. A structural collection is its own `Elements` and
>   its own `Walked`, and it is exempt from the trait's requirement, which would otherwise require
>   `Iterable(C)` of itself.
> - The requirement is the trait's, not `elements`'s, so `it` is in scope for `Walked`.
> - A trait that requires itself, an associated type the trait defines
>   ([Declaring a trait](#declaring-a-trait)), and the base-case exemption are each the
>   compiler's alone; a declared trait has none of them.
> - The walk terminates by a check where an instance is declared. A chain with no type variables
>   is followed there, and a cycle (`Bag` to `Wrap` to `Bag`) is rejected. A generic instance's
>   `Elements` is strictly smaller than its head: `Wrap(T)` with `Elements = T`.

#### Summoning an instance

```ebnf
summon_expr ::= "summon" "(" trait_type ")"
member      ::= ( summon_expr | ident ) "::" ident
```

`summon(T)` is the instance of the trait type `T` that is visible where it is written, and `i::f` is
the function `f` of the instance `i`:

```python
c = Circle::new(2)
summon(Area(Circle))::area(c)    # 12
summon(Area(_))::area(c)         # the hole is inferred: the instance of `Area(Circle)`

def total(S, s: S) => Int requires a: Area(S):
    a::area(s)
```

- **A trait's functions are read from an instance.** No name reaches one through its trait:
  `Area::area(c)` is an error. `i::f` without arguments is the function as a value.
- **A hole in `T` is inferred,** as a hole in an annotation is. `summon(Area(_))::area(c)` finds
  `Area(Circle)` from the type of `c`.
- **The visible instances** are the requirements of the definitions a `summon` stands in, named or
  not, and every instance the program declares ([Declaring an instance](#declaring-an-instance)).
  Each call passes a requirement the instance the program declares for the call's types, so the
  visible instances that answer one `T` are one instance. **[Open]** — which instance a summon
  names where visible instances differ, as one installed in a scope would, and a scope that
  requires that no instance of a trait is visible.
- **A summon places its requirement on the definition it stands in,** as an operator places its
  trait's, whether the clause states it or not: `def total(s): summon(Area(_))::area(s)` requires
  `Area(S)` of its parameter's type `S`.
- **Which instance a summon names is decided when the program is compiled,** at each
  specialization of the definitions it stands in, so a call of an instance's function runs a
  function the compiler knows. What is decided is which instance a summon stands for, not a value:
  an instance installed in a scope may hold a value only the running program has, as a
  transaction does
  ([8.7 Transactions as contextual parameters](#87-transactions-as-contextual-parameters)).
- **An instance stands only before `::`.** `summon(T)` and a requirement's name are qualifiers.
  Binding an instance to a name, passing one to a function, and holding one in data are
  **[Open]**.
- **A requirement's name is a qualifier in the body.** `a::f` reads the instance `a` where a
  requirement binds `a`, which shadows a module of that name there, and `a::Elem` its associated
  type ([Trait requirements](#trait-requirements)). Reading an associated type through
  `summon(T)` is **[Open]**.

> **Direction [Decided] — an instance is a module.** A trait is a nominal Module type
> ([9.8 Module types](#98-module-types)) whose operands are fixed type members, and an instance is
> a module with no state whose members are its functions, read with `::` as a module's members are.
> A generic instance, `instance forall (T) Area(Two(T)) requires a: Area(T)`, is a module that takes
> types and instances as arguments. Its instance at particular arguments is shared, as an import
> with particular arguments reaches one shared run ([9.2 Imports](#92-imports)), rather than made
> afresh for each use, as a run is. `requires Transaction`
> ([8.7 Transactions as contextual parameters](#87-transactions-as-contextual-parameters))
> is a requirement of this kind, whose instance a `with begin():` block installs for its body
> rather than for the whole program. **[Open]**: passing an instance at a call explicitly, and
> installing an existing module as an instance of a trait.

#### Declaring a trait

```ebnf
trait_stmt  ::= "trait" Ident "(" Ident ( "," Ident )* [ "," ] ")" [ requires_clause ] ":"
                NEWLINE INDENT trait_item+ DEDENT
trait_item  ::= Ident [ "<:" expression ] NEWLINE
             |  "def" ident "(" params ")" "=>" expression [ requires_clause ]
                [ causes_clause ] NEWLINE
```

A `trait` declaration binds a capitalized name to a new trait over its **operands**, the types it
names in parentheses: one instance type for each list of operand types. Its body declares
**associated types**, each a capitalized name, alone, `Elem`, or bounded, `Size <: Int`, and
**functions**, each a `def` line with a signature and no body. Every instance holds each function at
its own operands and defines each associated type, except one bounded by `Effect` or `Context`,
which stands for a clause its functions decide ([Effects in traits](#effects-in-traits)). An
associated type is an alias the instance defines, not a nominal type, so no `type` keyword
introduces it.

```python
trait Area(S):
    def area(s: S) => Int
    def scaled(s: S, k: Int) => S

trait Container(C):
    Elem
    def first(c: C, otherwise: Elem) => Elem
    def tag(R, c: C, label: R) => {R, Elem}

trait Scales(V, F):
    def scale(v: V, f: F) => V
    def scale_vec(f: F, v: V) => V
```

- **A signature states every type.** Each parameter is annotated and the result is written. The
  operands and associated types are types in every signature. A function may declare type parameters
  of its own, as `tag` declares `R`, and a `requires` clause; each call opens the parameters at its
  own types and satisfies the clause there. A signature is a written type, so one without a `causes`
  clause causes nothing, and an associated type `Name <: Effect` lets instances cause different
  effects ([Effects in traits](#effects-in-traits)).
- **A parameter may be pass-by-reference.** `Mut(V)`, `Mut(V, Txn)` and `Feed(V)` state a
  parameter as they do on a `def` ([6.2 Non-purity as type
  wrappers](#62-non-purity-as-type-wrappers)): the caller's variable or feed is the argument, and an
  instance's function writes it. A signature states them nowhere else, neither nested in a type nor
  as the result. An instance's function takes the signature's parameter without restating it, and a
  call through a summon or a requirement passes the variable or feed as a `def`'s call does:

  ```python
  trait Take(T):
      def take(t: T, s: Mut(Int, Txn), n: Int) => Int

  instance Take(Box):
      def take(t, s, n):
          with begin():
              s := s - n
          n
  ```

- **A trait's function is no method.** No parameter of one is named `self`, in the trait or in an
  instance, and a call reads it from an instance: `summon(Scales(_, _))::scale_vec(2, v)`, not
  `2.scale_vec(v)` ([Associated functions and methods](#associated-functions-and-methods)).
- **A function may declare no parameters** (**[Decided]**). A call reads it from an instance like
  any trait function: `summon(One(Circle))::one()` ([3.8 Function calls](#38-function-calls)).
- **Neither the trait's name nor a type's reaches a function.** `Area::area(c)` is an error, and
  `Circle::area(c)` names only a function `Circle` declares
  ([Summoning an instance](#summoning-an-instance)).
- **[Open] — default functions.** A trait function with a body, which an instance that leaves it
  out would take, is not part of the language: every instance defines each of its trait's
  functions.
- **A trait's names are types.** The trait's name, its operands and its associated types are
  capitalized, and none is a type the module declares or a built-in name. A trait is declared at a
  module's top level, and its signatures name the traits declared above it.
- **A requirement names a declared trait as it names a built-in one.** `requires Area(S)` states
  that `S` has an instance of `Area`, and under `requires c: Container(C)`, `c::Elem` is the `Elem`
  of `C`'s ([Trait requirements](#trait-requirements)).
- **[Open] — an associated type the trait defines.** `Elem = Int` in a trait, which every instance
  would take, is not part of the language, as a default function is not: every instance defines
  each of its trait's associated types.
- **An associated type may be bounded.** `Size <: Int` states that every instance's choice of the
  type is below `Int`, and may name the trait's operands and its other associated types. An
  `instance Measured(Box2)` whose block defines `Size = String` is an error at the `instance`. A
  hole in the bound is any type, chosen afresh at each use: `Iterable`'s `Elements` is bounded
  `<: _ |=> _`, every collection.
- **A trait may require traits of its types.** `trait Ranked(A, B) requires s: Same(A, B):` states
  that every instance of `Ranked` is at types `Same` holds of: an instance whose types `Same` does
  not hold of, by the instances declared above it and its own `requires` clause, is an error. Each
  instance's functions see that instance of `Same`, as `s::same` here.
- **A requirement is not transitive.** `requires r: Ranked(T, T)` states nothing of `Same(T, T)`:
  under it, `summon(Same(T, T))` and `r::s` are errors, and a definition that calls `Same`'s
  functions requires `Same(T, T)` as well. An instance shows only its own trait's functions, so two
  traits a trait requires may declare functions of one name.

#### Declaring an instance

```ebnf
instance_stmt ::= "instance" [ "forall" "(" Ident ( "," Ident )* [ "," ] ")" ]
                  trait_name "(" expression ( "," expression )* ")" [ requires_clause ]
                  ( ":" NEWLINE INDENT instance_item+ DEDENT | NEWLINE )
instance_item ::= Ident "=" expression NEWLINE | def_stmt
```

An `instance` block declares an **instance** of the trait its head names and installs it for the
whole program: the types it is for, a definition of each of the trait's associated types, and a
definition of each of the trait's functions.

```python
type Circle = Int
type Two(T) = {T, T}

instance Area(Circle):
    def area(s) => Int:
        3 * s.extract() * s.extract()
    def scaled(s, k):
        Circle::new(s.extract() * k)

instance forall (T) Container(Two(T)):
    Elem = T
    def first(c, otherwise):
        c.extract().0
    def tag(c, label):
        (label, c.extract().0)

instance forall (T) Area(Two(T)) requires a: Area(T):
    def area(s):
        a::area(s.extract().0) + a::area(s.extract().1)
    def scaled(s, k):
        Two::new((a::scaled(s.extract().0, k), a::scaled(s.extract().1, k)))
```

- **An instance is for a nominal type.** Each operand of the head is a **pattern**: a type
  variable, a base type, or a nominal type applied to patterns in turn, as in `Two(T)`, `Two(Int)`
  and `Duo(Two(Int), B)`. At least one operand is a nominal type, and the instance is declared in
  its trait's module or in the module of a nominal type its head names
  ([Traits and instances across modules [Decided]](#traits-and-instances-across-modules-decided)).
- **`forall` declares the head's type variables.** `instance forall (T) Area(Two(T))` declares `T`;
  a capitalized name in the head that names no type and is not declared is an error. A type variable
  stands for any type, one type wherever the head names it, appears in an operand, and is a type
  parameter of every function in the block. A variable standing as a whole operand, `F` in
  `instance forall (F) Scales(Vec2, F)`, accepts any type there.
- **The block defines every associated type,** once each, as a type alias is written, `Elem = T`,
  over the head's variables. The head names only the operands, as a requirement does.
- **A `requires` clause makes the instance conditional.**
  `instance forall (T) Area(Two(T)) requires a: Area(T)` answers `Area(Two(X))` only where `Area(X)`
  holds, and its functions reach the instance that holds it as `a`.
- **Resolving an instance's conditions ends.** A type's depth is how deeply it nests, a type
  variable counting 0: `Int` and `T` have depth 0, `Two(T)` 1, `Two(Two(T))` 2. Each condition is
  no deeper than the head: its depth is at most the head's, and each type variable stands in it no
  deeper than at its deepest place in the head. A condition on the instance's own trait, or on a
  trait not declared before it, is shallower: both comparisons are strict.
  `instance forall (T) Area(Two(T)) requires Area(T)` is accepted, and `requires Area(Two(T))` is an
  error. A variable may stand in a condition more often than in the head, as `T` does in
  `instance forall (T) Same(Two(T)) requires Equatable(T, T)`. The compiler's traits are declared
  before a module's, a module's traits in the order it writes them, and an imported module's
  before the importing module's; traits of two modules neither of which imports the other are not
  ordered. A chain of conditions therefore either names an earlier trait or a shallower type at
  each step that keeps its trait or names a later one, so it ends.
- **The block defines each of the trait's functions, and nothing else.** A `def` in it is the
  trait's function at the instance's types. A parameter it leaves unannotated, its result, its own
  type parameters and its `requires` clause are the trait's there, and one it writes must be the
  trait's. It writes no `causes` clause and no context requirement: it requires and causes what the
  trait's signature states, and its body causes nothing beyond that
  ([Effects in traits](#effects-in-traits)). A `def` names no type of its own, and `pub` does not
  mark one.
- **No two instances of a trait accept one type.** Two instances overlap when some types match both
  heads, as `Two(T)` and `Two(Int)` do, and `Duo(Int, B)` and `Duo(A, String)`; the second is an
  error. `Two(Int)` and `Two(String)` do not overlap, and a summon picks between them by the types
  it is resolved at. This rule, and the one on which module may declare an instance
  ([Traits and instances across modules [Decided]](#traits-and-instances-across-modules-decided)), are rules of
  installing an instance for the whole program.
- **An instance is visible after its `instance` statement,** as a `def`'s name is after the
  `def`. Within a
  module, a summon answered by an instance declared below it is an error, and so is a summon inside
  a generic definition declared above the instance that a use answers with it. Within the block, a
  function may call another of the instance's in either order, and two that call each other at the
  instance's types are an error. A call another instance answers, at other types, is no call of
  this block's functions, whichever way the two call each other.
- **An instance's function may call its own instance at other types, where the chain of calls
  can end.** `Area(Two(T))`'s `area` calls `area` at `T`, so at `Two(Two(Circle))` it calls
  `Area(Two(Circle))`'s, which calls `Area(Circle)`'s, and the chain ends however deep the type it
  starts at. A call reaching an instance's function, inside that function at some types, is an
  error when each of those types is **inside** the call's type at its place, as when `area` calls
  `area` at `Two(Two(T))`: `T` is inside `Two(T)`, so the chain need not end. The types compared
  are the ones a call gives the head's variables and the function's own type parameters, so
  `tag(R, s: S, label: R)` calling `tag` at `T` with `R` doubled to `{R, R}`, from `One(T)` and
  `R`, is accepted: `One(T)` is inside no `T`.
- **A type is inside another when deleting parts of the other gives it:** replacing a type by one
  of the types it is built from, or dropping components of a tuple, fields of a record or arms of a
  variant. `Int` and `{Int, String}` are inside `{Int, Two(String)}`, and `{String, Int}` is not.
  Refinements and the bounds of ranges are set aside. No infinite sequence of types avoids an
  earlier one inside a later one, so every chain the rule accepts ends.
- **A summon names the instance its types pick.** Each summon, and each use of a generic
  definition that summons, is resolved at its own types to the one visible instance that accepts
  them, and a call reads its function from that instance. An instance is declared at a module's
  top level.
- **An instance of an arithmetic operator's trait defines the operator.**
  `instance Addable(Money, Money)`, with `Output = Money` in its block, defines `add`, which `+` on
  two `Money` values calls, and an instance may be over two types, `instance Addable(Money, Int)`.
  A `**`'s exponent is a non-negative `Int` whichever instance answers it
  ([3.3 Arithmetic and logical operators](#33-arithmetic-and-logical-operators)), so an instance
  of `Exponentiable` names `Int` as its second operand.
- **An instance of a trait that declares no function has no block.**
  `instance Equatable(Money, Money)` is the whole declaration. A type's own `impl` block declares
  at least one function.

#### Equality and order

```python
type Money = Int
type Person = {age: Int, name: String}
type Version:
    new(major: Int, minor: Int)
type Two(T) = {T, T}

instance Equatable(Money, Money)
instance Orderable(Money, Money)
instance Equatable(Person, Person)
instance Orderable(Person, Person)      # by age, then name
instance Equatable(Version, Version)
instance Orderable(Version, Version)    # by major, then minor
instance forall (T) Equatable(Two(T), Two(T)) requires Equatable(T, T)
instance forall (T) Orderable(Two(T), Two(T)) requires Orderable(T, T), Equatable(T, T)
```

- **Two values are equal when they are the same value.** `Equatable` and `Orderable` declare no
  function, and an instance defines none: `==` compares a nominal value's constructor and its
  constructor's argument, as it compares a product's components. No instance redefines equality,
  so a key of a `Set`, a `Map` or a `groupby` and the equality a join or a refinement states mean
  one thing everywhere. A grouping or a comparison by something coarser names it at the use, as
  `groupby(names, lower)` does.
- **A nominal type opts in.** An instance names one nominal type twice, and every constructor's
  argument must compare by value where the instance's `requires` clause holds: a base type the
  compiler compares, a product of such types, or a nominal type with its own instance, declared
  above. A constructor with no parameters compares by its name alone. `instance Equatable(F, F)`
  for `type F = Int => Int` is an error at the `instance`, since no function is `Equatable`.
- **What orders by value is equal by value.** `Orderable(A, B)` requires `Equatable(A, B)`
  ([Declaring a trait](#declaring-a-trait)), so an instance of `Orderable` needs one of `Equatable`
  at its types. A requirement is not transitive: a definition that compares `T`'s values with `==`
  under `requires Orderable(T, T)` requires `Equatable(T, T)` too.
- **A nominal type's order is the order its declaration writes.** An orderable type has one
  constructor. Its values order by the constructor's argument: several parameters
  lexicographically, in the order they are written. A parameter whose type is a record type,
  `{age: Int, name: String}`, orders by its fields in the order they are listed, and so does a
  record type that is a field or a tuple component of it. `Person` orders by `age`, then `name`.
  Reordering a declaration's parameters or fields changes the order.
- **A type with no written order is not orderable.** A type with several constructors is not,
  since its constructors have no order ([Declaring a nominal type](#declaring-a-nominal-type)).
  Any record other than one the declaration lists has no order: one named by an alias, as in
  `type P = PersonFields`, or passed as a type argument, as in `type P = Two({b: Int, a: Int})`.
  Each is an error at the `instance`.
- **`Option` compares by value where its argument does.** The compiler declares
  `instance forall (T) Equatable(Option(T), Option(T)) requires Equatable(T, T)`, as it declares
  `Option`, so `Option::some(1) == Option::none` is `False` and an `Option` is a key of a `groupby`.
  `Option` has two constructors, so it is not orderable.
- **`max` and `min` read the same order.** `max([Person::new((age=3, name="a")), …])` is the
  greatest value in it by `age`, then `name`. Every field takes part, so no two different values
  tie.

#### Traits and instances across modules [Decided]

A trait is a member of its module ([9. Modules [Decided]](#9-modules-decided)), and an instance
belongs to the whole program.

- **`pub trait` exports a trait** with its functions and associated types, and `pub` is refused on a
  trait's `def`. Another module names it qualified, as `shapes::Area` in a `requires` clause, in
  `summon(shapes::Area(_))` and in an instance's head `instance shapes::Area(Circle):`, or by its
  own name after `use shapes::{Area}`.
- **An instance's functions read nothing a run gives its module.** Every import and run of the
  module shares the instance, so, as an associated function's
  ([Associated functions and methods](#associated-functions-and-methods)), its functions read no
  mutable variable, feed or source of the module, no value parameter without `const`, no member of
  a Module-typed parameter, and no member of a run the module declares other than its types'
  functions and constructors, directly or through the module's bindings and functions, and an
  error names what one reads.
- **An instance holds wherever its trait and its types can be named.** `instance` takes no `pub`,
  and no import selects instances: a module sees every instance its imports declare, directly or
  through other imports. A key of a `Set`, a join's equality and each summon therefore mean the same
  in every module.
- **An instance is declared in its trait's module or in the module of a nominal type its head
  names.** A module that can name the trait and the type imports the module declaring the
  instance, directly or through other imports. The compiler's traits and `Option` belong to no
  module, so a module declares an instance of a compiler trait only for a type it declares, and an
  instance for `Option` only of a trait it declares.
- **Outside its trait's module, no operand of an instance's head is a type variable.**
  `instance forall (T) shapes::Area(Two(T))` may stand in `Two`'s module, and
  `instance forall (F) Scales(Vec2, F)` only in `Scales`'s. Two modules that do not import each
  other then cannot declare overlapping instances, so an overlap is an error in the module declaring
  the second instance, which a module checked on its own reports
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)).
- **A public member's contract names only public traits.** A `pub` definition whose stated or
  inferred `requires` clause names a private trait is an error, and so is a `pub trait` whose
  signatures or `requires` clause name a private type or trait.
- **[Open] — a summon answered by an instance of another module.** A generic definition, an
  instance's function included, may be used at a type whose instance a module importing the
  definition's declares: `app`'s `instance Area(Square)` answering the requirement of a library's
  `def total(S, s: S) => Int requires a: Area(S)`. Which such instances a use may pass is open;
  the scoping rule of [Declaring an instance](#declaring-an-instance) orders one module's
  declarations.
- **[Open] — a trait as a member of a Module type.** A Module type names no trait, so a module
  reaches the traits of a module it takes as an argument only through an import.

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
- **A polymorphic function type has one `requires` clause,** after its codomain, holding the trait
  requirements on the types it quantifies and the context requirements of a call:
  `forall (T) {T, T} => T requires Orderable(T, T), Transaction causes AffectWorld`
  ([Writing requirements and effects](#writing-requirements-and-effects)).
- **It is never a type constructor.** `forall (T) V` does not denote a function from types to
  types. A parameterised alias, if added, is written in the head form `Pair(T) = {T, T}`
  ([6.7 Type-alias statements](#67-type-alias-statements)).
- **A diagnostic prints an inferred polymorphic type in this notation.** A mismatch against a
  polymorphic annotation prints the right-hand side's type with each variable it quantifies as a
  parameter, `A`, `B`, … in order of first appearance, and each trait it requires of them as a
  requirement, named where it has an associated type and that type bounded by what it is.
  `def inc(a): a + 1` prints as `forall (A) A => Int requires r: Addable(A, Int), r::Output <: Int`.
  A part of the type the notation cannot write, such as a parameter joined with another type, is
  marked in the printed type (`A ∨ Int`), not dropped.

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
| `min(xs)` | Minimum element of `xs`. Element type must support `<`. |

All three are unary and take a collection-typed argument. Other aggregates
(`count`, `avg`, `len`) are **[Planned]** but not yet recognised.

`max` and `min` are to return `Option(T)`, `Option::none` for an empty collection, as the checked
lookup `c[k]` returns `Option::none` for an absent key
([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)). A postfix `!` is to
unwrap the result where the collection is proven non-empty, as it unwraps a lookup whose key is
proven present
([Subscript and unwrap syntax [Decided]](#subscript-and-unwrap-syntax-decided)). Until then `max` of
an empty collection is not defined, and neither is `min` of one
([Partiality is not yet defined](#partiality-is-not-yet-defined-open)).

The north-star programs additionally assume non-aggregate built-ins —
`str`, `open`, `stdout`, and a stream-restriction combinator
`restrict` — all **[Tentative]**: they exist only as usage sketches in
[`tests/programs/`](../tests/programs/), with no design writeup.

> **[Open]** — the restriction combinator's **name**, and how any of
> these combinators are *called*. The corpus spells the same operation
> two ways: `txn_kv` and `ledger_balance` write `c.restrict(\e -> …)`,
> the north-star `storefront` writes `orders.filter(\o -> …)`, and
> nothing decides between them — one of the two names has to go. Both
> are written in **method** position, as is `catalog.keys()`. A method
> call resolves among the methods of a
> nominal type ([6.8 Nominal types and methods
> [Decided]](#68-nominal-types-and-methods-decided)). `Set`, `Map` and
> `FullMap` are nominal, so `catalog.keys()` resolves; `List` and
> `Collection` are structural, so `orders.filter(…)` on one names no
> method, and a trait's function is read from an instance
> ([Summoning an instance](#summoning-an-instance)).

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
> returns a `FullMap` keyed by the keys present in `c`
> ([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided),
> [src/ccl/design/collections.md](../src/ccl/design/collections.md)). Its
> entries iterate as key–value pairs, so the rollup destructures the pair
> in the `for` binder and rebuilds a map with `map` over a comprehension
> ([3.12 Comprehensions](#312-comprehensions)):
>
> ```python
> map([key -> sum([o.price for o in g]) for key -> g in groupby(paid, \o -> o.sku)])
> ```
>
> (the north-star `storefront` `/stats` rollup). A single binder takes the whole
> entry rather than the group (§4.6), so `for g in groupby(…).values()` is how to
> iterate the groups alone — which is what the unkeyed form above does today.

### 7.3 Sources

Sources are built-in functions registered at compile time. A source
call denotes the entire stream the source will produce. `http_serve` is
both a source and a sink: it returns a source of requests and a sink for the
responses ([10. Sinks](#10-sinks)).

| Call | Source | Domain |
|---|---|---|
| `stdin()` | Process standard input | One element per line of UTF-8 text. |
| `http_serve(port, method, path)` | HTTP server, a source and a sink | Returns a `(requests, responses)` 2-tuple. The requests source yields request bodies; the responses sink is a feed. Called only as the whole right-hand side of a top-level `=` (see below). |

Additional sources may be pre-registered by the host embedding (testing,
demos, etc.). `std::time` adds a clock read and an alarm source and sink
([7.5 Time [Decided]](#75-time-decided)).

Opening a source requires `ObserveWorld`, and binding a sink causes `AffectWorld`
([Inputs from outside the program](#inputs-from-outside-the-program),
[Output outside the program](#output-outside-the-program)). A reading, such as the clock, is a call
of a `@Builtin` function a std module declares ([9.16 The std root](#916-the-std-root)).

`http_serve` opens its route when the program starts, so a call is the
whole right-hand side of a `=` in the top-level block, and its three
arguments are string constants ([9.19 Constants](#919-constants)): a module
takes its route's address from a `const param`, and each run serves the
address its arguments give. The target is any pattern (§4.3), and a tuple
pattern names the two sides:

```python
reqs, resps = http_serve(port, method, path)
```

- the `reqs` side is a streaming source: each element is the
  body of one incoming request to `(method, path)` on `port`.
- the `resps` side is a sink, a feed: feeds into it
  (via `<<` from a request-handler `for` loop, or via `<<=` once)
  become the response bodies. The sink pairs each response with its
  triggering request — the request that was bound to the loop
  variable in the iteration that produced the response.

Multiple `http_serve` calls in the same program that share a `port`
share an HTTP listener; the `(port, method, path)` triple must be
unique across the program, across all its runs.

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
> itself: a *keyed feed* — supporting both
> `resps[req.id] = …` and a feed form `resps << …` — that needs CCL
> and CHL definitions.
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

### 7.4 `box`

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

**A comprehension over a boxed collection is not boxed.** It reads the collection the box
holds, so its result is a collection keyed like that one: by the keys of whichever alternative
the box holds. Two comprehensions over the same box are keyed alike, so they join and combine
position by position:

```python
b = box([1, 2]) if c else box([1, 2, 3])
ys = [x * 2 for x in b] if d else [x * 3 for x in b]   # ✅ both keyed like `b`
```

To keep a result as a box — to join it with another box, or to return it where an abstract
collection type is expected — box it. The new box ranges over the alternatives the source box
does, so it satisfies every annotation the source satisfies:

```python
def doubled(xs: List(Int)) => List(Int):
    box([x * 2 for x in xs])                            # ✅ a list wherever `xs` is one
```

**Box each branch's result, not something inside it.**

```python
box([y for y in xs if y > 1]) if c else box(ys)                # ✅
box([y for y in b1]) if c else box([z for z in b2])            # ✅
[y for y in b1] if c else [z for z in b2]                      # ❌
```

The branches of the third spelling are keyed like two different boxes, `b1` and `b2`, and two
collections keyed differently do not join. Boxing each branch records which keys it has, and
the boxes join.

**An abstract collection type needs `box` too.** `List(T)` and `Collection(T)` say nothing
about which collection they are, so a value reaches one only by being boxed:
`x: List(Int) = box([1, 2, 3])` binds, and `x: List(Int) = [1, 2, 3]` is an error. A
filtered box is not a `List(T)`, because a filtered range of positions has gaps:
`box([x for x in xs if x > 1])` is a `Collection(Int)`.

---

### 7.5 Time [Decided]

**[Decided]** — the rules of this section; the std root that holds `std::time` is **[Planned]**
([9.16 The std root](#916-the-std-root)).

`std::time` provides a reading of the wall clock, `time::now()`, and an alarm source and sink,
`time::alarms()`. Its other members are library functions over the two types it declares:
`time::Instant`, a point on the UTC timeline counted in nanoseconds since the Unix epoch, and
`time::Duration`, a length of time in nanoseconds. `Instant` is unrelated to the builtin `Time`, a
position in the commit order ([6. Types (informal sketch)](#6-types-informal-sketch)).

#### `time::now()`

`time::now()` returns the runtime's clock reading as an `Instant`.

- **A reading is the system clock, best effort.** Readings carry no order: a reading can be
  earlier than one taken before it, within one process or across a restart. The runtime does not
  correct the system clock. A program that needs an order takes it from the transaction system.
- **Each evaluation of a call reads the clock.** A call is evaluated once per iteration of each
  enclosing loop. Two calls can return different readings, including two calls in one transaction.
  A binding holds one reading: in `t = time::now()`, every use of `t` is the same instant.
- **A call at a module's top level reads the clock once, when the program first starts.** A reload
  and a restart keep that reading
  ([Inputs from outside the program](#inputs-from-outside-the-program)).
- **A reading introduces no additional sequencing.** A computation consuming its value has an
  ordinary data dependency on it. Taking a reading does not order independent evaluations
  ([8.5 Ordering and concurrency](#85-ordering-and-concurrency)). Commit order never consults a
  reading, so a transaction that commits after another can hold an earlier reading. Both rules
  describe this clock, whose readings carry no order. A clock whose readings the commit engine
  places in commit order would order them.
- **A call requires `ObserveWorld`.** It is a reading
  ([Inputs from outside the program](#inputs-from-outside-the-program)), not an expression the
  compiler may merge or duplicate. A module whose top level calls `time::now()`, directly or
  through a function, requires `ObserveWorld` and is run
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)).

#### `time::alarms()`

`time::alarms()` returns a source and a sink. Each row fed to the sink is held, and comes out of
the source once the clock reads at or after the row's `time::at` field. `std::time` declares it as:

```python
def alarms(R <: {at: Instant}) => {Source(R), Feed(R)}
```

```python
import std::time

expiries, set_expiry = time::alarms()

sessions: Mut(Map(String, time::Instant), Txn) := Map::empty   # session id -> expiry
expired: Feed(_)

for r in requests:
    with begin():
        expiry = time::now() + time::minutes(30)
        sessions[r.session] := expiry
        set_expiry << (session=r.session, time::at=expiry)

for r in logouts:
    with begin():
        sessions[r.session] := time::now()

for e in expiries:
    with begin():
        match sessions[e.session]:
            case Option::some(expiry):
                if expiry == e.time::at:
                    expired << (session=e.session)
            case Option::none:
                pass
```

- **Binding.** The call is bound at a module's top level by tuple destructuring, as `http_serve` is
  ([7.3 Sources](#73-sources)). The call opens a source, so the calling module's top level requires
  `ObserveWorld`, and `std::time` itself stays shareable.
- **Rows.** `R` is the row type, bounded by `{at: Instant}`
  ([Kinds and bounds](#kinds-and-bounds)), so a row is the caller's own record with a field
  `time::at: time::Instant`. The label belongs to `std::time` ([9.12 Field labels and tags belong
  to a module](#912-field-labels-and-tags-belong-to-a-module)), and every other field is the
  caller's. The call's uses determine `R`, as any type parameter's uses do
  ([Type parameters](#type-parameters)): the rows the program feeds the sink and its loops over the
  source. `Source(R)` is a source whose elements are `R`s.
- **Holding.** A row fed inside a `with begin():` block is held only if the transaction commits
  ([8.4 Feeds are the second form of mutability](#84-feeds-are-the-second-form-of-mutability)). A
  row whose `at` has passed when it is held comes out at once.
- **Release.** The runtime releases a row once its clock reads at or after the row's `at`. A
  reading in the transaction handling the row has no order relative to the release and can be
  earlier than `at`.
- **Arrival.** A released row is an arrival on the source
  ([8.5 Ordering and concurrency](#85-ordering-and-concurrency)): every loop over the source
  receives it, and it orders what consumes it as any arrival does. Of two rows held at once, the
  row with the earlier `at` arrives first, and rows with equal `at` arrive in an unspecified order.
  A row held after another row's release can arrive after it with an earlier `at`.
- **A release is a reminder to check, never a decision.** A row comes out whether or not a later
  transaction superseded the decision that held it. The handler's transaction reads the state the
  row refers to, as the example's comparison of `e.time::at` with the session's current expiry
  does.
- **No feed cycle.** A loop over the source that feeds the sink closes no cycle of feeds: the path
  from the sink to the source passes through the runtime, as `http_serve`'s responses and requests
  pass through a client.
- **Reload keeps held rows; a process exit discards them.** The pair's identity is the module path
  and name of the binding that holds it, as a mutable variable's is, and a reload that keeps the
  binding keeps its held rows. Durable state is **[Tentative]** ([8.8 `@LoadFrom`](#88-loadfrom)).

### 7.6 `int_to_uint` (temporary)

This operation has been added as temporary support for the development of proven and checked
lookups. It will be removed when `Int`s can be used directly for list lookups.

```
int_to_uint(x)
```

The `UInt` equal to the `Int` `x`. Its type is `(x: Int) => {UInt where int_eq_uint(x, _)}`, where
`int_eq_uint` holds of an `Int` and a `UInt` that are the same integer. A refinement checked against
the result can use that equality, so `int_to_uint(1)` checks against `{UInt where _ == z}` for
`z = int_to_uint(1)` and `int_to_uint(2)` does not. CHL has no `UInt` literal, so a `UInt` constant
is written as `int_to_uint` of an `Int` literal.

`int_eq_uint` appears only in this type; a program cannot write it in a refinement.

A negative `x` has no `UInt` equal to it. Applying `int_to_uint` to one is a runtime error.

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
  begin():` block, or in a function the block calls, which requires
  `Transaction` for them and gets it from the block (§8.7, **[Decided]**); a write that no
  block encloses is rejected (§8.3). A call inside a block of a function
  that runs a block of its own is a disguised nested transaction.
- **Nested transactions are rejected** — a block commits as one unit, so a
  `with` inside it has no coherent meaning.
- A block causes `RunTransaction`, and its body supplies `Transaction` to what it calls. A body that
  causes `RunTransaction`, directly or through a call, is the nested transaction above
  ([Discharging requirements and effects](#discharging-requirements-and-effects)). An exception that
  escapes the block aborts it: none of its writes commits and no output inside it is sent
  ([Exceptions](#exceptions), **[Decided]**).
- **Branch guards and tag dispatch.** A block may carry `if`/`elif`/`else`
  guards, more than one of them, and `match` dispatch. Each branch's
  writes are scoped to its own path and the transaction commits on the
  disjunction of the writing paths, so a write on the spine beside a
  guard commits unconditionally. In a block in statement position, a bare `if p:` with no
  `else` is the deny idiom: where `p` fails over the snapshot the transaction contributes no
  write and no reply.
- **An induction accumulator may not be written under a branch inside a
  block** (rejected with a diagnostic). Write it after the block, or, if
  it should be shared across the transaction, declare it `Mut(…, Txn)`
  and write it on the spine.

**Scope transactions minimally.** Only the operations that must be atomic
go inside `with begin():` — input validation before it, response
assignment after it. The north-star handlers observe this throughout (e.g.
`storefront`'s `/order` matches the catalog before opening the transaction
around `reserve` + `quote` + the feed).

#### A block is also the value it computes

**[Decided]** — the rules of this section.

A `with begin():` block on an assignment's right-hand side is the value of its last statement, by
the rule a function body follows
([4.1 `def` — function definition](#41-def--function-definition)): an expression, or an `if`,
`match` or `try` whose blocks each end in a value. The binding carries the value past the block's
end, so a handler scoped minimally replies outside the block with a value computed inside it:

```python
for req in withdraw_reqs:
    result = with begin():
        if balance >= req.amount:
            balance := balance - req.amount
            "ok"
        else:
            "insufficient funds"
    withdraw_resps << result
```

- **The value is read in the block's snapshot,** after the writes its path made before it
  (read-your-writes, [8.3 Reads](#83-reads)).
- **Every path of a block in value position commits.** In a block where some path writes, a path
  that writes nothing commits its reads, which places its value at a commit time. There is no deny:
  where the bare `if p:` above fails, the transaction commits no write and the code after the block
  still runs, with the value that path computed.
- **The value is available once the block commits.** Inside a loop, each iteration binds its own
  block's value, so a reply after the block is indexed by the iteration, as any reply outside a
  block is ([8.4 Feeds are the second form of
  mutability](#84-feeds-are-the-second-form-of-mutability)).
- **A block that writes no transactional variable is a snapshot read.** It commits nothing, and its
  value is as of an arbitrary commit position, as an as-of read's is ([8.3 Reads](#83-reads)). It
  reads several variables at one snapshot: `(a, b) = with begin(): (a, b)`.

### 8.3 Reads

- **In-context** (inside the mutating loop or block) — a bare reference is
  the value at the current position: the previous iteration's value, or,
  after a write earlier in the same iteration/block, the just-written
  value (**read-your-writes**).
- **Trailing induction read** — after a `for` loop, a bare reference to an
  induction accumulator is its final value (or the pre-loop value if the
  source was empty). The loop has ended, so "latest" is unambiguous.
- **A function's result** — a bare reference as a function's last statement
  is a read: the function returns the variable's value where its body ends,
  never the variable, which no function returns (§8.1).
  `def total(xs): s := 0; for x in xs: s += x; s` returns the sum, and
  `def available(): stock` reads `stock`, transactional, so it requires
  `Transaction` and `ReadTxn(stock)`.
- **A `Txn` mutable variable is read only inside a `with begin():` block,** or in a function
  the block calls (**[Decided]**), which requires `Transaction` for it
  ([8.7 Transactions as contextual parameters](#87-transactions-as-contextual-parameters)).
  A bare read that no block encloses is an error, and stays one: the block is what pins a
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
- **Reply *outside* the block** rides its own loop's domain and fires every iteration regardless of
  commit — request-indexed, value-correct, but not commit-ordered. A reply of a block's value waits
  for that block to commit, which every path of it does
  ([A block is also the value it computes](#a-block-is-also-the-value-it-computes)). **To gate or
  commit-order a reply, put it inside the block.**

### 8.5 Ordering and concurrency

A mutable program's meaning is an *ordering story* — which effect happens
before which. CHL states that story as a single principle:

**Execution is maximally concurrent; source position orders nothing by
itself. The only ordering is the transitive closure of dependency
edges, and every edge originates at an _event_.** Two pieces of logic are
ordered exactly when a chain of dependency edges connects them, and freely
interleaved (or parallel) otherwise. The events:

- **Program start.** Initializers, literals, constant loop sources
  (`[10, 20, 30]`), and top-level `=` bindings are available here; logic
  reading only them runs immediately.
- **Incoming data on a source.** Logic consuming an element depends on that element's arrival.
  Arrival order gives the source's position order; it does not order the iterations of a loop over
  the source. Those iterations are ordered only where their body requires it
  ([Ordered loops](#ordered-loops)). A transactional write alone imposes no such requirement.
  An arrival also depends on every commit whose output was sent out of the program before the
  element arrived ([Output outside the program](#output-outside-the-program)): a request a client
  sends once it holds a reply comes after the commit that reply rode. Requests sent concurrently
  stay unordered.
- **A data dependency forced by logic.** When logic reads a value another
  piece produces, the read depends on the write — read-your-writes in a
  block, a commit decision reading a snapshot, a reply consuming its own
  commit record.

  Within one evaluation — the top level's, a block's, an iteration's or a call's — written order
  decides which way such an edge points. Its statements, and the arguments and operands of each
  expression in it, take effect in the order they are written wherever two of them interact: a
  read sees the writes written before it and none written after it, a later write leaves what an
  earlier read saw unchanged, and whatever is written after a piece that raised runs only where it
  did not raise ([Exceptions](#exceptions)). Two pieces that cannot change each other's values or
  outputs, in either order, are unordered: appends to a feed commute, two reads commute, and a
  reading is keyed by its call path rather than by when it is taken
  ([Inputs from outside the program](#inputs-from-outside-the-program)). Commits are ordered by
  the consequences below, not by where a block is written.
- **`await_final`.** The **completion event** of a transactional mutable variable
  (§8.6): it is available only once every writer of the mutable variable has
  drained, and everything downstream depends on that completion.

Consequences a program may rely on:

- **Commit order is not global.** Two `with begin():` blocks are ordered
  relative to each other only if they mention a mutable variable in common —
  a shared variable is what makes one block's commit visible to the other. A
  block mentions what its body's `ReadTxn(x)` and `WriteTxn(x)` name, its
  footprint ([Discharging requirements and
  effects](#discharging-requirements-and-effects)).
  Blocks with no variable in common are **unordered**: nothing in the
  language imposes an order between them, and their transactions interleave
  freely. Two independent `for` loops relate their accumulators the same way.
- **Commit order is not lexical order.** A block's trigger makes it eligible to run. Two blocks
  do not commit in their written order unless a dependency orders them.
- **Commit order is not position order.** The iterations of a loop whose body
  runs a block commit in the order the transaction engine decides, which
  need not be the loop source's position order; the loop is ordered only by
  what [Ordered loops](#ordered-loops) names. A loop that a
  non-transactional accumulator orders runs its iterations, and so their
  transactions, in position order.
- **A clock reading orders nothing** (**[Decided]**). A `time::now()` reading is not an event,
  and commit order never consults one. A row an alarm source releases is a source arrival
  ([7.5 Time [Decided]](#75-time-decided)).
- **Read-your-writes** within a block or iteration.
- **Reply-after-commit / cross-endpoint monotonicity.** A reply fed inside a block depends on its
  commit, and a request that arrives after the reply was sent depends on that commit in turn (the
  arrival edge above). These edges, rather than the relative arrival order of independent
  requests, give the cross-endpoint guarantee: a client that sees `ok 2` then reads the counter
  observes `≥ 2`.
- **Terminal vs. temporal reads.** `await_final` (and the trailing
  induction read) wait for a history's *completeness*; an as-of read waits
  only for the *frontier* (that no earlier-or-equal commit is still
  outstanding) and samples the mutable variable as of the reader's own position.
- **A trigger alone imposes no order between iterations.** Program start makes a batch of
  transactions eligible without ordering them. Distinct source arrivals likewise order no loop
  whose body requires no order. The engine may choose any serialization consistent with the
  program's dependencies. To require position order, the loop body must introduce an ordering
  dependency ([Ordered loops](#ordered-loops)). `await_final` waits for completion; it does not
  choose an order for the transactions whose completion it awaits.

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

**The rules hold across modules** (**[Decided]**). `await_final(x)` requires nothing: its value is
one value for the whole run, the same wherever it is evaluated ([6.9
Capabilities](#69-capabilities)). A writer of `x` is any statement that causes `WriteTxn(x)`, or a
top holding it, directly or through a call, a call of another module's function included, so the
await waits for every writer of `x` in the program. A writer that depends on `await_final(x)`
through another module's public value is the cycle above, and an error at the write.

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

### 8.7 Transactions as contextual parameters

**[Decided]** — the rules of this section.

(2026-06-29 §6; the north-star `txn_kv` program is the worked example.)

A transaction is passed *implicitly by block scope*: `with begin():` establishes it, and
`Mut(…, Txn)` mutable variables are the shared state. It is a contextual requirement, so a
transaction reaches a called function without a `Mut` parameter:

- `def put(…) requires Transaction:` — the function declares it needs a
  transaction from context. A function reading or writing a transactional
  mutable variable outside a block of its own requires one whether or not it
  says so, and a call of it that no block encloses is an error.
- **A transaction is never a value, but it may be named.** `with txn = begin():` names the
  block's transaction `txn`, and a requirement names the caller's, `requires txn: Transaction`.
  The name stands only before `::`, as a requirement's instance does
  ([Summoning an instance](#summoning-an-instance)): nothing passes, stores or returns a
  transaction, and a function value naming one does not leave the block or the function that names
  it ([Discharging requirements and effects](#discharging-requirements-and-effects)). `txn::now()`
  is the function on a transaction that answers its time, so a called function reads it through
  its requirement rather than a parameter threading it there.
  **[Decided]** — naming a transaction, and `txn::now()`.

Supporting decisions (same source):

- **Discharged by the requirement solver, *not* algebraic effects.**
  Cambra compiles to static dataflow; handler-based effects make control
  flow non-local and data flow handler-dependent — exactly what the
  dataflow compiler cannot see through. `requires Transaction` is ordinary
  dictionary passing: `Transaction` is a context trait whose instance the
  enclosing block supplies ([6.9 Capabilities](#69-capabilities)).
- **Locally-scoped transactions, not global coherence.** A fresh transaction is
  minted per `with begin():` block; many exist over a program's life.
- **[Open] — domains.** Every transaction is the one global domain's. A domain index,
  `Transaction(dom)` created with `with dom.begin()`, would partition the state into domains each
  serializable on its own, for scale; nothing needs one yet.
- **A commit is a data operation on a time-region**, not a control effect:
  block exit merges the region forward. A transaction that should not commit
  is written with a guard, the deny idiom of
  [8.2 Transactions: `with begin():`](#82-transactions-with-begin), or ends
  with an exception that escapes the block, which drops the region
  ([Exceptions](#exceptions)). There is no `abort()`.
- **Terminology:** type `Transaction`; variable abbreviation `txn` (never
  `tx`, which collides with "transmit"); operation `begin()`.
- **Implicit *parameters* only — never implicit conversions**; where a requirement is
  discharged stays inspectable.
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
qty_units: Mut(Map(String, Int), Txn) := map([k -> q * 10000 for k -> q in held])
```

Iterating a map binds each entry, and `map` re-keys the scaled pairs by their keys
([Re-keying is explicit](#re-keying-is-explicit-decided)), so that scales every quantity
the predecessor held.

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

## 9. Modules

A **module** is one `.cambra` file. A module is used in one of two ways:

- **Importing** it brings its public members into scope. Importing asserts that the module is
  shareable: its top level reads nothing from outside the program, and leaves behind no output and
  no state another module could reach. Its members exist once for each distinct set of arguments
  its imports pass, however many modules import it with those arguments
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)).
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
- **Shared import.** The one evaluation of an imported module's top level at one set of arguments,
  whose members every import passing those arguments reaches. Any state it holds ends with its top
  level, and it is named by the module path with those arguments, `shop(Receipt=stripe::Receipt)`
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)).
- **Member.** A binding at a module's top level. Bindings inside a `def`, a loop, or a block are
  **locals**.
- **Public member.** A member declared with `pub`. Every other member is private to its module.
- **Parameter.** A value, a type, or a module that a run or an import supplies, declared by a
  `param` statement ([9.4 Parameters](#94-parameters)).
- **Module type.** The structural type of a module's public members, `Module{…}`
  ([9.8 Module types](#98-module-types)).
- **Module interface.** What checking records about a module for the modules that use it: its
  public members' contracts, its parameters, and whether it is shareable
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module),
  [9.14 Checking a module on its own](#914-checking-a-module-on-its-own)).

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
- An import reaches every public member of the module's shared import. Importing a module that is
  not shareable is an error
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)).
- An import passes arguments to the module's parameters as a run does
  ([9.4 Parameters](#94-parameters)): keyword-only, one for each parameter without a default. Every
  argument is a constant, so two imports of one module with equal arguments reach one shared import,
  and its type members are one type in both: `import sorted_map(K=String)` in two modules gives
  both one `sorted_map::Map`. An omitted argument is the parameter's default, so `import m` and
  `import m(x=1)` reach one shared import when `x` defaults to `1` (**[Planned]**). An argument may
  be a literal, a type, or an import name passed as a value of its Module type
  ([9.8 Module types](#98-module-types)). **[Decided]** It may be any constant
  ([9.19 Constants](#919-constants)), and two arguments with one value reach one
  shared import. A run
  name may not: a shared import stands outside every run, and an import reaches no run's state
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)).
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
arg      ::= ( ident | Ident ) "=" expr
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
  An argument is any expression over the names above the statement: the declaring module's members,
  earlier runs' members, imports, and parameters. A `const` parameter's argument is a constant
  ([9.19 Constants](#919-constants)). A run's public members are what it returns, so
  `run index(docs=p::documents) as ix` passes one run's member to another. An import name in an
  argument denotes its shared import, and a run name its run, as a value of its Module type, which
  is how a module is passed to another.
- A run name is bound from its statement to the end of the declaring module, as a value binding
  is, because a run is an evaluation. `eu::x` reaches the run's public member `x`. An argument names
  only runs above its own, so runs cannot depend on each other in a cycle: `run svc(peer=y) as x`
  above `run svc(peer=x) as y` names `y` before it is bound.
- A run needs no `import`. A run name and an import name in one module may not coincide. A
  statement naming a shareable module at arguments an import may pass is an `import`, and running
  it there is an error ([Shareable modules](#shareable-modules)). A shareable module imported in
  one place and run with a run among its arguments in another reaches two copies of itself: the
  import reaches the shared import, and the `run` statement declares a run.
- A module returns a run it declares the way it returns any value: by binding it to a public member.
  `pub audit = a`, below `run audit_api as a`, is a member of the run's Module type ([9.8 Module
  types](#98-module-types)), and a module running `shop` reaches the run's members through it,
  `shop::audit::events`, as through a parameter of Module type. `pub` on a `run` is refused.

### 9.4 Parameters

```ebnf
param_stmt ::= ["const"] "param" ident ":" type ["=" expr]
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
  It names a type that varies with the run, and takes a bound written as a `def`'s type parameter's
  is ([Kinds and bounds](#kinds-and-bounds)). A run or an import supplies it as an argument,
  `Receipt=stripe::Receipt`, as it does any parameter without a default. Checked on its own, the
  module knows a bounded type parameter only through its bound: `Receipt` above has an `id` and
  nothing else checking can rely on ([9.14 Checking a module on its
  own](#914-checking-a-module-on-its-own)). The module's uses of a type parameter with no bound are
  checked at each argument. A default is a type over the module's import names and the type
  parameters declared above it. **[Planned]** An argument left out is inferred from the types of the
  other arguments.
- **A structural bound is met by structural types only.** A nominal type relates to no structural
  type ([A nominal type is opaque](#a-nominal-type-is-opaque)), and a record meets `{id: String}`
  only through the labels the bound names, which belong to the bounding module
  ([9.12 Field labels and tags belong to a module](#912-field-labels-and-tags-belong-to-a-module)).
  `Receipt=stripe::Receipt` therefore passes when `stripe::Receipt` is a record whose `id` is the
  bounding module's label.
- **[Decided] — a trait requirement is a bound a nominal type meets.** `param Receipt requires
  Identified(Receipt)` takes any type with an instance of `Identified`, checked at the `run` or
  `import` against the instances the argument's module sees. Inside the module, `Receipt` stays
  opaque and has `Identified`'s functions, as a type parameter under a `requires`
  clause does ([Trait requirements](#trait-requirements)). The clause follows a `<:` bound where
  there is one, and may name the module's other type parameters, as
  `requires Convert(Receipt, Price)` does.
- A value parameter is an immutable value, annotated with its type. A value parameter written
  without an annotation is an error, so each module states what its arguments are, if only as `_`.
  Its type is its annotation, with each `_` in it inferred from the module's uses the way a function
  parameter's is: `param k: _` leaves all of it to inference. The annotation is the whole annotation
  of the parameter's binding, so it may be polymorphic, `param f: forall (T) T => T`
  ([Polymorphic type annotations](#polymorphic-type-annotations)).
- `const param` declares a value parameter whose argument, at every `run` and
  `import`, is a constant, and whose default is one too
  ([9.19 Constants](#919-constants)). It is the only kind of parameter a constant
  may name. A type parameter and a Module parameter are fixed at link time already, and `const` on
  either is an error.
- A parameter of Module type is how a module takes another module. The argument is a name that
  denotes a module ([9.6 Qualified references](#96-qualified-references)), and Module subtyping is
  the check ([9.8 Module types](#98-module-types)). The parameter is a qualifier: `audit::events`
  reaches the argument's member.
- A parameter's type is the only thing checking reads about its argument
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)). An interface is an
  alias of a Module type, usually exported by a library both sides import.
- A parameter is in scope throughout its module. A member or a `use` name with the same spelling
  is an error naming both sites, and so is a parameter spelled like an import name or a run name. A default is evaluated before the module's members, so it is an expression over the
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
pub def Price::discounted(self, pct: Int) => Price: …
```

**[Planned]** — `pub` on a transactional mutable variable:

```python
pub stock: Mut(Map(String, Int), Txn) := Map::empty
```

**[Planned]** A declaration loaded with `@LoadFrom` is an ordinary declaration without an
initializer ([8.8 `@LoadFrom`](#88-loadfrom)), so its `pub` stands at the head of the declaration's
line, below the decorator:

```python
@LoadFrom(qty)
pub held: Int
```

- A member without `pub` is private. Only its own module can name it.
- `pub` on `:=` is accepted (**[Planned]**) on the statement that introduces a `Txn` mutable
  variable, which states
  its type `Mut(V, Txn)`, and refused on a later write to it. It is refused on an induction variable
  ([9.10 Induction variables stay in their module](#910-induction-variables-stay-in-their-module)).
- `pub` is refused on `import`, `run`, `param`, `op=`, `<<=`, `for`, `if`, `match`, `with`,
  expression statements, and anywhere but a module's top level.
- A public name is bound exactly once at its module's top level. A later binding of the same
  spelling, public or private, is an error naming both sites. Without this rule the exported binding
  would be whichever one was in scope at the end of the module, and a shadowing edit far from the
  `pub` would change the module's interface.
- Private names keep the ordinary top-level shadowing of
  [5. Scoping and binding](#5-scoping-and-binding).
- `pub` on a `type` declaration exports the nominal type with its constructors, and with `new` and
  `extract` in the single-constructor form. `pub` on an associated function's `def`, including one
  in an `impl` block, exports it, and one without `pub` is reached only from its own module, in
  either spelling
  ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). An associated
  function binds no module-level name, so the bound-once rule above does not apply to it.
- Types need not be annotated on public members. An unannotated member's contract is its inferred
  type ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)).

### 9.6 Qualified references

A **name that denotes a module** reaches that module's members: an import name, a run name, a
parameter of Module type, and a member bound to one of them, `pub audit = a` ([9.3 Runs](#93-runs)),
whether reached by its name, through a path of public members, `shop::audit`, or through `use`. `::`
separates the name from the member, and `.` stays record projection ([3.9 Subscript and attribute
access](#39-subscript-and-attribute-access)). With `import shop::cart`, `run shop::cart as c`, and
`param p: Module{count: Mut(Int, Txn)}`:

| Written | Position | Means |
| --- | --- | --- |
| `cart::total` | value | the public member `total` of `shop::cart`'s shared import |
| `cart::Item` | type | the public type member `Item` of `shop::cart`, an alias or a nominal type |
| `c::count` | value, write target | **[Planned]** the public member `count` of the run `c` |
| `c::total` | value | the public member `total` of the run `c`, a copy distinct from `cart::total` |
| `p::count` | value, write target | **[Planned]** the member `count` of the run passed as `p` |
| `cart` | value | `shop::cart`'s shared import, as a value of its Module type ([9.8 Module types](#98-module-types)) |
| `c` | value | the run `c`, as a value of its Module type |
| `cart::hidden` | any | error: `hidden` is private to `shop::cart`, with a secondary label at its declaration |
| `cart::missing` | any | error: `shop::cart` has no member `missing` |

- Import names, run names, Module-typed parameters, and members bound to a module cannot be
  shadowed. A binder anywhere in the module spelled like one of them is an error. `m::f` names a
  module, so a value binder spelled `m` would give one spelling two meanings in one scope.
- An import name is in scope throughout its module, including above the statement: an import is a
  static fact rather than an evaluation, so no order constrains it. A run name is in scope from its
  statement down ([9.3 Runs](#93-runs)).
- A qualified member is a named callee. `cart::total(x)` is a call to the member it resolves to,
  including the special forms (**[Planned]**) and `Mut`-parameter call shapes that dispatch on the
  callee. Through a parameter, `p::f(x)` takes its call shape from `f`'s type in the
  parameter's Module type (**[Planned]**).
- A qualified generic member keeps its polymorphism: `n::id(1)` and `n::id("a")` both check.
- A name an import's `use` clause binds is in scope throughout its module, including above the
  statement, as the import name is. One a run's `use` clause binds is in scope from the `run`
  statement down, as the run name is. A local may shadow either. A member of the module with the
  same spelling is an error naming both sites.

### 9.7 Importing asserts a shareable module

**[Decided]** — importing a module whose only state is induction variables and private feeds: the
compiler refuses to import a module that declares mutable state, performs IO, runs another module,
or has a top-level loop, `if`, `match` or `with`.

Importing a module asserts that it is **shareable**: its top level reads nothing from outside
the program, and leaves behind no output and no state another module could reach
([Shareable modules](#shareable-modules)).

State that outlives a top level therefore belongs to runs. Every transactional mutable variable,
and every feed other modules append to, has a run that a `run` statement names, so the source says
which modules reach it: the module that runs it, and the modules that run is handed to. An imported
module declares no run, since the import would reach the run's state. A module that runs another is
itself run.

An imported module's top level is evaluated once for each distinct set of arguments, however many
modules import it with those arguments, because its members are values it computes. That evaluation
is the module's **shared import** at those arguments. Every import passing them reaches the same
members. Its run path is the module path with its arguments, so it never collides with a run a
`run` statement names. Its induction variables and private feeds are its own: their histories end
with its top level, so no other module reaches them.

```python
# inventory.cambra: declares a transactional variable, so it is run and not imported
stock: Mut(Map(String, Int), Txn) := Map::empty
pub def reserve(sku, qty) requires Transaction:
    …
pub InStock = {String where _ in stock.keys()}   # intended; not supported today
```

`InStock` is intended and not supported today, in one file as across modules: the compiler cannot
name a mutable map's key set in a type. `run inventory as inv` and `run inventory as eu_inv` are two
runs, each with its own `stock`, and `inv::InStock` is a different type from `eu_inv::InStock`.

#### Shareable modules

A module is **shareable** when its top level, less what its scopes discharge, requires nothing but
trait instances and causes nothing
([6.9 Capabilities](#69-capabilities)). An import shares
one evaluation among every import passing its arguments, so what decides is the module with its
arguments: a statement naming a shareable module, whose arguments are each one an import may pass
([9.2 Imports](#92-imports)), is an `import`, and any other is a `run`. Importing a module that is
not shareable is an error at the `import`, naming what its top level requires or causes. Running a
shareable module with arguments an import could pass is an error at the `run`, so a reload that
makes a module shareable makes its runs imports ([9.18 Reloading a program of
modules](#918-reloading-a-program-of-modules)). A run passed as an
argument carries its state into the module it is passed to, which an import cannot share, so
`run shop(counter=c)` with a run `c` is legal whatever `shop`'s top level does. The check is per
module: a module that serves a route or holds a run's state is run, whatever else it exports.

- **A top level that opens a source or takes a reading requires `ObserveWorld`,** and one that binds
  a sink causes `AffectWorld`. Its module is run.
- **A transactional mutable variable makes its module a run.** Its declaration writes it, which
  causes `WriteTxn(x)`, and no construct discharges that.
- **So does a public feed.** Other modules append to it, so declaring it causes `Append`, which
  the top level's end does not discharge.
- **An induction variable and a private feed do not.** Each one's history ends with the top level,
  so its writes are discharged there, and a module whose only state is induction variables and
  private feeds is shareable when nothing else makes it a run. A public function that reads or
  writes an induction variable names it past its scope, which is an error
  ([9.10 Induction variables stay in their module](#910-induction-variables-stay-in-their-module)).
  A public function that appends to a private feed makes the feed the run's, as a public feed is,
  since appends commute and have no order to lose across modules.
- **`@LoadFrom` is outside this model.** A loaded declaration
  ([8.8 `@LoadFrom`](#88-loadfrom)) binds a plain value the version it replaces carried across the
  reload, which its top level neither requires nor causes, so a load makes no module a run.
- **A `run` statement requires and causes what its module's top level does,** so a module that runs
  another is run.
- **A top level from which an exception escapes is an error,** imported or run
  ([Exceptions](#exceptions)).

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
| `Txn` mutable variable | **[Planned]** `name: Mut(V, Txn)` |
| member bound to a module, `pub audit = a` | `name: Module{…}`, the Module type of the module it is bound to |
| type alias | `Name = T` for an exact type, `Name <: T` for one known through a bound, or `Name: K` for one known through its kind, any of them followed by a `requires` clause on it (**[Decided]**) |
| nominal type | `Name = T`, where `T` is the nominal type |
| private member | none |

A capitalized entry is a type member. Its `<:` and its `requires` clause are the bounds of a type
parameter ([9.4 Parameters](#94-parameters)), and the entry is the one place `<:` appears inside a
type literal ([Two annotation forms: exact and bounded](#two-annotation-forms-exact-and-bounded)).
`Name: K` states its kind, as `T: K` does for a type parameter, so `Name: Type` is any type
([Kinds and bounds](#kinds-and-bounds)). A module reaching a type member through a Module type
knows what its entry states and nothing more. Through `Name = T` it can build values of the member,
and through `Name <: T` or `Name: K` it cannot. A type member is in scope in the entries after it,
which is how `charge` above returns a `Receipt`.
**[Decided]** `Module{Receipt requires Identified(Receipt), charge: {amount: Int} => Receipt}` is met by a run
whose `Receipt` has an instance of `Identified`.
An entry's clauses write the private transactional state of the module the type describes as
`Module::*`, and a run's state is the parameter's through it: `counter::*` for a parameter
`counter`, and `counter::stock` for its entry `stock: Mut(V, Txn)` (**[Planned]**)
([Discharging requirements and effects](#discharging-requirements-and-effects)).

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

An import name denotes its shared import, and a run name its run, as a Module value in two positions
only: an argument, and a binding, `pub audit = a` ([9.3 Runs](#93-runs)). A Module value stored in
data or returned from a function is **[Open]** ([9.20 Open questions](#920-open-questions)). A
Module-typed parameter therefore names exactly one shared import or run in each copy of its module.
A `Txn` member reached through it is a bare variable reference, as through a run name
(**[Planned]**).

### 9.9 Running

Each run performs its module's top level, with its parameters bound to its arguments:

- Its mutable variables and feeds are its own. `eu::stock` and `us::stock` are two variables.
- Its sources open and its routes serve while it runs. The `(port, method, path)` triple of every
  route is unique across all runs. A conflict is an error at both `run` statements.
- Its own runs run with it, and their run paths extend its own.

Runs share state only by being passed: a module passes one run to others as an argument. A shared
import holds no state that outlives its top level
([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)):

```python
run audit
run storefront(port="8080", audit=audit) as eu
run storefront(port="8081", audit=audit) as us   # eu and us feed one `audit::events`
```

A program of modules means what the same code means written in one file, with each member spelled
by its qualified name. For mutable state, modules add visibility and nothing else:

- **[Planned]** A public mutable variable is a `Txn` variable. It is read and written through a
  qualified reference inside a `with begin():` block, or in a function a block calls ([8.3
  Reads](#83-reads)), and `await_final(eu::stock)` reads its final value ([8.6
  `await_final`](#86-await_final)). `=` does not rebind one.
- **[Planned]** A qualified reference is a bare variable reference, so `eu::stock` may be passed to
  a `Mut` parameter under the downward-only discipline of [8.1 Mutation is explicit: the `:=`
  operator](#81-mutation-is-explicit-the--operator).
- **[Planned]** A Module type's entry `stock: Mut(V, Txn)` is the variable of the run passed for the
  parameter, not a copy: `p::stock := e` writes the argument's `stock`. `Mut` is invariant, so the
  argument's variable has value type `V` exactly.
- A public feed is fed and read through a qualified reference. Append merges commutatively, so
  several writers are a feed's semantics.
- A module that keeps its state private and exports functions over it relies on functions that
  capture mutable variables ([4.1 `def` — function definition](#41-def--function-definition)) and
  that run inside their caller's transaction
  ([8.7 Transactions as contextual parameters](#87-transactions-as-contextual-parameters)).
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

The qualifier is `this`, an import name, a run name, or a member bound to one of them. Record and
variant types stay structural ([3.15 Variant constructors](#315-variant-constructors)), and two
modules agree on a type by naming the same labels. `{audit_api::app: String}` written in
`storefront` is the type `audit_api` writes as `{app: String}`. Within one file this changes
nothing.

- **[Open]** — a syntax that aliases another module's label or tag, so the importer writes it
  unqualified.
- A sum or product that several modules share is declared as a nominal type. The constructors of a
  constructor list belong to the type and their parameter names are not labels
  ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)), so another
  module writes `Shape::circle(1)` with no qualified tag or label. `Option` is such a type, in a
  std module ([9.16 The std root](#916-the-std-root)). A record in the single-constructor form
  `type N = R` keeps its labels, which belong to the declaring module like any other:
  `shop::Price::new(shop::amount=3)` and `p.extract().shop::amount`.
- **[Open]** — which module owns the labels of data from outside the program, such as the fields
  of an HTTP request body.

A module's type members are its type aliases and its nominal types
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). Exporting an
alias exports a spelling for a structural type, and the user's type is the same type. Exporting a
nominal type exports the type itself: `mod::Price` is one type in every module that names it, and
distinct from every other type of its shape.

#### Nominal type identity

A nominal type is identified by its module path, its name, its type arguments, and the arguments of
the module parameters its declaration depends on ([9.4 Parameters](#94-parameters)). The type is
one for each set of arguments those parameters take, whether an import or a run passes it. An import
reaches a type through its import name and a run through its run name, and two spellings name one
type exactly when those parts agree.

- **A declaration's identity includes the argument of every module parameter it reaches.** It
  reaches a type parameter of its module by naming it, by naming another type of the module that
  reaches it, or through an associated function that reaches it, since the function then has types
  of its own at each set of arguments. A function reaches a type parameter that its signature or
  body names, or that a binding or function of the module it reads reaches, as `wrap` reaches `T`
  through `id`:

  ```python
  param T
  def id(x: T) => T: x

  type Box = Int
  def Box::wrap(self, x): id(x)
  ```

  Each such parameter is an implicit parameter of the type, and the argument an import or a run
  passes fills it.

  Two imports given different arguments reach different types:

  ```python
  # shop.cambra
  param Receipt
  type Price = {Int where _ >= 0}
  type Order:
      placed(receipt: Receipt, total: Price)
  ```

  ```python
  # deploy.cambra
  import shop(Receipt=stripe::Receipt) as eu
  import shop(Receipt=paypal::Receipt) as us
  ```

  `eu::Order` is `shop(Receipt=stripe::Receipt)::Order`, as a diagnostic writes it, and differs
  from `us::Order`. `Price` reaches no parameter, so `eu::Price` and `us::Price` are one type. A run
  passing `Receipt=stripe::Receipt` reaches the same `Order` as `eu`.
- **A declaration also reaches a `const` parameter.** Its refinements name only `_` and constants
  ([9.19 Constants](#919-constants)), and it reaches each `const` parameter they reach, a constant
  binding through its definition. **[Planned]** — through a function its refinement calls, its
  body and every function that body calls.

  ```python
  const param max_rate: Int
  limit = max_rate * 2
  def valid(r): r <= limit

  type Rate = {Int where _ <= max_rate * 2}   # names the parameter
  type Capped = {Int where _ <= limit}        # reaches it through `limit`
  type Checked = {Int where valid(_)}         # [Planned]: through `valid`'s body, then `limit`
  ```

  All three reach `max_rate`. A constant that reaches no parameter, such as `ten = 10`, is the same
  at every set of arguments. A value parameter without `const` is no constant, so no declaration
  names it and it never enters a type's identity.
- **A declaration reaches no state and no source.** No constant reads a mutable
  variable, a feed or a source, so a value that met the declaration when built meets it for as long
  as it lives. `InStock = {String where _ in stock.keys()}` therefore stays an alias.
- **Type arguments compare by type equality.** A type argument may be structural: two imports
  passing `{id: String, card: String}`, one through an alias and one written out, reach one `Order`.
  A type argument compares the same whether written or inferred at the `import` or `run`.
  **[Planned]** A Module argument compares by the shared import or run passed.
- **A `const` argument compares by value.** Linking fixes every import's and run's arguments, so
  `import shop(max_rate=30)` and `import shop(max_rate=10 + 20)` reach one `Capped`. In a module
  checked alone ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)), an
  argument that reads one of that module's own `const` parameters has no value yet and compares by
  the parameter: two runs passing `max_rate=r` reach one type, and `max_rate=r` and
  `max_rate=r + 0` reach two.
- **[Open] — comparing refinements.** Whether `{Int where _ >= 0}` and `{Int where 0 <= _}` are
  one type is undecided, both as type arguments and for an alias whose refinement names a
  top-level binding ([6.4 Refinement syntax](#64-refinement-syntax)), since
  [6. Types (informal sketch)](#6-types-informal-sketch) defines equality for records and variants
  but not for refinements.
- **A module is checked once against every argument.** Inside `shop`, `Receipt` is opaque, so the
  functions of `Order` hold for every argument's `Receipt`
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)). A shared import takes
  its module's default arguments, and a `run` passing the same arguments reaches the same types.

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
runs that check and prints the module's interface. No other module names the module's
private transactional variables or the state of the runs it declares, so the interface writes their
reads and writes `ReadTxn(Module::*)` and `WriteTxn(Module::*)`, as a Module type of the module
would, and a public variable by its name (**[Planned]**). **[Planned]** — the interface writes each
type with the alias names its module wrote: a member annotated `base: Count` is printed `base:
Count`, not with the type `Count` names.

- **Parameters are typed binders.** A value parameter has its annotated type, with each `_` in it
  the type its uses infer. A type parameter is opaque apart from its bound. One with no bound is
  **coupled** to its arguments: the module's uses of it are checked at each argument. The interface
  states which value parameters are `const` and which public bindings are constants
  ([9.19 Constants](#919-constants)).
  **[Planned]** — and which public functions may be called in a constant.
- **Imports are read through contracts.** A module sees each member another module exports through
  its contract, and whether the module is shareable
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)).
  A function's contract includes its `requires` and `causes` clauses.
- **A public member's contract is its type.** An exactly annotated member's contract is the
  annotation, checked against the body, and a module using the member reads no body. An unannotated
  member's contract is its inferred type, refinements and all, and a `<:` member's is its inferred
  type below the bound. An inferred type depends on the body, so a module using such a member is
  checked together with the member's body. Such a member is **coupled** to its uses.
- **A run is checked at the `run` statement.** Each value argument is checked against its
  parameter's type, and each type argument against its parameter's bound. A `const` parameter's
  argument is checked to be a constant. A module argument's
  members are checked against the parameter's Module type: each value member against its entry,
  and each type member equal to an exact entry `Name = T`, or below a bound. A parameter whose
  annotation's `_` its uses leave open, as `k * k` leaves `param k: _`, is **coupled** to its
  arguments, as an unannotated member is to its uses.

The check covers parsing, name resolution, and typing, plus the module's own `run` and `import`
statements: their arguments ([9.3 Runs](#93-runs)). Its guarantee: **a module that checks cannot be
made to fail, in any of these, by a use that checks through members whose contracts are exact
annotations.** Every error such a use causes is reported at the use, against the annotation, with a
secondary label at the library line the requirement comes from. An error a use of a coupled member
causes in that member's body is reported at the body, with a secondary label at the statement that
brings the body into the using module.

Some checks run only once the program is assembled from its root, because they need the bodies of
called functions or the full set of runs: the mutable-variable and transaction rules of
[8. Mutability, transactions, and feeds](#8-mutability-transactions-and-feeds), feed routing, the
dataflow shapes the compiler can emit, and route uniqueness across runs. So do the uses that
several modules make of one coupled member together, such as a monomorphic member that two
importers settle. One of these can refuse code inside a module that checked. The error is reported
at the code it names, with the run whose copy failed, and with a secondary label at the `run`
statement that created that run, or at each `import` that reaches a shared import.

An inferred contract changes when its body changes. Every user in the engine is rechecked on reload,
so a breaking change surfaces there. A library author sees it in the interface `cambra check`
prints. An annotation is how an author fixes the contract.

When a check reports errors, it also prints the export contracts it established and exits with a
failure status. An omitted definition with no complete declaration supplies no export contract.

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
- The match is case-sensitive, including on a case-insensitive file system, and so is the root
  file's name. `import cart` does not load `Cart.cambra`, and naming `deploy.cambra` as the root
  does not read `Deploy.cambra`.
- Two module paths resolving to one file, through a symlink for example, are refused. The file would
  have two identities, and two shared imports.

### 9.16 The std root

**[Planned]** — the rules of this section, apart from `@Builtin` below, which is **[Decided]**.

The compiler's own modules live under a **std root**, and every std module's path begins with `std`:
`import std::http` binds `http`, then `http::serve(…)` and `http::ok(…)` ([7.3
Sources](#73-sources)), and `import std::time` binds `time`, then `time::now()` and
`time::alarms()` ([7.5 Time [Decided]](#75-time-decided)). A path beginning with `std` names a
module of the std root and never a file under the module root, so `std` is the only name the std
root reserves, and adding a std module changes no user module's meaning. `std` alone names no
module, and a root file named `std.cambra` is refused.

A builtin source, sink, or special form a std module provides is recognized by what a name resolves
to, not by how it is spelled. After `import std::http as web`, `reqs, resps = web::serve(…)` is the
same form as `http::serve(…)`, and the bare name `http_serve` is gone. Its address arguments are
constants ([9.19 Constants](#919-constants)), so a module that serves a route takes its address as
a `const param` and each run serves its own.

The prelude (`sum`, `max`, `groupby`, `stdin`, `box`, `begin`, …) stays unqualified and in
scope in every module.

**`@Builtin` marks a declaration whose behaviour the compiler supplies.** Only a std module
declares one, and its declaration states its type. A `@Builtin def` is a signature with no `:` and
no block, and its clauses are exact, as a written function type's are
([Writing requirements and effects](#writing-requirements-and-effects)). The compiler supplies the
value of each call, and finds the function by its path. `std::time` declares its clock this way,
and its `now` wraps the reading in an `Instant`:

```python
@Builtin
def clock() => Int requires ObserveWorld

pub def now() => Instant:
    Instant::new(clock())
```

**[Decided]** — `Option` is a `type` declared in a std module, and is in the prelude
([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)). Builtin
operations that answer an `Option`, the lookup `c[k]` and the unwrap `e!`
([3.9 Subscript and attribute access](#39-subscript-and-attribute-access)), refer to that
declaration. `Set`, `Map` and `FullMap` stay compiler builtins, as nominal types with no
constructors
([6.3 Direction: collection types [Decided]](#63-direction-collection-types-decided)).

### 9.17 No trailing expressions

**[Planned]** — the rules of this section.

A trailing value expression is an error in every module, since what a module does is its sinks. A
script-shaped root therefore needs an output sink, which [10. Sinks](#10-sinks) does not yet define.

### 9.18 Reloading a program of modules

**[Planned]** — the rules of this section.

A reload replaces the source of every module, the root's included, and the running program carries
its state across ([8.8 `@LoadFrom`](#88-loadfrom)):

- **State belongs to runs.** Each run's state is its own. The new version evaluates a shared
  import's top level again, which reads nothing from outside the program
  ([9.7 Importing asserts a shareable module](#97-importing-asserts-a-shareable-module)), and its
  loaded declarations pair by its run path as a run's do. A reload pairs the runs of the two
  versions by run path. A run the new version adds starts from its declared initial values. A run
  present in both takes over its state, whether its module's source, its arguments, or both changed.
- **Removing a run is deleting stateful code.** A reload that drops a run holding state is refused
  unless the new version marks the removal with `@Discard`
  ([8.9 `@Discard` [Decided]](#89-discard-decided)), as it must for any deleted variable:

  ```python
  @Discard
  run storefront as us          # everything `us` held is intentionally gone
  ```

- **A module that becomes shareable is imported.** A version that removes the last of what made a
  module a run, such as its last transactional variable, must import it where the version before
  ran it, since running a shareable module is an error
  ([Shareable modules](#shareable-modules)). Each run that change drops is a removed run: one that
  held state is marked `@Discard`, as above.
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

#### Reloading a nominal type

A stored value of a nominal type carries over a reload when the new version declares a compatible
type. Comparing the constructors' parameter types alone is not enough: two versions of
`type Price = {Int where _ >= 0}` that differ only in the refinement hold the same `Int`, and a
stored `0` must not become a `Price` the new refinement excludes.

- **The type continues by name.** The new version declares a type of the same name in the same
  module, or one marked `@RenamedFrom` with the old name: `@RenamedFrom(Price)` for a rename, and
  `@RenamedFrom(old_mod::Price)` for a move to another module.
- **Every old constructor continues.** For each constructor of the old type, the new type has one
  of the same name, or one marked `@RenamedFrom` with the old name on the line above it. Its
  parameter types are supertypes of the old one's, compared under the arguments of each run that
  holds such a value ([Nominal type identity](#nominal-type-identity)). Refinements are compared
  with the rest, so a tightened refinement is refused. A recursive type is compared assuming the
  pair under comparison compatible.
- **Adding constructors is compatible.** Removing one, or renaming one without `@RenamedFrom`, is
  refused as a change of the variable's type is ([8.8 `@LoadFrom`](#88-loadfrom)).
- **The swap rewrites a renamed constructor in stored values.** A value names its constructor
  ([A nominal type is opaque](#a-nominal-type-is-opaque)), and a constructor marked
  `@RenamedFrom(circ)` takes over every stored `circ` at the swap, which writes the new name into
  each value. A later version reads the value under the name its predecessor declares, and needs
  no record of earlier renames.
- **A run argument that a stored type mentions is part of that state's type.** Changing `eu`'s
  `Receipt` argument while `eu` holds an `Order` is refused unless the old `Receipt` is a subtype of
  the new one.
- **A change to the type's parameters is compared at instantiation.** A variable holding a value
  of the type has a concrete type in each version: the old declaration at its old arguments, and
  the new declaration at its new ones. The rules above compare those two, constructor by
  constructor, so adding, dropping or reordering a parameter needs no rule of its own.
  `type Box: boxed(Int)` becoming `type Box(T): boxed(T)` carries over a variable now declared
  `Box(Int)`. A change of variance changes no stored value; the new version's compile checks the
  uses it affects.
- **A change that no subtyping covers is a conversion.** The new version keeps the old declaration
  unchanged and declares the new type under another name, loads the value at the old type with
  `@LoadFrom`, and converts it. A later version deletes the old declaration once no state holds it,
  and may give the new type the old name with `@RenamedFrom`.

**[Open] — reload decorators that stay in the source.** A deployment applied twice should reach the
same result, so a version that keeps `@RenamedFrom`, `@LoadFrom` or `@Discard` from an earlier
reload could be accepted, as long as each decorator was valid against the version it was written
for and the new version is valid. [8.8 `@LoadFrom`](#88-loadfrom) instead refuses a migrating
source recompiled unchanged, because the name it loads is gone. How a later version tells a
decorator already applied from one that names nothing, such as a mistyped `@LoadFrom`, is
undecided.

### 9.19 Constants

A **constant** is a value fixed once the program is linked. It reads no source, no feed and no
mutable variable, so it holds one value for the life of a run, whatever data arrives. `const` marks
a parameter whose argument must be one ([9.4 Parameters](#94-parameters)). A binding carries no
marker: it is a constant when its definition is one.

```python
const param max_rate: Int
limit = max_rate * 2

pub type Capped = {Int where _ <= limit}
```

- **A constant expression** is built from literals; constant bindings and `const` parameters in
  scope, including another module's public constant binding, `cfg::port`; operators, a ternary,
  and record, tuple and list literals over constants, and a field or element of one.
  **[Planned]** — calls, with constant arguments, to functions that may be called in a constant.
  A type, an import name and a run name are fixed at link time as well, and stand where a type or
  a module is expected.
- **A top-level `=` binding is a constant when its definition is a constant expression.** `limit =
  max_rate * 2` is one, and so is `cap = scale(limit)` for a `scale` that may be called in a
  constant (**[Planned]**). A binding that is not a constant is an ordinary value wherever no
  constant is required. Read where one is required, it is an error at the read that names what its
  definition reads. A mutable variable, a value parameter without `const`, and a function are never
  constants.
- **A `const` parameter is the only binding a run gives a constant**, since the obligation falls on
  every `run` and `import` of the module, and a module checked alone states it in its interface
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)). `const` before any
  other statement is an error.
- **[Planned]** **A function may be called in a constant when its body reads only its own
  parameters, constants,
  and functions that may be, and it requires nothing and causes nothing**
  ([6.9 Capabilities](#69-capabilities)). Requiring and causing nothing is not
  enough alone: a function that captures a value the run computes is not one. A call computes the
  function's body with each parameter its argument. **[Planned]** — a body holding more than `=`
  bindings and its value, each a constant expression over the parameters, and a call of a prelude
  function such as `sum`. Functions carry no marker. The check follows a `def` through its body and
  every function that body calls, and reads an imported function through its module's interface,
  which records whether each public function may be
  ([9.14 Checking a module on its own](#914-checking-a-module-on-its-own)). A call to one that may
  not is an error naming the binding, source, feed or mutable variable its body reads.
- **A read of a constant is known to be the constant**, in a module checked alone too, where a
  `const` parameter has no value yet. There `Capped::new(max_rate)` meets
  `{Int where _ <= max_rate}`, and in a module that writes `run shop(max_rate=r + 1) as a`, a value
  of `{Int where _ <= r + 1}` meets `a::Capped`'s refinement.
- **A constant is required where the language needs a value at link time:** in a refinement in a
  `type` declaration, whose names other than `_` are constants
  ([Nominal type identity](#nominal-type-identity)); and as a `const` parameter's argument
  ([9.4 Parameters](#94-parameters)) and a route's address
  ([7.3 Sources](#73-sources)). **[Decided]** — as an import's argument
  ([9.2 Imports](#92-imports)).

### 9.20 Open questions

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
- **Discarding and redeclaring one address.** A version that both writes `@Discard stock` and
  declares `stock` could mean a reset to the declared initial value, or be an error.
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

A sink is any operation that hands data out of the program, and each causes `AffectWorld`
([Output outside the program](#output-outside-the-program)). Binding a feed to a sink is one.
**[Decided]** — so is calling a sink function that takes a collection and writes it out: feeds are
one way to build the collection, not the only one.

## 11. Errors and recovery

### 11.1 Lex errors

The lexer reports seven error kinds, every occurrence of each, and still emits a token stream the
parser reads, so a lex error does not stop parsing.
[chl-parser/design-chl-parser.md](../chl-parser/design-chl-parser.md#lexer-recovery) specifies
the stream each error leaves.

- **`InvalidToken`** — no token rule matched at the position.
- **`UnterminatedString`** — a string literal's line ended before its closing
  quote ([1.7 Literals](#17-literals)). The span is the opening quote.
- **`DetachedBacktick`** — a backtick not immediately followed by an
  identifier ([1.8 Operators and punctuation](#18-operators-and-punctuation)).
  The span is the backtick.
- **`UnmatchedClose`** — `)`, `]`, or `}` that matches no open bracket.
- **`UnclosedBracket`** — an open `(`/`[`/`{` the source never closes. The span is the open
  bracket.
- **`MismatchedClose`** — `)`, `]`, or `}` of another kind than the innermost open bracket,
  where that open bracket is never closed. The span is the close bracket; the error also names
  the open bracket.
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
- Type mismatches (e.g. comparing values of incompatible types,
  feeding a name that is not a feed).
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
- **First-class functions in arbitrary positions** — a function may be
  bound, passed, and held in a product field, and each call must resolve
  to it statically ([3.8 Function calls](#38-function-calls)). A function
  that no call consumes, such as one stored in a collection or returned as
  the program's result, is not supported. See the 2026-03-05
  first-class-functions design notes.
- **Recursion** — self-reference in `def` is not yet wired through;
  self-referential *value* bindings get the explicit `rec` form
  (**[Decided]**, §4.3).
- **Imports / multiple files** — modules, imports, runs, and parameters
  are specified in [9. Modules](#9-modules).
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
- **Destructuring patterns** beyond tuples, `_` and constructor patterns — record and variant
  patterns in assignment targets and binders (a `match` arm's tag or constructor pattern is §4.10),
  a pattern in a constructor pattern's parameter, and per-component annotations with `:` binding
  tighter than `,` (**[Decided]**, §4.3.1).
- **Unit values do not run** — the type surface is settled (`{}` for the type,
  `()` for the value, §6.6) and both typecheck, but a unit-valued program
  output cannot be materialized by the interpreter: it has no column
  representation, so `x = ()` compiles and then fails at runtime. This is a
  runtime gap, not a surface one.
- **The term-level delimiter migration** — record values are `(f=1, …)`, and `{…}` no longer
  denotes a term-level value (it is record-type / tuple-type / unit syntax,
  [2.4 Atoms](#24-atoms)). The map literal `[k -> v, …]` parses, and `map([…])` is the only reading
  of it as a `Map` (**[Decided]**, [3.11 List, tuple, record literals](#311-list-tuple-record-literals)).
  Earlier plans to spell the entries `[k: v, …]`, `[k=v, …]`,
  or Unicode `[k ↦ v, …]` are superseded by the map-literal decision.
- **Map comprehensions** — `[k -> v for …]` is a comprehension of pairs, and reading one as a
  `Map` is `map([k -> v for …])` ([3.12 Comprehensions](#312-comprehensions)).
- **Nominal types** — a recursive `type` declaration, `@RenamedFrom` on a type, and carrying a
  value of a nominal type over a reload are **[Decided]** and unimplemented
  ([6.8 Nominal types and methods [Decided]](#68-nominal-types-and-methods-decided)).
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

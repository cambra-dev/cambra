# CCL IR — the typed AST

CCL is the typed expression tree between CHL source and the dataflow operator graph. Lowering
constructs `TypedExpr` nodes, inference resolves their `Type` slots, and later passes transform the
tree before operator conversion. This document specifies the node vocabulary and the invariants
needed to read or transform it. See the [design index](README.md),
[lowering](lowering.md), [type inference](type-inference.md), and
[optimization](optimization.md) for the surrounding passes.

---

## Key design decisions

### Purity invariant: CCL is a pure value language

Every `TypedExprNode` denotes a value. Type inference, rewriting, and planning may duplicate or
reorder expressions; a node therefore cannot execute I/O or dispatch a sink as a pipeline effect.
`Defer` is a pure placeholder for a deferred output. `LoweringContext` records its sink binding,
and `compile_program` assembles the `SinkConsumer` at the program boundary. Source registrations
follow the same boundary rule. The [CCL invariant](../CLAUDE.md) applies to new node variants.

### Less normalized than ANF

Compound expressions may occur directly inside other expressions. `f(x + y)` can be represented as
`(x + y) ▷ f`; no `Let` is required between the addition and the application. `Let` names a value
when the lowering or a later pass needs a shared binding or a scope. The tree is less normalized
than strict A-normal form, leaving nested expression structure available to later rewrites.

### Structured names and α-uniquification (Barendregt convention)

`Name` distinguishes source spellings, minted binder identities, compiler binders, and references
inside dependent types (`ccl/names.rs`):

| Variant | Identity and use |
|---|---|
| `Raw(String)` | Source spelling before uniquification; lexical scope distinguishes equal spellings. |
| `Unique { base, uid, home }` | Source binder minted by `uniquify`; `uid` distinguishes binding sites, while `base` retains the source spelling and `home` the imported module or run whose top-level member it binds ([docs/modules.md, "Names carry their home"](../../../docs/modules.md#names-carry-their-home)). |
| `Synthetic { kind, uid }` | Compiler binder with a fresh `uid`; `kind` identifies its origin (`Pair`, `Mono`, `FloatedDefer`, `SolverArg`, or `Component`). |
| `Reserved(ReservedName)` | Special name; the shared refinement-element binder is `__elem`. |
| `PiBound(PiRef)` | Bound reference in a function type's codomain; its de Bruijn index determines equality, while its spelling hint is display metadata. It is never a term binder. |

Lowering can produce two `Let` binders spelled `x` for successive source assignments. The
`uniquify` pass mints an identity for each source binding site and resolves bound uses according
to lexical scope. A reference to the second binder then differs from a reference to the first,
even though both display as `x`. `Unique` and `Synthetic` draw identifiers from the same fresh-id
space; a synthetic name records compiler origin rather than claiming a source declaration.

Structural comparison of copied, already-minted terms preserves binder identity. Independently
lowered α-equivalent terms can have different `uid`s and need not compare equal. The comprehension
phase therefore runs after `uniquify`, so the generator source it copies into a loop-join predicate
is already minted and the copy keeps its `uid`s. Lowering's own copies, such as a chained
comparison's middle operand, are taken before `uniquify`, which mints each copy separately.
Linking uniquifies each run's copy of its module's chain alone, with the members its qualifiers
reach and the module's `use` names beneath its binders ([docs/modules.md, "A module lowers
once"](../../../docs/modules.md#a-module-lowers-once)).
`uniquify` does not mint again at an already-minted binding site, so a predicate shared by `Rc`
keeps one `uid` at every site it occupies. No pass may mint fresh uids on an equality-mediated path:
copying must preserve the identities that refinement deduplication and other structural comparisons
use. Within this mint-once, copy-preserving representation, structural comparison implements the
α-equivalence checks without another scope analysis. It does not identify independently minted
α-equivalent trees.

Copies keep their binders' identities, so two copies of one binding site can meet in one scope:
a specialization clone's argument and the body of another clone of the same definition, or two
copies of one value under one writer. A rewrite that moves a `let` binder into a scope it did not
occupy therefore renames it first (`refresh_let_binder` in `ccl_utils.rs`): the binder gets a fresh
`uid` of the same kind (`Name::refreshed`), and its reads follow, in terms and in type slots. The
kind stays because later rules read it, such as `Name::is_anf_temp`.

At the post-`uniquify` checkpoint, every binding site must be `Name::Unique`, not merely a minted
name. A surviving `Synthetic` binder there indicates that a pass minted it too early. The check
does not require globally distinct uids, since copied binding sites retain their original identity
(`assert_all_binders_minted` in `uniquify.rs`).

`Name::base()` is for display. Scope and identity checks use the variant and its fields, such as
`is_elem()` for the reserved refinement binder. Dependent function types close references to a
`PiBound` index; its hint can differ between references that compare equal. See
[type inference](type-inference.md) for the locally nameless refinement representation.

### Binding structure lives in one place

`ccl/scope.rs` defines term binding with `for_each_scoped_item`. It yields direct children with
their enclosing binders and yields the name occurrences made by the node itself. Free-variable
analysis, `Subst::rewrite_expr` and inference's `check_scope_valid` use that walk. The scope rules
are:

| Node | Binder scope |
|---|---|
| `Lambda` | `param` binds in `body`. |
| `Let`, `MutDecl` | `binding` binds in `body`; `bound_expr` or `init` is outside its scope. |
| `LetRec`, `DefGroup` | Every group binder binds in every definition and in `body`. |
| `For` | `position` and `target` bind in `body`, and `target`'s type is in `position`'s scope; `iter` is outside their scope. |
| `Case` | A branch pattern's payload binder binds in that branch's `guard` and `body` only. |
| `Comprehension` | A generator's `target` binds in its own `guards`, in every later generator, and in `element`; its own `iter` is outside its scope. |
| `Feed`, `Define`, `MutWrite` | `name` is a use of an enclosing binder. |
| `Transact` | Keys and writer footprints are history-record labels, not variable uses; the node binds nothing. |

`Binders` borrows binder slots without allocating a list and implements the `shadows` check for
each child. A comprehension's binders come into scope one generator at a time, so its covering
scope is a prefix of its generators (`Binders::Generators`) and the prefixes nest: each scope
extends the one before it, and the last one matches `walk_binders`. Every other node's scopes are
disjoint, and their concatenation matches `walk_binders`. `Transact` labels are emitted as `KeyRef`,
distinct from the `VarRef` occurrences that free-variable analysis counts. A node's type slots and
their refinement predicates require the caller's type walk; the term-scope walk does not traverse
them.

The immutable walk lists children in `TypedExpr::walk_children` order. It groups each binder's
children consecutively, so `for_each_scoped_item_mut` can announce a scope once and pair it with
the mutable child walk. Tests in `scope.rs` check child order, name occurrences, and agreement with
`TypedExpr::walk_binders`. The scope and binder enumerations are exhaustive over node variants;
adding a binding form requires declaring its scope and its binder slot. `uniquify` walks its own
mutable environment because it mints names before descending, but checks its result against
`walk_binders`.

`Subst` is simultaneous: a replacement is not substituted into another replacement during the
same application. `Subst::rewrite_expr` restricts mappings under binders that shadow their keys
and asserts that a replacement cannot be captured by a crossed binder. Its in-place discharge
keeps the replaced occurrence's root `NodeId` and freshens replacement interiors. Transport mode
(`Subst::apply_expr_inner`) constructs a new tree and records new node identities. Both modes
visit refinement predicates in type slots as well as expression children. A substitution may be
vacuous in the expression children yet still affect a predicate or a witness reference in a type.

### Every stored type is well-scoped

Every type slot is well-scoped at every phase: each name free in it is bound by a term binder
around the slot's node, or is one of the program's free names, its sources and sinks. The term
binders are the ones [Binding structure lives in one place](#binding-structure-lives-in-one-place)
lists. Inside a type, that type's own binders bind too: a Pi binder over its codomain, a dependent
tuple's component over the components after it, `__elem` over a refinement's predicate, and a
quoted term's binders over that term. A sum binds its witnesses within its own type and nowhere
else, and a generalized type's `Poly` binds its type parameters within that type and nowhere else.

The rule does not change from phase to phase. Lowering and elimination change which form a term
takes, not what binds where:

- A morphism's binder binds within the morphism's own type. A morphism after it in a chain names
  no binder of an earlier one
  ([A chain names each position](type-inference.md#a-chain-names-each-position)).
- A morphism lambda elimination lifts out of a parameter's scope receives in its input every value
  its term reads. Where only its type reads the parameter, through what the morphism receives, its
  type is generic in that part ([Generalized types](type-parameters.md#generalized-types)).
- A view of a collection before lambda elimination is written with its position bound,
  `λ 𝑟 → 𝑟 ▷ __hist ▷ 𝑠₁ ▷ … ▷ 𝑠ₙ` (`ccl_utils::pointwise_view`), as a loop over a collection is
  (`λ 𝑟 → (𝑟 ▷ 𝑥𝑠) ▷ (λ 𝑥 → body)`).

An opaque `let`'s name is the one exception, and only until mutability elimination. While
inference runs, a read binder's definiens is a mutable variable no type may name, so a type lifted
past the `let` keeps the binder's name (`Typing::close_let_type`). Mutability elimination names the
value each read took and makes every opaque `let` transparent
([A read is named while inference runs](mutability.md#a-read-is-named-while-inference-runs)).

[dependent-types.md](dependent-types.md) maps the forms that bind inside a type.

`well_scoped::assert_well_scoped` checks the rule in debug builds at every boundary `settle`
checks, type parameters included, and `infer::debug_assert_no_free_witness` checks witnesses.

### Source locations on substituted parameter projections

An ordinary multi-parameter `def f(p, q)` lowers to one lambda over a tuple parameter.
`uncurry_params` substitutes a projection for every use of `p` or `q`:

```
λ __arg_tuple_0 → __arg_tuple_0.0 + __arg_tuple_0.1
```

The original parameter has no `TypedBinding` in that shape. The outer `Apply` of the substituted
projection keeps the parameter occurrence's `NodeId` and source span. Its `Proj` child carries the
parameter declaration span from the substitution template. A definition lookup can therefore
distinguish the use site from the declaration. The test
`a_substituted_parameter_carries_occurrence_and_declaration_spans` checks both spans.

Replacing each parameter with an inner `let p = __arg_tuple_0.0` would introduce `Let` nodes
that lambda elimination lifts to function-valued bindings. The resulting `zip(.0, .1)`-shaped
morphisms need reductions that simplification does not implement. Direct projection substitution
avoids that unsupported form, as specified by `substitute_params` in `lower/functions.rs`.
Scope exit is a separate mechanism: inference discharges an ordinary `let` definition into result
refinements when they leave its scope (see
[`let` binders and scope exit](type-inference.md#let-binders-and-scope-exit)). A function with a
`Mut` parameter still uses named curried binders because a mutable write needs a named target.

### Application shape

`Apply` has one function child and one argument child; its symbolic form places the argument first:
`𝑎 ▷ 𝑓` means `𝑓(𝑎)`. A one-argument CHL call uses one `Apply`. An ordinary multi-argument call
`f(a, b)` packs `(a, b)` into one argument, matching the tupled parameter lambda. A call to a
function with a `Mut` parameter instead uses chained applications matching its named lambdas.

At the IR level, a curried application forms a chain: `𝑏 ▷ (𝑎 ▷ 𝑓)` has an outer application
whose function is the inner application. CHL call lowering currently requires a named target, so
the source spelling `f(a)(b)` is rejected. Curried functions that survive inlining may require a
`curry` combinator that operator conversion does not currently compile. The ordinary tupled
lowering avoids that form; see [lowering](lowering.md).

### `Comprehension` — the surface comprehension node

`Comprehension { generators, element }` carries `[element for … if …]`: one `Generator` per `for`
clause, holding its `target`, its `iter`, and the `if` clauses that follow it before the next `for`.
Lowering builds it; `ccl/comprehension.rs` is the phase that eliminates it, between `mut_read` and
inference.

The phase is placed there because the encoding below is a refined `Cast`, and A-normalization
leaves a refined cast's value as it finds it: the cast's value and its target's predicate hold two
copies of one generator source, and naming a sub-expression under the cast would rewrite only one
of them (`ccl/anf.rs`, "Five recognition contracts: positions a `Let` must never sit between").
Built at lowering, a comprehension reached inference un-normalized. In surface form its element
normalizes like any other term, and the copy the phase takes afterwards is a copy of the normalized
one.

### Lambda/Apply encoding of collection iteration

Collection iteration uses ordinary function nodes in two shapes. A single-generator comprehension
such as `[f(x) for x in xs]` becomes an outer lambda over an iteration position: `λ __iter_record →
__iter_record ▷ (xs ▷ unbox) ▷ (λ x → f(x))`. The first application reads the source at that
position, through `unbox`; the second maps its element through the body. Several generators build
one collection over tuples of positions ([Several generators](#several-generators)).
`ccl/comprehension.rs` builds both, and the `__iter_record` binder it mints is a `Synthetic`:
α-uniquification has already run, so a raw spelling would shadow its twin in a nested comprehension.
A feed-only or yield-only statement loop without loop-carried mutation is built at lowering as `xs ▷
unbox ≫ (λ x → body)` (`lower/loops.rs`) and indexed by the comprehension phase to the same form, `λ
𝑟 → (𝑟 ▷ (xs ▷ unbox)) ▷ (λ x → body)` (`ccl_utils::loop_parts` reads one). Both forms use existing
function nodes; mutation and transaction loops instead retain a structured `For`. `lambda_elim`
removes the lambdas and produces point-free combinators; operator conversion builds the dataflow
operators. See [lambda elimination](optimization.md#lambda-elimination-ccllambda_elimrs) and the
[operational lowering model](/docs/operational-semantics/lowering.md).

#### Several generators

A comprehension over several generators is the comprehension over the first generator of the
comprehensions over the rest, flattened by `uncurry(𝑛)`:

```text
[e for a in S for b in T]
  ⟹  (λ r → r ▷ (S ▷ unbox) ▷ (λ a → λ r' → r' ▷ (T ▷ unbox) ▷ (λ b → e))) ▷ uncurry
```

`uncurry(𝑛) : ((𝑘₁ : 𝐴₁) ⤇ (… ⤇ ((𝑘ₙ : 𝐴ₙ) ⤇ 𝑉))) ⇒ (((𝑘₁ : 𝐴₁) × … × 𝐴ₙ) ⤇ 𝑉)`, where each
`𝐴ᵢ` may read the keys outside it, turns the `𝑛` nested collections into one collection keyed by
the tuple of their positions, one component per generator; `uncurry` alone is `uncurry(2)`. Where
an inner generator's source reads an outer element, as in `[x for xs in xss for x in xs]`, its
keys depend on the outer key and the tuple is dependent
([type-inference.md, "4.8 Dependent tuples"](type-inference.md#48-dependent-tuples)); elsewhere it
is the plain tuple. Each level is a one-generator encoding.

The filters of every generator form one filter, stated as the same nest over the filter's value,
flattened the same way and read at the element: `__elem ▷ ((λ r → … (λ b → p)) ▷ uncurry(𝑛))` on
a cast of the flattened collection. The filter is a collection keyed as the result is, so reading
it at `__elem` is an application at the domain, which `uncurry(𝑛)`'s scheme types whether or not
the tuple is dependent. It is not split across the levels: join planning reads the equalities
between generators off the one filter over the tuple (`planning/join.rs`). A source that may be a
sum is bound ahead of the whole nest, so the filter's copy of it reads the name its level reads. A
source that reads an outer element is bound ahead of its own level instead, inside the element
binder it reads: the level's domain is the source's projection, and A-normalization would name a
source left in place inside the level, out of the domain's scope.

### `MutDecl` — the mutable variable introduction

`x := init` introduces a mutable variable with `MutDecl { binding, init, body }`. The binder is
live only in `body`; the seed `init` is evaluated outside its scope. `MutWrite` names an existing
mutable variable and optionally carries a key for a keyed write. The mutability phases eliminate
these nodes into a causal `LetRec` or, for sequential positions, shadowing `Let`s.

`MutDecl` is the node that introduces a mutable variable in an expression body. A `Let` over a
mutable initializer binds the value read from it; `b = a` does not create a mutable alias. A
`Lambda` parameter may also bind a mutable history for pass-by-reference calls. This distinction
is structural and remains available after source annotations are cleared by inference. See
[mutability](mutability.md) for read and write rules.

### Type aliases resolve where they are declared

`LetType { name, ty, body }` is the type alias `name = ty` declared over `body`, where `ty` is a
type or a Module type, each of whose entries holds a type ([docs/modules.md, "A Module type is not a
`Type`"](../../../docs/modules.md#a-module-type-is-not-a-type)). It binds no value: lowering
substitutes `ty` at every use, so nothing refers to `name`. The node holds `ty` where the
alias is declared, because a refinement predicate in `ty` reads values, as `Pos = {Int where _ > k}`
reads `k`, and those names resolve in the declaration's scope, not at a use under a local `k`.

Every use shares `ty`'s predicate terms, and uniquify rebuilds a shared predicate once. A use in a
statement lies in `body` ([chl-spec.md, "6.7 Type-alias
statements"](../../../docs/chl-spec.md#67-type-alias-statements)), so uniquify reaches the
`LetType` first and the use takes the resolution made there. Two uses lie outside `body`:

- `nominal::bind_constructors` binds each constructor around the whole module, so uniquify reaches a
  constructor's parameter type first. Lowering refuses a constructor parameter type whose refinement
  names a binding (`lower_parameter_type`), so every predicate reached there is closed and resolves
  the same in both scopes.
- A run's value argument is bound in a `let` above its `Run` node, annotated with the parameter's
  type with the type arguments substituted, and linking puts each type argument's `LetType` where
  that node stood, so uniquify reaches the annotation first. Only the run's other arguments are
  bound between the two, spelled `__run::…` (`argument_name`), which no source writes, so each
  free name resolves the same at both.

A debug build asserts that a use uniquify reaches before its alias's `LetType` resolves each free
name as the `LetType` does. Uniquify then replaces the node with `body`. No pass after it sees a
`LetType`, and each has an unreachable arm for one.

### `Run` — a `run` statement before linking

`Run { name, module, statement, arguments, modules, types, body }` is the `run` statement at
`statement` that declares the run `name` of `module`, over `body`, the rest of the declaring module.
`arguments` names the parameters it passes value arguments for, each bound in a `let` above the
node, and `modules` holds each module argument: its parameter, the module as the declaring module
spells it, and the argument's span. `types` holds each type argument with its parameter and span,
and linking puts a `LetType` of each where the node stood, so uniquification resolves its
refinements in the declaring module's scope. A module lowers once, before any run of it exists, so
the statement cannot stand for the run's chain yet. Linking creates the run and replaces the node
with its chain around `body` ([docs/modules.md, "A module lowers
once"](../../../docs/modules.md#a-module-lowers-once)). No pass after linking sees a `Run`, and each
has an unreachable arm for one.

### `Abstract` — a value known only by its type

`Abstract` is a leaf with no definiens. In a module's chain it is bound by the `let` of a parameter
with no default, or of a member a Module-typed parameter's Module type names ([docs/modules.md,
"Runs"](../../../docs/modules.md#runs)). Each run binds the parameter to its argument, and refuses a
run that passes none, so the linked program holds no `Abstract`.

In a module's check tree it stands for any parameter, or for a member a parameter's Module type
names ([docs/modules.md, "Checking a module on its
own"](../../../docs/modules.md#checking-a-module-on-its-own)). Inference gives it a fresh type, so
the `let` that binds it states its type: an exact annotation binds it at the annotation, and with
none its uses settle it. Under a polymorphic annotation it is generalized as a function definition
is, and each use's copy takes that use's instance. Inference is the last pass a check tree reaches,
so every pass after inference has an unreachable arm for an `Abstract`.

### `Cast` — explicit refinement acquisition

`Cast { value, target }` attaches a refinement to a function's domain. Lowering constructs it for
loop guards and `groupby`, and `ccl/comprehension.rs` for comprehension filters. The emitted target
has the shape `{𝐷 | 𝑝} ⤇ 𝑉`, often with holes for 𝐷 and 𝑉.
The resolved type is written to the wrapping
expression's `ty`. Keeping `target` in the node lets type and predicate walks find it without
treating a call annotation as a hidden operand.

`emit_cast` decomposes the value as a function and rebuilds it with the target's domain
refinements and function kind. The result restricts where the function is used; it does not
establish that an arbitrary scalar satisfies a new predicate. An `Int` to `{𝑥: Int | 𝑝(𝑥)}`
conversion is a value-level narrowing and is outside this rule. The current implementation
honors function-domain refinements, not a general conversion to every supertype. It constructs
the refined-domain function instead of demanding `value <: target`: the refinement relation does
not admit `unrefined <: refined`, and a data-function domain is invariant, so function variance
does not supply that edge either. Nested domain refinements compose in the rebuilt domain.
Planning uses the refinement for `Restrict`, while operator conversion discards the `Cast` wrapper
after the restriction is planned. See
[dependent refinements](type-inference.md#45-dependent-refinements-via-pi-types) and
[optimization](optimization.md).

`Realize(value)` has a different owner and obligation. Planning introduces it after inference
when it realizes a conditional collection's dependent-sum type as a gated collection over a
positional variant domain. The asserted type is the `Realize` node's own `ty`; the node has no
target field. The gated collection and the sum are not related by the ordinary `Cast` rule.
Operator conversion compiles `value` and drops the `Realize` wrapper. See
[conditional planning](optimization.md) for the realization step.

### `Case` only — no `IfThenElse`

`Case { scrutinee, branches }` represents `if`/`elif`/`else`, conditional expressions, and
variant matches. Each ordered `Branch` has an optional tag `pattern`, a Boolean `guard`, and a
`body`; the first matching pattern with a true guard wins. `if` and `elif` lower with no
scrutinee or patterns. An else arm has a true guard. A variant match supplies the scrutinee and
per-tag payload binders; a branch without a pattern is its default arm. A pattern-only branch
carries a literal true guard. See [variants and match](lowering.md#variants-and-match).

Inference constrains a pattern's payload binder from the matching scrutinee tag. With no default
arm, the match must cover the scrutinee's tags; a default arm permits other tags. Every guard must
have type `Bool`. Each body flows into one result type variable, so the result is the arms' join.
Different scalar types currently produce an incompatibility error. Data-collection arms at
different domains can coalesce to a dependent sum, while shared refinements can survive the join
(`infer::emit::emit_case`, `infer::solver::coalesce`).

### Other expression forms

The remaining nodes supply values or mark source structure for a later phase:

| Nodes | Contract |
|---|---|
| `Lit`, `Var`, `Builtin` | Literal, named reference, and compiler primitive reference. `Builtin` avoids magic variable spellings for combinators. |
| `BinOp`, `UnaryOp` | Typed scalar operations with expression operands. |
| `Tuple`, `Record`, `List` | Positional product, named product, and source list construction. Elements may be expressions. |
| `VariantCtor` | Tag and payload construction, dual to a `Case` pattern. |
| `NominalCtor` | A nominal type's constructor applied to its payload, typed by the declaration rather than as a variant ([nominal-types.md](nominal-types.md#constructors)). |
| `Method` | A method call's unresolved function, with a reference to each candidate; inference replaces it with the one its receiver's type names ([nominal-types.md](nominal-types.md#method-calls)). |
| `TraitFn` | A function read from an instance of a trait, the compiler's or a declared trait's, typed by the trait's signature at its operand types; coalescing replaces it with the function of the instance those types match, a term the compiler builds or a use of the binding a declared instance's `def` lowers to ([type-inference.md](type-inference.md#trait-functions)). |
| `DefGroup` | An `impl` or `instance` block's functions, which reach each other in any order; inference rewrites the group into the `Let`s that bind each after the functions it calls ([type-inference.md](type-inference.md#a-definition-group-is-emitted-in-the-order-its-references-need)). |
| `Proj` | First-class tuple or record projection; applying it to a value gives field access. |
| `Compose` | Function composition in application order, built by lowering and lambda elimination. |
| `ExprStmt` | Statement expression followed by its continuation. |
| `For`, `MutWrite`, `Begin` | Pre-phase loop, mutable write, and transaction-block structure; mutability phases consume them. |
| `Feed`, `Define`, `Defer` | Deferred-output write, definition, and placeholder; `channelize` resolves them. |
| `Error` | Recovery placeholder accompanied by lowering errors; compilation stops before inference. |

`Source` is specified under [source injection](#source-injection). `Realize`, `Transact`,
`LetRec`, `LetType`, and `Aggregate` have their own sections because their typing or phase
ownership needs more than a node description.

### `Copair` and `DisjointJoin` — two collection-combining operations, not one

`Copair` and `DisjointJoin` differ in result domain and definedness. Their types describe
different operations:

| Node | Input collections | Result domain | Definedness |
|---|---|---|---|
| `Copair` (`⊎`) | `𝐴 ⤇ 𝑉`, `𝐵 ⤇ 𝑉` | Positional sum `𝐴 + 𝐵` | Tags keep all positions distinct. |
| `DisjointJoin` (`⊔`) | Partial maps on one 𝐷 | The same 𝐷 | Operand positions must be disjoint. |

`Copair` is the collection operation behind `a ++ b`. `emit_copair` assigns each operand an
anonymous `FieldKey::Index` tag in a `Type::Variant` domain and joins their codomains. Thus
`xs ++ xs` retains both copies of every row. `TypedExpr::copair` flattens nested value-form
copairings at construction; a let-bound operand can still contain its own tagged domain. The
point-free `Builtin::Copair` form may arise when lambda elimination lifts an inside-lambda
value-form copairing. A `++` over a lambda parameter currently fails at the post-elimination type
check, so this point-free fed form does not reach operator conversion through that route.

`DisjointJoin` joins partial collections over one domain without adding tags. `lambda_elim`
introduces it for `Case` fan-outs whose first-match arms partition the fed input. Inference
requires a shared domain; the type does not itself prove positional disjointness. Operator
conversion uses the flat merge that relies on that property. A copairing of the same arms would
instead create a positional variant domain, which would not have the domain expected by a
consumer of the original input. The node distinction records the operation at construction
rather than inferring it from whether conversion received a fed input.

Without a fed input, operator conversion builds a tagged union for `Copair` and a flat union for
`DisjointJoin`. With a fed input, it supports the disjoint join and rejects `Copair`: tagged
demultiplexing and re-tagging of a fed copairing is not implemented. An inline union-domained
generator beside another generator reaches this rejection. The let-bound spelling reaches runtime
and fails in union-key lookup instead. The respective tests are
`an_inline_union_generator_beside_a_second_generator` and
`a_let_bound_union_generator_beside_a_second_generator` in
`tests/it/compilation_pipeline/scalars_collections.rs`.

### The program's outputs are a trailing `Record`

A program that binds a sink ends in a `Record` of the sink-bound names, appended by lowering at
the tail of the root `Let*` chain so each output is in scope of the bindings above it. The node is
an ordinary `Record`, the same one a program whose trailing expression is a record literal ends
in.

Lowering appends it as the body of an `ExprStmt` whose effect is the program's own trailing
expression, and `channelize` collapses that `ExprStmt` to its body (`drop_expr_stmts`). A sink
program's trailing expression is therefore dropped, and the `Record` is what sits at the tail.
Which conversion entry point runs is read off the sink registry, the same fact lowering read when
it decided to append a `Record` at all.

An output is an iteration site by the rule a product's components follow
(`planning::iterate`'s `mark_component_source`). A pure program has one output and no `Record`:
its trailing expression is that output.

### `Transact` — the domain-parameterized recurrence carrier

`Transact { keys, writers, domain, parameter }` is the recurrence carrier for mutable accumulation
loops and transactions. It denotes a record whose fields are key histories, each of type `𝐷 ⤇ 𝑉`
over the shared sequencing domain 𝐷. A read of key `k` projects `__hist.k`. Each `TransactKey`
carries its initial value, the seed: what the key holds before the domain's first position. Each
`WriterSite` carries an iteration source, a point-free decision body, and read and write key lists.
Its decision is either `` `commit(writes) `` or `` `abort(unit) ``. The store's feedback and
scheduling belong to the compiled operator, while the node denotes the resulting history record.

`planning::plan_loops` constructs `Transact` from a recognized causal `LetRec` after lambda
elimination. An induction group has one writer with the accumulator footprint; a transaction
group can have multiple writers with separate read and write sets. Operator conversion selects
the position-driven induction store for a concrete iteration domain and the concurrent commit
store for `Type::Txn`. The node carries the domain so conversion can choose the engine without
reconstructing it from the writer expressions.

`parameter` is `None` for a top-level `Transact`, whose writers take the snapshot tuple alone. A
**nested** `Transact`, an inner loop's, sets it to the `(enclosing, position)` pair `lambda_elim`
merged the two loops' binders into, and is the top-level `Transact` lifted pointwise over that
parameter 𝑃: each writer's body takes `(𝑃, (snap…, item))`. Each `init` is `enclosing ⇒ 𝑉`, a
morphism of the enclosing position alone, so the inner loop seeds from wherever the enclosing one
had got to, and an enclosing position whose inner loop runs no position has a seed all the same. The
source is curried instead, `enclosing ⤇ (domain ⤇ item)`, one collection per enclosing position. The
`Transact` then denotes one history record per enclosing position, `enclosing ⇒ {key: 𝐷 ⤇ 𝑉}`, and a
variable read is the morphism `__hist ≫ .key` of the enclosing parameter. The parameter is stated
rather than rebuilt from `enclosing` and `domain` because the pair carries refinements neither
component does. Operator conversion realizes it as one store per enclosing position (see
[*Induction stores as a changelog*](../../interpreter/design-operators.md#induction-stores-as-a-changelog-inductionstore-and-storedenseread)).
Symbolic rendering: `transact under 𝑃 (k = init, …) { … }`.

See [mutation loops](lowering.md#mutation-accumulation-loops)
and [loop planning](mutability.md#loop-planning-plan_loops-letrec-patterns--transact).

### `LetRec` — causal mutually recursive definition groups

`LetRec { bindings, body }` scopes every binder over every group definition and over `body`.
`mut_elim` and `transact_phase` turn mutable state into such groups; `channelize` also constructs
`Feed`-kind groups for assembled channels. A mutable history definition reads
strictly earlier positions through `get_prev_seq` or `get_prev_txn`; trailing reads use
`final_read`. Feed outputs can be carried through the group's decision record before
channelization gathers them. The symbolic form is
`letrec 𝑏₁ = 𝑒₁; …; 𝑏ₙ = 𝑒ₙ in body`.

`check_letrec_causal` rejects a cycle in the group's reference graph made entirely of
non-causal references. A guarded reference must occur in a previous-value accessor's history
slot; a reference in the accessor's position or default argument remains non-causal. The check
looks at value dependencies, including binder shadowing, rather than type-slot predicates.
`plan_loops` recognizes causal induction and transaction groups and produces `Transact`; it also
flattens acyclic channel groups into ordinary `Let`s. A raw `LetRec` reaching operator conversion
is unsupported. See [the history model](mutability.md#the-model-histories-and-causal-recursion)
and `ccl/letrec.rs`.

### `TypedExpr` — type slot on every node

Every expression is a `TypedExpr` with a `TypedExprNode`, a `ty` slot, an optional
`user_annotation`, and a `NodeId`. `TypedExpr::new` stamps a `Type::Hole`; inference replaces it
with a registered inference variable or a resolved type. `TypedBinding` carries a name, a `ty`
slot, and an optional source annotation. Inference checks annotations and clears both expression
and binder `user_annotation` slots before downstream passes. No persistent `declared` field exists;
the binder's resolved `ty` is the type at which references are bound. See
[the binder slot](type-inference.md#the-binder-slot-and-why-annotations-do-not-outlive-inference).

`NodeId` tracks provenance, not expression equality: `TypedExpr` comparison ignores it.
`Clone` freshens node identities, while `clone_preserving_ids` and `preserve` are explicit paths
for carrying an existing identity through a rebuild. A substitution's in-place replacement keeps
the occurrence root and freshens copied interiors. Passes that rebuild nodes must decide which
identities survive so the lowering projection can still attribute diagnostics; see
[provenance](provenance.md).

### Type vocabulary

`Type` contains both durable value types and temporary inference or phase markers. The main
durable forms are:

| Form | Meaning |
|---|---|
| `Base`, `UIntRange` | Scalar types and dense finite index domains. |
| `Fun` | A function `𝐴 ⇒ 𝐵` or data collection `𝐴 ⤇ 𝐵`; an optional named binder scopes over the codomain. |
| `Tuple`, `Record` | Positional and named products. A record's field names are `Label`s. |
| `DepTuple` | A dependent tuple, each component's type reading the ones before it ([4.8](type-inference.md#48-dependent-tuples)). |
| `Variant` | Tagged sum; source tags use `FieldKey::Name`, while anonymous positional sums use `FieldKey::Index`. `Openness` distinguishes a complete tag set from an open requirement. |
| `Refinement` | A base type restricted by a nonempty set of predicates; construction flattens nested refinements. |
| `DataSource`, `Txn` | An external source's nominal domain and the transaction sequencing domain. |
| `Nominal` | An application of a `type` declaration to its type arguments ([nominal-types.md](nominal-types.md)). |
| `Poly`, `Param` | A polymorphic type over type parameters, and a parameter ([type-parameters.md](type-parameters.md)). |
| `WitnessRef` | Reference to a dependent-sum witness, inside the sum's own type; realization or erasure replaces it with a candidate. |
| `WitnessProjection` | `σᵢ(𝑐)`, the `i`th witness of the sum the term `𝑐` holds: how a type outside the sum names it ([Projecting a sum's witness](collections.md#projecting-a-sums-witness)). |
| `FamilyApp` | A generalized family applied to terms, `𝐷₁(𝑘)`: a type per value of the binders it is applied to ([Generalized types](type-parameters.md#generalized-types)). |

A `Label` (`src/ccl/label.rs`) is a record field label or a variant tag: a spelling and the module
it belongs to ([chl-spec.md, "9.12 Field labels and tags belong to a
module"](../../../docs/chl-spec.md#912-field-labels-and-tags-belong-to-a-module)). Record types
and terms, projections, variant constructors and patterns, and `FieldKey::Name` all hold one. The
root module's labels have no module path, and they share that namespace with the labels the
compiler builds for itself and with the tags of nominal types' constructors (`nominal::ctor_tag`),
`Option`'s `some` and `none` among them. A run's top-level mutable variable is labeled in its run
(`Name::field_key`). At run time, where records are keyed by strings, a label is its
`Label::runtime_key`: `name`, `module::name` for another module's label, and `@run::name` for a
run's, whose `Display` is `run::name`.

A data function can carry witness binders in its `FunKind`: for example, `Σ (𝐷 : [𝐷₀, 𝐷₁]). 𝐷 ⤇ 𝑉`
ranges over two possible collection domains. The witness reference survives inference and is
resolved by planning's realization step; it is not an inference placeholder. Outside the sum's own
type the witness is named through a term, `σᵢ(𝑐)`, and the collection is read as `unbox(𝑐)`. Its
binder range is a `TypeKind`, separate from the `Type::Variant` used for tagged values. The
positional `Variant` used by `Copair` is thus a data domain, while the Σ records a choice of domain
for one collection. See [type inference](type-inference.md) for witness subtyping and consumption.

### Transient types and inference slots

| Form | Created for | Resolution |
|---|---|---|
| `Hole` | Unrelated unknown slots created by lowering and constructors. | Inference replaces each slot; a survivor is an error. |
| `SharedHole(id)` | Lowering positions that must share one inferred type. | Annotation normalization maps equal ids to one inference variable. |
| `BoundedHole(𝑇)` | An annotation slot constrained below 𝑇. | Annotation normalization creates an inference variable with an upper bound. |
| `Infer(var)` | Solver variable with level and bounds. | Coalescing resolves it where required; strict typecheck rejects a survivor. |
| `History` | Mutable or deferred-output handle over a domain. | Mutability phases or `channelize` erase it to a function type. |
| `ChanDom(name, level)` | Nominal domain of a defer channel. | `channelize` substitutes its assembled domain. |

`Hole` has no identity, while `SharedHole` links positions before inference. Neither is a value
type. `BoundedHole` is also an annotation obligation, not a union of all subtypes of its bound.
`Infer` may remain temporarily where a value has not been exercised; strict typecheck requires a
fully resolved tree before operator conversion. Lowering does not mint solver variables.

`History { function, history_kind }` denotes a handle over the data function
`function : domain ⤇ value`. `Overwrite` is a mutable variable, rendered `Mut(value, domain)`:
ordinary reads yield its value, and its phase builds carry-forward histories. `Append` is a feed
channel, rendered `feed(domain ⤇ value)`: reads yield the whole collection, with no off-path
carry. The domain and value are invariant in the type relation. Lowering can construct histories
for declarations and parameters, and inference propagates them. `Type::feed`, `Type::mutable`,
`Type::history` and `Type::history_keyed` own construction, all through `Type::history_over`. Their
argument order is `(domain, value, kind)`, even though `Mut` displays the value first.

The function's binder names the position, and the value may read it: `Type::history_keyed` builds
`(𝑘 : domain) ⤇ value`, the type of a feed in a loop whose row at each position reads that position
([A history's value may depend on its position](type-inference.md#a-historys-value-may-depend-on-its-position)).
`ChanDom` is minted when inference types a
defer binding; its introduction level lets specialization freshen a channel introduced inside a
generalized definition while retaining a captured outer channel. See
[`Mut` as a type](mutability.md#mut-is-a-ccl-type) and
[`Feed` as a type](mutability.md#feed-is-a-ccl-type).

---

## Aggregation

### `Aggregate` — first-class aggregation node

`Aggregate { input, kind }` identifies a fold independently of a function name. CHL `sum(xs)`,
`max(xs)`, and `min(xs)` lower to this node. `OperatorSchemes::aggregate` supplies the whole
input-to-output type; `emit_aggregate` applies that scheme to the inferred input. A collection input
has data function type `𝐷 ⤇ 𝑉`. `Sum` requires `Int` elements and yields `Int`. `Max` and `Min`
yield the element type and also require `Orderable` of two elements. `Drain` consumes any element
type and yields `Unit`; `Sole` yields the element type and requires at most one input element at
runtime. Operator conversion dispatches by `AggregateKind`, without inspecting a call-site variable
name.

`AggregateKind` also defines the output extent, seed, fold, and partiality. `Sum`, `Max`, `Min`, and
`Drain` use total folds with an in-band identity. `Sole` has an `Option(𝐴)`-like accumulator:
empty is represented by an empty column, one element by a length-one column, and adding another
element faults. `is_partial` states that distinction, and `initial_accumulator` checks that the
seed representation agrees. The duplicate-key check for map construction uses this `Sole` law
(`ccl/aggregate.rs`).

---

## Source injection

`Source(name)` is a value reference to an externally registered data source. Lowering recognizes
registered zero-argument source calls and records the source name in the node. Inference gives it
a data function type with a nominal `DataSource(name)` domain and the registered element type.
Operator conversion resolves that domain to the registered source extent and reader.

The node is `Source(name, paths)`. An empty `paths` reads each value whole. Each path is a list of
keys through nested tuples and records, and names one leaf of the value. One path makes the node's
type the data function from `DataSource(name)` to that leaf's type. Several make it the data
function to the tuple of the leaves' types, in the order of `paths`. Lowering and inference make
whole reads. [Projection pruning](optimization.md#projection-pruning) makes projected reads, after
the last `simplify`, with the paths sorted and none a prefix of another. Inference sees whole reads
only. The post-planning check derives the type of a projected read from the registered source type
(`projected_source_type`), requires it to be a subtype of the type the pass stamped, and raises
a missing-field error where a path steps through a key the type does not carry. Operator
conversion reads it with `MapResultWithSource::projecting`, which asks the source for the column
through `DataSourceDomainExtentImpl::get_fields`, which takes the same paths as field names. A
source overrides it to read the leaves alone; the default moves the leaves out of the result of
`get`.

`GlobalContext` coordinates the lowering, inference, and conversion registries. The lowering
registry makes names available while constructing the tree; `compile_program` registers sources
with inference and conversion after lowering has discovered them. The conversion registry
shares a materialized source extent across references to the same registered source. Sink
bindings remain outside the expression tree as described by the purity invariant.

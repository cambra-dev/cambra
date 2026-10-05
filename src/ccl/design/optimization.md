# Optimization & compilation passes

After inference, the compiler rewrites typed CCL into an operator graph. `context.rs` runs
`inline`, transaction rewriting, `mut_elim`, `channelize`, the as-of-read rewrite,
`lambda_elim`, `planning::plan_loops`, and `planning::run`, in that order. Lambda elimination
runs `simplify` internally; planning also runs it before and after iteration-site marking.
`interpreter/operator_conversion.rs` then converts the planned CCL to `TileOperator`s. The
transaction and mutation phases are described in [mutability.md](mutability.md); the AST is
described in [ir.md](ir.md).

---

## Inlining Pass (`ccl/inline.rs`)

`inline_capability_lambdas` runs on the typed CCL tree after inference and before transaction
rewriting, channelization, and lambda elimination. It visits `Let` bindings and performs three
rewrites: it removes safe variable aliases, expands eligible function bindings at their uses,
then relocates bindings read in list elements. Expanding a call while its source lambda is still
present lets the pass substitute
the actual argument into the function body. This is required for supported calls to scalar and
collection-producing UDFs, not merely a performance optimization. A surviving scalar-domain
function binding would need iteration over a non-enumerable extent. A surviving nested lambda
can instead produce `curry` over a lambda body, for which operator conversion has no general arm.
Beta-reducing the user-argument lambda avoids those forms before lambda elimination. A function
passed around without a call is still substituted as a value; substitution alone does not
beta-reduce it.

### Alias inlining

For `let y = x in body`, the pass can replace free uses of `y` with `x` and remove the `Let`,
regardless of whether `x` denotes a scalar, function, or collection. The replacement is
conditional. The pass skips the alias shortcut if its whole-body check finds a rebinding of `x`
by a `Let`, lambda parameter, `LetRec` binder, or loop target. It also skips the alias shortcut if
the body contains a mutable write to `x`. Substitution across such a write could turn a read of
the value captured at `y`'s binding site into a read of the later value. These checks are
conservative: a matching rebind or write can block alias removal even if no particular use would
be affected. The binding remains eligible for the function-inlining check that follows. Removing
an alias here also keeps lambda elimination from lifting that alias into a `const(x)` wrapper.

### Function binding eligibility

The second rewrite checks the type of the bound expression. It expands a `Type::Fun` binding
unless its `FunKind` is `Data`; a non-function binding remains in place. The function's domain is
not the criterion. A function accepting a collection, a scalar-domain UDF, a tuple-argument UDF,
and a curried function can all qualify. A `Data` function represents a collection, including one
over a finite index domain, and remains bound. Alias removal has precedence, so a plain `Var`
binding can disappear even when its type is `Data`.

An opaque binding named in a type remains bound: its name denotes a value without exposing its
definition, so substituting only its term uses would leave the type referring to a removed binder.

### Collection sharing

Keeping a collection binding preserves a sharing point. Operator conversion compiles a surviving
`Let` bound expression into an operator behind `Memo` and gives uses branches from `FanOut`.
Substituting the collection at every use would instead give downstream compilation separate
copies of its expression, which may duplicate its work. Conversely, an expanded function body
appears at each use, trading that possible duplication for call-site specialization. The pass
has no use-count or cost test; its type-kind rule makes this decision uniformly. A collection
substitution could sometimes enable fusion with its consumer, but this pass does not make that
tradeoff. These restrictions describe function-binding expansion; the separate list-element
rewrite below can copy a bound value into a literal element. The type-level decision is described in
[Generalizing a collection is filter pushdown](type-inference.md#generalizing-a-collection-is-filter-pushdown).

### Substitution and beta-reduction

For an eligible binding, the pass substitutes the bound expression at free occurrences of its
name and removes the `Let`. At a call whose function position is that name, including a chain of
applications for a curried call, it reduces an application when the substituted function is a
lambda: the argument replaces the lambda parameter in its body. If the substituted function is
not a lambda, the application remains. Applications of unrelated anonymous lambdas are left for
later passes. Substitution respects binders that shadow the function name and also visits
refinement predicates stored in type slots, where a use may otherwise be missed by the ordinary
expression walk.

Beta-reduction has a further condition for a refined outer parameter: the argument's type must
entail the parameter's refinements. The pass asserts when it cannot establish that condition,
since dropping the parameter without preserving its precondition would be unsound. For
multi-argument UDFs lowered with a tuple parameter, substitution can leave
`Apply(Tuple(...), Proj(Index(i)))`; `simplify::try_literal_tuple_projection` folds that shape
later. Finally, the pass revisits the reduced result, so newly exposed `Let` bindings can undergo
the same inlining checks.

### Moving a binding into a list element

`inline_list_element_reads` replaces a list element that reads a `Let` binder with that
binder's definiens, dropping the `Let` when no reader remains. An opaque binder named in a type
is left in place. A list literal's elements
are a value position: op-conversion compiles the whole literal to one table read at
graph-build time, so an element is sequenced against nothing and the move changes no
order. A definiens reading a mutable variable the body may write stays bound, because the
read would otherwise move past the write. Two mentions count as a write: a `MutWrite` to
that variable, and a handle passed to a callee, whose body this pass has not expanded at
the binding it is rewriting.

The relocated definiens carries A-normalization's bindings for its own compound
sub-values, and `flatten_anf_bindings` substitutes each into its one use as the element is
placed. Without it, a nested constant reaches the element position as a `Let` chain around
the value former — ``[`a(`b(4))]`` as ``let __anf = `b(4) in `a(__anf)`` — and
op-conversion reads only the constant formers there (`expr_to_value`), so a program whose
element is a constant is rejected as a computation. The flattening is scoped to what moves,
to A-normalization's own binders, and to a binder read once; an element that is a
computation still reaches that rejection spelled as the computation it is.

A predicate carries its own copy of the `Let` chain riding the term, so both rewrites
descend into refinement predicates. Rewriting one copy alone leaves a node's type
describing a collection its value no longer is, which the `post-inline` check reports as a
domain mismatch.

### Limitations

- **Unapplied or partially applied compute functions:** An unapplied nested lambda can leave a
  `curry` over a lambda body, which operator conversion cannot compile. A partial application such
  as `add(1)` can eliminate that combinator but still leave a compute-function result: debug
  planning rejects it at the data-site assertion, while a build without that assertion attempts
  to iterate its non-enumerable `Int` domain. Binding each application and ultimately consuming the
  result, `x = add(1)` followed by `x(2)`, lets inlining eliminate both parameter layers. The
  spelling `add(1)(2)` is separately rejected because CHL call lowering requires a named target.
  Curried data functions are different: grouping constructs them through `converse`, and the
  runtime represents them with nested `DataFunction` tilings.
- **Collection bindings:** A `Type::Fun` with `FunKind::Data` is not expanded by the function
  rewrite, regardless of its domain. A safe plain-variable alias can still be removed by the
  earlier alias rewrite. A surviving `Let` compiles through `Memo` and `FanOut`.
- **Body duplication:** An eligible function body is copied at each use in the CCL tree. The pass
  has no use-count or cost test.
- **Recursive UDFs**: unsupported (already noted in `operator_conversion.rs`).

---

## Lambda Elimination (`ccl/lambda_elim.rs`)

`lambda_elim::run` removes term-level `Lambda` nodes from the channelized, typed tree. It
eliminates outer lambdas before their nested lambdas, then simplifies the result to a fixed
point. A nested lambda can capture its outer parameter, so eliminating the inner one first
would mistake that parameter for a constant. The rules use the Cartesian closed category
structure described in [operational lowering](/docs/operational-semantics/lowering.md).
Refinement predicates in type slots remain pointful until planning compiles them.

### Output nodes introduced

The pass represents composition with `TypedExprNode::Compose`, and projections with
`TypedExprNode::Proj`. It rewrites non-composition binary operations to an application of
`Builtin::BinOp(op)` to a tuple, and unary operations to an application of `Builtin::Neg` or
`Builtin::NotFn`. These rewrites apply both inside and outside lambdas.

| Source expression | Point-free CCL shape |
|---|---|
| `f ≫ g` | `Compose([f, g])` |
| `.0`, `.field` | `Proj(Index(0))`, `Proj(Field("field"))` |
| `a + b` | `(a, b) ▷ add` (`Apply(Tuple([a, b]), Builtin(BinOp(Add)))`) |
| `-a`, `not a` | `a ▷ neg`, `a ▷ not_fn` |
| `λ x → x` | `id` |
| `λ x → c`, where `x` is not free in `c` | `c ▷ const` |
| `λ x → e ▷ f` | `⟨λx→e, λx→f⟩ ≫ apply` |
| `λ x → λ y → e` | `curry(λ (x, y) → e)` |

The eliminated function retains its inferred `FunKind`. If its result type refers to the
eliminated parameter, the point-free function type retains the binder as a dependent function.
`Builtin::Zip` pairs point-free functions: `⟨f, g⟩` is
`Apply(Tuple([f, g]), Builtin(Zip))`. Records of functions use the corresponding record-shaped
`Zip` application. There is no separate `Zip` AST node. `Builtin::Compose` is a first-class
composition function; it differs from the `TypedExprNode::Compose` chain.

The other combinators introduced here include `Curry`, `Const`, `Apply`, `Map`, aggregation
builtins, and the point-free `Copair` form. `Builtin::Copair` appears as
`Apply(Tuple(arms), Builtin(Copair))` when a copair is lifted out of a lambda. A value-position
`TypedExprNode::Copair` remains a value-form node. Planning later introduces `Iterate`,
`Restrict`, `Strength`, `CurryOver`, `Converse`, `Uncurry`, and the domain transformations used by
join plans; `simplify` introduces `Strength` as well.
Lambda elimination does not introduce iteration sources.

### Conditional expressions and filters

A value-selecting `Case` inside a lambda becomes a `DisjointJoin` of arms. Each arm first
applies `filter_values` to the fed input using its first-match condition, then computes the
arm value. This keeps a partial operation in an arm from running at positions rejected by
that arm's guard. A scalar `Case` in value position uses a one-element iteration domain:
each arm lifts its value over that domain, restricts it by its first-match condition, and
the arms are unioned. `final_or_default` extracts the selected value. Its fallback is the
exhaustive final arm. A collection-valued `Case` remains for conditional-collection planning.
For a scalar pattern match, the branch condition comes from the scrutinee's tag.

For a source followed by `λ x → Case { guard → action; true → unit }`, the `Compose` rule
attaches the guard as a refinement of the source domain and composes the eliminated action
after it. This recognition requires the two-branch `Case` at the lambda body's root. Planning
later materializes the refinement at an iteration site. A leading `Let` around the `Case`
does not match this filter rule and takes the general lambda-elimination path.

### `Let` inside a lambda

For `λ x → let v = def in body`, elimination keeps a `Let`: its bound expression becomes
`λx→def`, and free uses of `v` in the body become `x ▷ v` before that body is eliminated.
The bound function therefore varies with the surrounding input. Operator conversion fans
that input to both the bound expression and the body. A `Let`'s type is reclosed over its
new definition if a refinement in the result refers to the binder. The current `Let` node
contains `binding`, `bound_expr`, and `body`; it has no `bound_ty` field.

### A generator over a sum composes with its source

A comprehension over a Σ-typed collection lowers to a lambda that is itself a sum,
`λ k : σ → (k ▷ 𝑆) ▷ 𝑓`, whose key ranges over the source's witness. Before elimination,
`compose_sum_generators` rewrites each such generator to `𝑆 ≫ 𝑓` when `k` is free in neither `𝑆`
nor `𝑓`. The composite takes its kind from `𝑆`, retaining its sum and using `𝑓`'s codomain.
A filtered
generator is left to the cast-wrapped arm, since the filter's refinement reads the key.

The rewrite keeps the witness out of the nested-lambda rule. That rule turns `λ 𝑥 → λ 𝑦 → body`
into `curry(λ __pair → body)` with `__pair : (𝑋, 𝑌)`. For a Σ-typed inner lambda, `𝑌` is `σ`. Its
binder sits on the inner lambda's type rather than on the pair, and the key's witness depends on
the pair's first component, which `Type` has no dependent pair to state. After the rewrite the
inner lambda is the element function `𝑓`, over the source's values, which carry no witness.

Where `𝑓` reads nothing from the enclosing scope, elimination leaves
`⟨𝑆, 𝑓 ▷ const⟩ ▷ zip ≫ compose`. `simplify` rewrites this to `𝑆 ≫ map(𝑓)`, or to `𝑆` for `id`.
Where `𝑓` reads the enclosing scope, elimination leaves `⟨𝑆, curry(𝑔)⟩ ▷ zip ≫ compose`
with `𝑔` over `(𝑋, 𝑉)`, which `simplify` rewrites to `⟨id, 𝑆⟩ ▷ zip ≫ strength ≫ map(𝑔)`.
`strength : (𝑋, Σ (𝐷 : 𝐾). 𝐷 ⤇ 𝑉) ⇒ Σ (𝐷 : 𝐾). 𝐷 ⤇ (𝑋, 𝑉)` pairs a value with each value of a
collection under that value's key, so the witness binds once, by the outer sum, and no dependent
pair is needed. Operator conversion compiles it to `Product::per_row_values_at`, which pairs each
row with the values of its own collection. Both rules are scoped to an `𝑆` whose values are a
sum, because planning's recurrence recognition reads a history through the unrewritten form.

A correlated inner comprehension over a collection every row reads is the same shape with that
collection constant: planning rewrites its `curry(𝑔)` to `⟨id, const(𝐾)⟩ ▷ zip ≫ strength ≫
map(𝑔)`, where `𝐾` is the collection the inner comprehension ranges over
(`src/ccl/planning/correlated.rs`). A site whose type is dependent stays one node,
`(𝐾, 𝑔) ▷ curry_over`, since the chain has no spelling for a domain narrowed by its input
(`src/ccl/ops.rs`, `Builtin::CurryOver`).

#### A pair naming a sum's witness is refused

`lambda_elim::run` refuses a `curry` whose argument's type still names a witness free once
simplification has run: the nested-lambda rule reached a Σ-typed inner lambda that
`compose_sum_generators` did not rewrite.

---

## Planning (`ccl/planning/`)

Planning turns point-free CCL into explicit iteration and filter chains. `context.rs` first
calls `planning::plan_loops` to recognize causal `LetRec` groups as `Transact` nodes. Both
induction loops and transaction groups use this carrier; its domain selects the runtime
engine during operator conversion. `planning::run` then performs these rewrites in order:

1. Realize collection-valued conditionals and erase determined sum witnesses. A row of a jagged
   collection read from a mutable variable is refused.
2. Recognize pointful keyed-aggregate sources and rewrite them using `converse`.
3. Simplify point-free expressions before inserting iteration sources.
4. Fold closed scalar computations with `const_fold::fold_constants`.
5. Mark iteration sites, choosing a hash join where its predicate matches.
6. Compile remaining refinement predicates throughout the tree.
7. Insert `map(filter_values(𝑞))` for supported refinements on inner, per-group collections, and
   refuse a narrowing none materializes (`reject_unmaterialized_narrowings`).
8. Simplify the planned expression again.

Constant folding evaluates supported operations through the runtime's `src/scalar_ops.rs` kernel
on one-element columns. `src/ccl/planning/const_fold.rs` defines which expressions are excluded;
the pass leaves their runtime evaluation unchanged.

The second simplification removes identities and nested composition introduced by join
planning. Structural rules that could discard an iteration source guard themselves against
subtrees containing `iterate`. A planned `restrict` is protected because its upstream contains
`iterate`; the guard does not independently recognize `restrict`. Predicate compilation follows
the group-by and join recognizers because they inspect inference's pointful predicates.

### Conditional collections

A collection-valued guard `Case` carries a sum over its possible domains. For a witness with
finitely many named candidates, conditional planning restricts each arm by its first-match
condition and unions the arms. Exactly one arm contributes data. The resulting tagged union
is an executable representation of the selected collection; it is introduced after type
inference because its type differs from the source sum. A determined witness with one
candidate is erased from the term and its types. Every other witness is materialized: its `box`
stays standing, the value carries its own keys, and operator conversion bounds the domain from
the witness's kind. A `for` loop over a sum is refused by name, since its history would name the
witness outside its binder. See
[collections.md](collections.md#compiling-a-conditional-collection).

### Loop recognition

`plan_loops` recognizes the point-free causal form emitted by mutation and transaction
rewriting. It turns each supported `LetRec` group into a `let __hist = Transact { keys, writers,
domain } in body`, then rewrites history reads to that binding. Each writer has an iteration
source, a decision body, and read and write key sets. Operator conversion compiles a concrete
iteration domain to the induction store and `Txn` to the commit engine. The transaction
recognizer also retains feed taps alongside writes in the history record. Guard-free, acyclic
channel groups emitted by `channelize` instead flatten to dependency-ordered `Let` bindings.
An unrecognized causal group panics at compile time; there is no fallback recognition strategy.

### Hash Joins

At an iteration site with a refined tuple domain, `try_hash_join_rewrite` delegates to
`convert_loop_join` and `plan_loop_join`. The same planning path handles every arity of at least
two. `split_join_conditions` splits the pointful predicate's top-level `and` tree into equalities
and residual predicates; it does not extract join conditions from inside other Boolean forms.
Each equality side must depend on exactly one distinct tuple arm. `replace_tuple_project_with_id`
removes that arm's tuple projection to obtain its key function.

`spanning_tree_children` builds a breadth-first tree rooted at arm 0. A disconnected equality
graph makes the entire site fall back to loop iteration; it does not produce a partial hash join.
`build_join_plan` combines each child subtree with the accumulated probe side, choosing build and
probe order from that tree without a cost model. Every `JoinPlan::Loop` leaf represents one arm.
Each `JoinPlan::Hash` groups the build side by its key with `converse`, probes that group, and uses
`uncurry` and `map_domain` to restore the pair domain.

Additional equalities crossing a join become residual predicates. `collect_arms_used` identifies
the arms required by each other predicate, and `reindex_for_domain` adapts it to the selected
node's flat domain. Predicates run at the first node containing all their required arms;
single-arm predicates can be pushed to a leaf. A residual with no referenced arm currently hits
the `TODO support constant predicates in joins` assertion.

The domain must have exactly one refinement for this recognition path. With multiple refinements,
the attempted conversion retains the others around the base, which then fails `convert_loop_join`'s
bare-tuple match and leaves ordinary iteration and filtering.

`join_plan_to_expr` emits the tree as CCL. A leaf starts with `iterate`; a hash node uses
`converse`, `uncurry`, and `map_domain`. Nested joins may need `flatten_domain` to make
their tuple domain flat. `convert_loop_join` applies `permute_domain` when breadth-first
arm order differs from the source tuple order. A residual predicate applies `restrict`
to its leaf or joined stream. The join output thus has the same tuple order and filters
as the loop it replaces.

### Keyed Aggregates

`recognize_groupby_sites` matches the dependent-refinement source produced for a keyed
aggregate such as `sum(x) for x in groupby(xs, key_fn)`. The source describes a group
through a key equality on its element domain. The rewrite computes keys over the source,
groups them with `converse`, and maps the value function over each group. The group keeps
the key-dependent refined domain, so a later aggregate sees only its members. If the
pointful shape does not match, the site retains ordinary iteration and restriction.

### Iteration-Site Marking (`insert_iterate_markers`)

`insert_iterate_markers` visits positions that operator conversion compiles with no
upstream input. These include the program's collection-valued result, collection-valued
`Let` definitions, aggregate and grouping inputs, `Transact` writer sources, collection
merge operands, and function-typed fields in a value-position `Record`. `Zip` instead
fans an existing input to its tuple or record operands. For `final_or_default`, only its
stream operand needs iteration; the default is a scalar. A top-level `Let` is traversed
through its definition and body rather than prefixed with an iteration source. Its
definition is compiled even when the body never uses it.

`wrap_with_iterate` first checks whether a site already has an iteration source or an
operator that internalizes iteration. It then attempts the hash-join rewrite. Its default
source is `(true ▷ const) ▷ iterate` over the unrefined domain, followed by one applied
`p ▷ restrict` for each refinement in `application_order`, then the value-producing
body. An unrefined site has only the initial `iterate`. The type of `restrict` is a
function transformer: it narrows the upstream collection's domain and preserves its
values. Accordingly, `upstream ▷ (p ▷ restrict)` applies the transformer to the
upstream function; composing it as a morphism would have the wrong input type.

A `restrict`'s predicate is compiled at the site it filters, after the walk has passed that
site, so the walk never reaches a collection the predicate aggregates, `zs` in `if x > sum(zs)`.
Planning runs the walk over each `restrict`'s predicate once the walk over the tree is done
(`plan_restrict_predicates`), where the collection is an iteration site like anywhere else. The
refinement `make_restrict` writes on the narrowed domain states the predicate as compiled: the
markers belong to the term the `restrict` applies, and a refinement carries none.

`Builtin::Iterate` requires no upstream input and compiles to `IterateExtent`. A
nontrivial predicate on that builtin adds a `Restrict` operator; the planner's default
source uses the trivial predicate, so each later refinement is represented by its own
applied `restrict`. `Builtin::Restrict` consumes its upstream input. Already marked
chains, collection-typed bound variables, and combinators that create iteration from
their arguments are not prefixed again. A bare sum witness has no iteration extent;
conditional planning must realize it or the unresolved case reaches a compile error.

The complete `is_iteration_bearing` skip cases are:

- Value-position `Tuple`, `Record`, `Copair`, and `DisjointJoin` nodes.
- A `Var` whose function kind is `Data`.
- An `Apply` headed by `Iterate`, `Restrict`, `AsOf`, or `FilterValues`, or by a builtin whose
  `iterates_arg` property is true, including the domain-transforming combinators.
- An `Apply` whose function position is not a builtin, such as a projection, variable, or curried
  application; its conversion path rejects an additional upstream input.

Recognizing a `restrict`-led chain is necessary for repeated planning walks: its upstream already
has an iteration source, and another wrapper would stack a second one.

### Per-group value filters

`insert_per_group_filters` handles a refinement on the domain of a collection returned by a
function, where that refinement depends on the function's input collection. The ordinary
iteration walk sees the function's own domain and cannot materialize this inner one.
When each added predicate reads that input collection, planning converts the added
conditions into a value predicate 𝑞 and inserts one `map(filter_values(𝑞))` before the function.
The operator filters each group's elements independently. `reject_unmaterialized_narrowings`
refuses a narrowing no per-group filter materializes, since operator conversion would compile the
site without its filter.

---

## Compilation

`interpreter/operator_conversion.rs` converts planned CCL to tile-dataflow operators.
`Compose` passes each operator's output to the next. The conversion arms distinguish
expressions that consume an upstream stream from expressions that compile their own
input. Planning supplies `iterate` at the latter sites, so conversion does not infer
iteration from a refinement type. A surviving `Lambda` or `LetRec` violates the pass
boundary and is rejected.

| Planned CCL | Operator behavior |
|---|---|
| `f ≫ g` | Compile `f`, then feed its result to `g` |
| `id`, `map(g)` | Pass the input through; `map` compiles `g` with that input |
| `const(c)` | `MapResultToConst` on the input |
| `zip(f, g)` | Share input through `FanOut` and combine results with `Zip` |
| `zip((a: f, b: g))` | `zip_arms_named_at` selects `Zip` or `MakeRecord` |
| `.n`, `.field` | Project a tuple or record field |
| `add`, `neg`, and other scalar builtins | Apply the corresponding scalar operator |
| `(true ▷ const) ▷ iterate` | `IterateExtent` over the declared domain |
| `p ▷ iterate`, nontrivial `p` | `IterateExtent` followed by `Restrict` |
| `upstream ▷ (p ▷ restrict)` | Filter the upstream with `Restrict` |
| `filter_values(p)`, `map(filter_values(p))` | Filter fed values or each inner collection |
| `copair`, `disjoint_join` | Combine collection arms through union operators |
| `List` | `MapResult` over an index stream |
| `Lit`, value-position `Tuple` or `Record` | `Constant` or `MakeRecord` |
| `Source(name)` | `MapResultWithSource` reads the registered source using the supplied upstream input |

`build_product` uses the node's extent to distinguish a record of tiles from a collection of
records. A record extent uses `MakeRecord`; a function extent uses `zip_arms_named_at`, which
pairs the components over their ambient iteration. `Transact` is intercepted at its enclosing `Let`
and compiled as a shared history store. End-to-end cases are in
`tests/compilation_pipeline/`.
See [Operator Conversion](../../interpreter/design-operators.md#operator-conversion-interpreteroperator_conversionrs)
for the operator-level contracts.

### `Let` nodes compile to a shared binding, not `Apply(Lambda)`

Operator conversion compiles the bound expression, places `Memo` behind a `FanOut`, and
binds that handle in a scope. Each `Var` use takes a branch. A binding aligned with the
surrounding iteration reads its branch directly; a free binding used under an input is
applied pointwise through `MapResult`. The `Let` arm can fan a surrounding input to both
the definition and body, as required by `Let` expressions produced inside lambda
elimination. The bound expression is compiled even if unused, so planning marks a
collection-valued definition as an iteration site. The binding's type must be resolved
before conversion.

A bound morphism must have the upstream input it requires. A bound `.0`, or a chain headed by one,
fails conversion when that input is absent; the binding can also hide a chain head from planning's
iteration-site recognizers. `simplify::try_let_morphism_inline` substitutes a function-typed
A-normalization binding used once into that use, exposing the chain to both passes.

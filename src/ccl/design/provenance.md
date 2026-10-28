# Provenance — node identity and source attribution

Provenance relates compiler nodes to their inputs and source spans. `src/ccl/provenance.rs`
defines node identities, recording, tables and folds. `src/ccl/context.rs` installs the sessions;
`src/ccl/panes.rs` declares retained snapshots and the relations between them.
See [The seam](#the-seam) for pipeline integration and
[Operator conversion](#operator-conversion) for operator identities.

Unmarked sections describe the implementation. **Planned** marks proposed features.

## Mechanism at a glance

Expression nodes and operators carry `NodeId`s. A rewrite that preserves a logical node keeps
its identity; a duplicate receives a fresh identity. The [identity rules](#node-identity) define
which copies may preserve IDs and how shared predicate terms are checked.

A [recording](#the-recorder) names the node being rewritten. Construction hooks capture new
nodes and copies under the innermost recording. The [table](#the-provenance-model) stores one
row per produced ID, with ancestry, additional attribution and a rewrite tag.

[Folding](#the-fold) selected phases produces a node relation, source attribution, deaths and
recording leaks. Pane folds relate retained snapshots. `ProvenanceAudit` instead measures a
chosen span against live trees. [Gate and audit coverage](#gate-and-audit-coverage) specifies
the checks and switches; enabling capture and asserting the absence of leaks are distinct.

## Terms

| Term | Meaning |
|---|---|
| **pane** | A retained compiler snapshot: an expression tree or operator graph. An expression pane retains a full-tree clone; the operator graph is already retained by compilation. A pane **below** another is later in the pipeline, not deeper in a tree. |
| **walk start** | An operator-pane node with no incoming `value` subscription edge: a sink or share point where a consumer starts a walk. Both wire producer and consumer derive these from edges. A tree pane instead ships its expression root. |
| **boundary node** | An operator-pane node representing a sink, with a label and identity but no tiling. A data source is not a node; an `IterateExtent` reads its domain. |
| **recording** | The dynamic scope opened by `provenance::enter` and held by a `RecordingGuard`. The innermost recording captures a mint or copy. A recording site is the code location that opens it. |

## Node identity

`NodeId` is a `Copy` newtype allocated from a process-global atomic counter separate from the
counter for binder `Uid`s. `TypedExpr` stores it inline. Provenance rows and source attribution
are keyed by this identity; equal expression values may have different IDs.

**Planned:** a `NodeId` also names a name's occurrence, the place the name is written
([Name occurrences](#name-occurrences)).

`TypedExpr::PartialEq` compares `ty`, `node` and `user_annotation`, excluding `node_id`.
`TypedExpr` has no `Hash` implementation. `NodeId` has `Hash` and `Ord` for keyed collections
and the fold's mint-order traversal. Its numeric value is serialized as an inspector handle;
it is not stable across compilations or changes to allocation counts.

The **main tree** consists of nodes reachable through `walk_children`. Refinement predicates
contain additional expression nodes reachable through type slots. A predicate term may be shared
by several slots through one `Rc`; distinct live terms must not share IDs. Two terms with one ID
would collapse to one row and one source attribution. [Walking the ids](#walking-the-ids) specifies
the different traversal rules for these two domains.

`Expr::new` mints an ID and reports it to the recorder. Ordinary `Clone` freshens each expression
node it copies and reports its origin; type-slot predicates retain their `Rc` sharing.
The explicit preserving operations and diagnostic-only exceptions are specified under
[Duplication](#duplication).

`NodeId::PLACEHOLDER` is zero; the counter starts at one. `Default`, `mem::take` placeholders and
diagnostic throwaways use this sentinel without recording a birth. It must not persist in the
main tree; the boundary check asserts that condition in debug/test builds.

`Phase` identifies the compiler stage in a row's `via` field. Each tag's runs lie within one pane
pair, but a tag can run on both sides of another tag within that pair: `MutRead` runs before and
after inference. Declaration-order range queries describe exact pipeline intervals only at
pane-pair granularity. A rewrite crossing a pane boundary needs a distinct tag; `AsOfRead` is
separate from `Transact` even though both are implemented in `transact_phase`.
`PANES` in `src/ccl/panes.rs` assigns phases to snapshot intervals.

### Walking the ids

`collect_tree_ids` enumerates the main tree and refinement-predicate interiors. It uses
`walk_type_slots`, including user annotations and `Cast` targets, and recursively visits the
predicates' own types. This is the ID domain used by expression-pane folds and source projections.
`collect_main_tree_ids` excludes predicates and supports the narrower audit mode.

**Planned:** every id walk reaches name occurrences through one enumeration
([Walking the ids with occurrences](#walking-the-ids-with-occurrences)).

`assert_unique_node_ids` checks the same two domains with different sharing rules:

- `duplicate_node_ids` visits each main-tree occurrence without pointer deduplication. Repeated
  IDs are collisions.
- `predicate_id_collisions` collects one ID set per distinct predicate `Rc`. It reports IDs
  shared by distinct predicate terms and IDs shared between a predicate and the main tree.
  Reaching one predicate through several type slots is permitted.

The predicate check compares sets across distinct terms; it is not a multiplicity check within
one predicate's ID set. Treating every type-slot occurrence as a distinct term would reject
permitted `Rc` sharing. The corpus test `distinct_predicate_terms_never_share_a_node_id`
also checks retained panes, including snapshots taken between pipeline boundary checks.

Predicate nodes require attribution when introduced, rewritten or raised into the main tree.
Lowering's `tag_predicate` sweeps a completed predicate through `lowering_predicate_leaf`.
That hook skips already-recorded IDs, preserving existing precise attribution when a shared term
is reached again. Inference records singleton-predicate construction against a literal site.

`PredMemo::rebuild` normally derives a fresh predicate under `predicate.rebuild`, naming the
original predicate as its parent. Replacing one `Refinement`'s `Rc` does not prove that the
original term is dead: another type slot may still hold it. `PredMemo::replacing` permits
id-preserving rebuilds only when the traversal replaces every occurrence. `uniquify` uses this
mode and separately checks ID-multiset preservation with `uniquify::collect_node_ids`; that walk
does not deduplicate by `PredicateId`.

Planning raises predicates through `fn_of_bare_predicate`, group-by key extraction and hash-join
key morphisms. A copied predicate keeps its own parentage through the copy hook, rather than
acquiring the enclosing rewrite site's parentage. The test
`both_raising_paths_attribute_the_predicate_to_the_predicate` covers both
`fn_of_bare_predicate` paths. In its slower path, the site's eta wrapper is consumed during
elimination and composes away as a transient.

Copies preserve predicate `Rc` sharing because planning memoizes compilation by that identity.
Rebuilding a separate predicate per occurrence would repeat compilation. The invariant and
memoization contract are specified in
[Sharing is an invariant, not an optimization detail](type-inference.md#sharing-is-an-invariant-not-an-optimization-detail).

### Duplication

Ordinary `TypedExpr::Clone` mints a new ID for each copied expression node and reports every
`(origin, fresh)` pair through `on_copy`. A recording writes each copy against its origin.
With no recording open, the copy has a fresh ID but no new provenance row; under an active phase,
the hook's debug coverage assertion detects that missing recording.

The explicit copying operations have different identity contracts:

- `clone` duplicates the value at fresh expression IDs. Its type slots share their predicates
  with the source through `Rc`; they do not duplicate those predicate terms.
- `clone_preserving_ids` retains every copied expression ID and emits no copy events. Source
  and copy must not become distinct occurrences in one reachable tree. Permitted uses include
  substitution templates, separately rooted pane snapshots, rollback/comparison snapshots,
  tests comparing a phase's input with its output, and copies that replace a borrowed source
  which is then dropped. A substitution template is not itself a live tree node; materializing
  a read gives that occurrence fresh identities. A snapshot remains a separate tree.
- `clone_at(id)` copies a subtree with the supplied root ID and ordinary cloning of its children.
  Substitution uses it to retain a replaced variable occurrence's identity while freshening the
  replacement's interior. Distinct occurrences retain distinct roots. Recording a wholly fresh
  copy against the occurrence could preserve attribution, but would also report the occurrence
  dead and require an ordering-compatible record.

`preserve(id, node)` constructs a node directly at an existing ID without minting or recording.
It defaults the type to `Hole` and the user annotation to `None`. A field-wise rebuild that must
retain those fields can carry the original `node_id` in its struct literal; exhaustive field
checking then prevents an omitted type or annotation from being silently defaulted.
Minting a root and overwriting its ID would leave a recorded birth that no node carries.

`clone_preserving_ids` is not a repair for an `Unrecorded` or `DanglingParent` leak. A duplicated
term needs a recording around the copy and a recorded origin. Preserving its IDs would instead
hide the missing recording and may create collisions.

`run_debug_check` is a separate diagnostic-only scope: clones preserve IDs and `Expr::new`
constructs a `PLACEHOLDER` throwaway. Nothing built in this scope may enter a live tree.
The scope prevents diagnostic work from shifting later allocation IDs and serialized fixtures.

Every duplicated arm freshens, including the first. Choosing an arm to retain the source ID by
position assumes that arm survives; later transformations may discard it.

Intermediate templates and per-branch environments may be copied several times before placement.
Freshening at placement records the identity of the occurrence that reaches the output. An
earlier freshening has three possible outcomes:

- Moved into the output: the placed node holds the fresh ID and names the original as its parent.
- Copied again: the placed copy names the intermediate ID. If that intermediate was not recorded
  and is not in the input tree, the fold reports `DanglingParent`. A recorded intermediate instead
  composes away. A template copied without an open recording must preserve its IDs. A copy under
  a recording may freshen: `Subst::discharge_env_in_place` and `discharge_env_in_binder` copy
  templates this way under their callers' recordings before materialization.
- Dropped: the ID and any recorded row may be unused. Uniqueness checks visit reachable nodes;
  there is no requirement that every recorded birth survive into an output tree.

A predicate lifted into the main tree must have fresh expression IDs because the predicate may
remain on its original type slot or be lifted at another site. `fn_of_bare_predicate` freshens
the placed term. Group-by key extraction uses `predicates::eliminate_lifted`, including lambda
elimination, before planning the lifted key. `groupby_recognition_lifts_the_key_without_aliasing`
checks the resulting IDs. The attribution test named above covers the iterate lift's parentage,
not a separate uniqueness assertion there. The required lowering passes are specified under
[Planning a lifted term](optimization.md#planning-a-lifted-term).

`compile_program` checks uniqueness after lowering and at the later boundaries handled by
`settle`. `assert_unique_node_ids` and `gate_leaks` return without asserting when neither
`debug_assertions` nor `test` is enabled. A passing boundary check establishes the invariant
for that checked tree, not for every intermediate tree built within the phase.

## Name occurrences

**Planned.** Each name the source writes that a term holds in a field rather than as a node carries
a `NodeId` of its own, an `Occurrence`, recorded at the span of the name as the source writes it. A
binder's annotation carries one too, recorded at the span of the type expression it writes.
Provenance mints, copies, enumerates, folds and gates an occurrence as it does an expression node's
id, so a `NodeId` names an expression node or an occurrence. Nothing in provenance reads which of
the two an id names.

A name appears in a term in seven ways, and the first four carry an `Occurrence`:

| Kind | Example | Held in | Its id |
|---|---|---|---|
| **binding occurrence**: the name a binder introduces | `p` in `def f(p)`, `g` in `g = 10` | `TypedBinding.occurrence` | an `Occurrence` |
| **applied occurrence held as a field**: a use of a binder bound elsewhere, written where the IR holds a name rather than a node | `out` in `out << v` | the `name_occurrence` of a `Feed`, `Define` or `MutWrite` | an `Occurrence` |
| **label occurrence**: a record field label or a variant tag a term writes | `x` in `(x=1, y=2)`, `ok` in `` `ok(1) `` | a `Record` entry's `label_occurrence`, a `VariantCtor`'s `tag_occurrence` | an `Occurrence` |
| **head occurrence**: the tag or constructor a `match` arm matches | `ok` in `` case `ok(v) ``, `rect` in `case Shape::rect(w, h)` | `Pattern.head_occurrence` | an `Occurrence` |
| applied occurrence held as a node | `g` in `p + g`, `Shape::rect` in `Shape::rect(1, 2)` | a `Var` | the `Var`'s own `NodeId` |
| field or method name | `x` in `p.x`, `m` in `v.m(a)` | a `Proj` or `Method`, tagged at the name | the node's own `NodeId` |
| substituted parameter or field: a use of a name lowering binds to no binder | `q` in `def f(p, q): q`, `w` in `case Shape::rect(w, h): w` | a projection tagged `lower.param_proj` | the projection's own `NodeId` |

The **annotation occurrence** is the fifth kind of `Occurrence`: `String` in `x: String = 5`, held
in `Annotation.occurrence` inside `TypedBinding.user_annotation`. In this doc, "an occurrence" means
any of the five, and a rule that covers fewer names them.

A name written in a type has no place in a term: `Shape` in `s: Shape`, an alias, a type
parameter, a `use` item and a module path. Lowering resolves each one and erases it, so no pass
after lowering holds it. Lowering records what it resolved in a table outside provenance
([Names lowering resolves](lowering.md#names-lowering-resolves)).

Occurrences are in the fold so that a binder is reachable in every pane, not only where lowering
built it. Passes copy binders: monomorphization's specializations, the comprehension phase's
main-tree and predicate lambdas, `channelize`'s companion lambdas. Each copy's occurrence is a row
parented on the occurrence it copies, so the pane-pair maps carry a binder from `pre-inference` to
every copy of it. A consumer reads the type of each specialization of `v` in `def twice(v)` that
way, and the LSP's hover reads a binder's inferred type the same way. Go-to-definition reads only
the `pre-inference` pane, so it alone would need no more than an id minted in lowering and copied
as a `Uid` is.

Occurrences exist only in a tree that lowering produced. A parse or lowering error anywhere in a
program leaves no tree, so it leaves no occurrences, and nothing that reads them answers for that
program.

Narrowing the binding node's span to the name does not give a binder a position of its own. That
span is the extent of what the node computes, and a diagnostic about the statement reads it that
way.

### The occurrence field

```rust
pub struct TypedBinding {
    pub name: Name,
    pub occurrence: Occurrence,
    pub ty: Type,
    pub user_annotation: Option<Annotation>,
    pub transparency: BindingTransparency,
}

pub struct Annotation {
    pub ty: Type,
    pub occurrence: Occurrence,
}

pub struct RecordEntry {
    pub label: Label,
    pub label_occurrence: Occurrence,
    pub value: TypedExpr,
}

Feed { name: Name, name_occurrence: Occurrence, value: Box<TypedExpr> }   // likewise Define and MutWrite
Record(Vec<RecordEntry>)
VariantCtor { tag: Label, tag_occurrence: Occurrence, payload: Box<TypedExpr> }
Pattern { head: PatternHead, head_occurrence: Occurrence, binding: TypedBinding, empty_payload: bool }
```

`Occurrence` wraps a `NodeId` and gives it the two properties [Node identity](#node-identity) gives
a `TypedExpr`'s id. Its `Clone` goes through `provenance::copy_id`, which freshens the id and
reports the copy, or keeps the id inside `preserve_ids()`. Its `PartialEq` holds for any two
occurrences, so an occurrence is not part of a binder's value. `TypedBinding` and `TypedExprNode`
derive `Clone` and `PartialEq`, and a bare `NodeId` field under them would be copied verbatim by
every clone, putting two live binders on one id, and would take part in structural equality.
`content_hash` hashes a binder field by field (`hash_binding`), so it leaves the occurrence out
without a change.

An occurrence is a field of the node, beside the name it locates, and never part of the name's value
(`Name`, `Label`, `Type`). Those values are copied between terms and types by clones no recording
covers: the solver and planning clone labels outside any recording, so an occurrence inside a
`Label` would reach a later pane with no row that explains it, reported as `DanglingParent`.

A binder's identity stays its `Name`'s `Uid`. The occurrence records where the binder is written
and what it descends from. One `Uid` has several occurrences wherever a pass copies a binder, and
each copy resolves to the written name through `parents`.

Fields that hold a name the source does not write in that place get no occurrence: a
`TransactKey` and a writer's footprint, which are labels the compiler builds; `Run.name` and a
run's arguments, which linking replaces; `LetType.name`, which `uniquify` removes; and the names
inside a `Type` (`Type::Fun`'s parameter name, a Σ witness, a record or variant
type's labels).

A multi-parameter function's parameters and the fields of a constructor pattern in a `match` arm
bind nothing either. `uncurry_params` and `bind_parameters` substitute a projection for each use of
the name. Both tag each substituted projection `lower.param_proj` at the span of the name the
parameter or field declares, and keep the channel
[ir.md](ir.md#source-locations-on-substituted-parameter-projections) describes. A constructor's
fields in a one-field arm and in `N::c(a, b) = v` are binders, and get binding occurrences.

### Labels, pattern heads and annotations

A record literal's labels, a variant constructor's tag and a pattern's head are written once in the
source and held once in the term, so each gets an occurrence beside it. A label occurrence records
at the label's name, without its qualifier: `price` in `catalog::price=25`. A tag's occurrence
records at the tag's name, without its backtick, as the parser's `tag_span` gives it. A head
occurrence records at the tag's name for a `PatternHead::Tag`, and at the constructor's name for a
`PatternHead::Constructor`: `rect` in `case Shape::rect(w, h)`. The `Shape` segment is a type name,
which lowering resolves ([Names lowering resolves](lowering.md#names-lowering-resolves)).

A field access `p.x` lowers to `p ▷ .x`, and the `Proj` is a node, so it needs no occurrence.
Lowering tags the `Proj` at the span of `x`, not of `p.x`, and the `Apply` at the span of `p.x`. A
method call `v.m(a)` tags its `Method` node at `m` the same way. A field name resolves to no
definition, as a label does: the `x` of `Pt = {x: Int, y: Int}` is a label inside a `Type`, which
holds no occurrence.

A binder's annotation is a type expression, not a name, and its occurrence locates that expression:
`String` in `x: String = 5`, `{n: Int}` in `z: {n: Int} = y`. The occurrence sits in `Annotation`
beside the `Type`, so inference's clearing of a reconciled annotation drops the occurrence with it.
An annotation occurrence therefore lives from lowering to inference, and `pre-inference` is the
one pane that holds it. Inference reports `AnnotationMismatch` and `PolyAnnotationMismatch` at the
annotation's occurrence, so `x: String = 5` underlines `String`. Every other diagnostic about a
binder keeps blaming its binding node.

A structural label has no declaration: two records that write `price` share the label without
either declaring it. A label occurrence therefore resolves to no definition, and a consumer reads it
for the label's type in a pane and for the other occurrences of the same `Label`. A head
occurrence for a constructor resolves to the constructor's declaration, `NominalCtor.span`, which
the pattern's `PatternHead::Constructor` reaches through its `decl`.

### Minting and recording occurrences

| Where | What the occurrence gets |
|---|---|
| Lowering, a binder the source writes | A `LoweringStep::Leaf` at the name's span, labelled `lower.image`. The binder helpers (`let_bind*`, `lambda`, `for_loop`, `mut_decl`, `AssignmentBindings`, `PrefixStmt::Bind`) take the name with its span in place of a `String`. |
| Lowering, an applied occurrence, a label, a tag, a pattern head or an annotation | A `LoweringStep::Leaf` at the span the source writes it at, labelled `lower.image`. |
| Lowering, a binder the source does not write | A `tag_machinery` leaf at the span its node is tagged with: `__arg_tuple_N`, `__result_N`, the group-by and set binders, `OUTPUT_BINDER`, a constructor's argument, an absent payload. |
| `uniquify` | Nothing new. It renames binders in place, so every occurrence survives, and mints none. |
| A copy of a subtree | A fresh id and a copy row, from `Occurrence::clone`. `subst`'s transport, monomorphization and inlining need no change. |
| A binder a pass makes | A mint under the open recording, which becomes its parent: `__anf_N`, the reads `mut_read` names, `mut_elim`'s history and writer binders. |
| A binder a pass makes to stand for a source binder | A copy of the source binder's occurrence through `copy_id`, so it resolves to the written name rather than to the recording's node. |
| A throwaway (`Expr::throwaway`, `mem::take`) | `NodeId::PLACEHOLDER`, which the recorder ignores. |

The construction helpers outside lowering (`Expr::lambda`, `let_bind`, `mut_decl`,
`TypedBinding::new_*`) take the occurrence as an argument, a fresh mint or an existing binder's
occurrence, so every call states which it is. A helper that minted from a name would give a rebuilt
binder an occurrence parented on the open recording. The leak classes and the uniqueness check
accept that occurrence, because it is recorded and unique, and only the name-text check in
[Checking occurrences](#checking-occurrences) reports it.

A binder that stands for a source binder copies that binder's occurrence:

- `comprehension`'s `per_element_lambda` builds `λ target` twice per generator, in the main tree and
  in the loop-join predicate. One keeps the generator's occurrence and the other copies it.
- Each `channelize` companion lambda copies the original lambda's occurrence, and
  `mono.coalesce_let`'s per-specialization `let`s copy the generalized binder's.
- `mut_elim`'s final-value binder (`Name::fresh_like(&acc.name)`) copies the `MutDecl` binder's
  occurrence, which `AccumulatorVariable` carries. `channelize_cluster` keeps the defer binders'
  occurrences with their names, and `normalize_bare_write` receives a `MutWrite`'s
  `name_occurrence` with its name.

`transact_phase`'s `walk_spine` clones store bindings before the `transact.store` recording opens,
and `emit_group_member` clones a group member's binder only to write it back. Neither places a copy
beside its source, so both are preserving clones. Lowering's `MintedTerm::copy` copies group-by
terms with no `copy_frame`, and `tag_predicate`'s sweep explains those copies: it records the
occurrences it reaches as well as the expression ids.

`PayloadPattern::Named` holds the span of a `` case `tag(v) `` payload's name, so the payload's
binder records at its name like any other binder the source writes.

### Walking the ids with occurrences

Every walk that enumerates the ids of a tree reaches its occurrences, through one enumeration.
`TypedExpr::for_each_own_id` yields the node's id, the occurrence and the annotation's occurrence of
each binder `walk_binders` reaches, the `name_occurrence` of a `Feed`, `Define` or `MutWrite`, the
`label_occurrence` of each `Record` entry, a `VariantCtor`'s `tag_occurrence`, and each `Pattern`'s
`head_occurrence`. It is an exhaustive match, so a binding form added to the IR fails to compile
until it is covered. A tree-level walk built on it descends through `walk_children` and, when
asked, through `walk_type_slots` into refinement predicates, which can hold binders: the group-by
key predicate holds `λ x → x`.

| Walk | Route |
|---|---|
| `collect_tree_ids` | The tree-level walk, with predicates. It is the domain of the fold, of every pane's id set and deaths, of the lowering projection and of the leak gate, so each covers occurrences through it. |
| `collect_main_tree_ids`, `duplicate_node_ids`, the placeholder check in `assert_unique_node_ids` | The tree-level walk, without predicates. |
| `predicate_id_collisions`, `uniquify`'s `distinct_predicate_terms` | `for_each_own_id` within each term, under their own `Rc` dedup. |
| `uniquify::collect_node_ids` | The tree-level walk, keeping its `LetType` skip. |
| `enclosing`, `context.rs`'s fallback for `traced` | `for_each_own_id` per node, so an occurrence's enclosing node is the node that holds it. A blamed occurrence resolves through the projection first, so an annotation mismatch reports at the annotation. |
| `copied_nodes` (monomorphization's pairing of a clone with its definition) | The two nodes' `for_each_own_id` sequences, zipped. |
| `build_node_table` | Ships each occurrence as an entry of the pane's node table, a child of the node that holds it ([An occurrence on the wire](../../inspector_model/design.md#an-occurrence-on-the-wire)). |

Hot reload's `keep_region` and `Correspondence`, and `diff.rs`, leave occurrences out: their domain
is the expressions `diff` matches, and no operator is keyed by an occurrence.

The pane-link tests and both wire validators require every `paneLinks` endpoint to be an entry of
its pane's node table. A fold whose domain holds occurrences puts edges between occurrences in every
map, so `build_node_table` ships occurrences in the same change that widens `collect_tree_ids`.

### Checking occurrences

The existing checks cover occurrences once the walks reach them. An unrecorded occurrence is
`Unrecorded`, a copy no row explains is `DanglingParent`, and two binders on one id fail
`assert_unique_node_ids` at every boundary.

One check is new, because none of the existing ones can tell a carried occurrence from a fresh
mint. At every retained pane, each occurrence whose name has a source spelling resolves through the
pane's projection to a span whose text is that spelling. A name's source spelling is
`Name::source_spelling`, read through the source `Name` that a `SyntheticKind::Mono` carries. A name
with no source spelling, such as the `__result_N` a loop's `feed` names, is not checked. An
associated `def`'s binder and a constructor's binder are `N::f` while the source writes `f`, so the
check compares the part after `N::`. A binder minted under a recording where it should have copied
its source binder's occurrence resolves to the recording node's span, and the check reports it.

A label occurrence and a tag's occurrence compare the `Label`'s name, and a head occurrence the
tag's name or the constructor's name. An annotation occurrence has no spelling to compare: lowering
substitutes an alias by the type it names, so `Annotation.ty` does not render as the text the source
wrote. At `pre-inference`, the one pane that holds annotation occurrences, each one's row must have
`via` `Lower`: lowering minted it, and no pass between lowering and inference copies or rebuilds an
annotated binder. A re-mint under a later recording carries that recording's phase, and the check
reports it.

The inspector reads occurrences for go-to-definition and for a binder's type in each pane
([An occurrence on the wire](../../inspector_model/design.md#an-occurrence-on-the-wire),
[Definitions resolve over the IR](../../inspector_model/design.md#definitions-resolve-over-the-ir)).

## The provenance model

A `ProvenanceTable` stores one row per produced `NodeId`. Recordings populate the table during
rewriting; a post-phase tree diff does not construct the rows.

| Column | Meaning |
|---|---|
| `parents` | Ancestry: IDs from which this node was produced. |
| `blame` | Additional attribution: IDs related to the product without an ancestry claim. |
| `tag` | An interned `RewriteTag` containing the producing `Phase`, `Nature` and `RewriteLabel`. |

The columns describe the product, not the later fate of an input. A parent or blamed node may
survive in the output tree. Naming a surviving node as a parent gives an overly broad ancestry
edge, not a death report. The fold reports deaths from the difference between input and output
ID sets.

One parent can describe either one product or several products with the same parent. Several
parents describe fusion. A pure insertion may have no parents if its blame column anchors it.
An in-place rewrite that retains its ID writes no new row; the fold can relate an unchanged ID
to itself.

The table stores no source spans. Attribution resolves through parents and then distinct blame
additions, using the available upstream projection. A blame edge can add a span absent from the
parents. For example, `mut_elim` can name a statement as the parent and blame the enclosing loop
keyword. The node relation retains the two edge labels so a consumer can distinguish ancestry
from related source material; [The edge labels](#the-edge-labels) specifies composition.

### Table access and write invariants

`parents` and `blame` return empty slices for an unrecorded ID; `tag` and `tag_id` return
`None`. An allocated or addressed ID need not have a row in this table. The backing store is
a `HashMap` with a separate tag-interning table. Paged or delta-encoded storage remains a
possible representation change, not the implemented layout.

`ProvenanceTable::record` debug-asserts three write preconditions:

- The produced ID has no previous row. Attribution has one rewrite tag and no join for two
  competing producers.
- At least one of `parents` or `blame` is nonempty.
- The produced ID is not one of its own parents.

The row insertion is unconditional; these checks are not release-build validation. Several
recordings may name the same input ID because they produce distinct output IDs. The same input
may also appear as a parent in later recordings.

`tag_in(id, phases)` exposes a row only when its producing phase is selected.
The fold must stop at an input pane's IDs rather than following their rows from earlier phases.
Private `rows_in` enumerates recorded rows in a phase set, not the process-wide ID key space.

`deaths(start, end, live)` returns sorted recorded IDs produced in the inclusive phase range
and absent from `live`; a reversed range triggers a debug assertion. This differs from the
fold's `input_ids ∖ output_ids`: the table query includes intra-span products later discarded,
while the fold can report the loss of an input node produced before the selected phases.

Predicate IDs use the same row representation. `PredMemo` records derived predicates against
their source terms; copies raised into the main tree keep their predicate origins.
The [predicate traversal contract](#walking-the-ids) specifies the required sharing.

### The recorder

`RECORDING_STACK` is a thread-local stack of open recordings.
`Expr::new` calls `on_mint`; expression cloning reaches `on_copy`.
Each hook captures into the innermost frame. A mint has that recording's named node and extra
consumed IDs as parents. A copy instead has its own origin as its sole parent and no added blame.
Naming blame on the enclosing recording therefore widens its minted products, not its copies.

A recording is opened before the local rewrite and held until its products have been built:

```rust
let _g = provenance::enter(named_id, "inline.beta", Nature::Machinery);
```

`named_id` identifies the input before rewriting; the guard does not inspect the output value.
This works for both consuming and in-place rewrites. An attempt that mints and copies nothing
writes no row. Nesting assigns each product to the innermost recording active when its hook runs.

Closing a guard first appends to an active `DerivationLog`, if present. It then routes the
captured products to the active lowering log, or otherwise to the active phase's table.
Without either sink, captured events produce no table or lowering rows.
A `TableSession` alone does not supply the phase or open a recording.

The installed scopes have different lifetimes:

| Scope | Installed state and lifetime |
|---|---|
| `TableSession` | One table for the compile when provenance capture is enabled. |
| `PhaseScope` | The ambient producing phase for the enclosed phase's recordings. |
| `LoweringSession` | The always-on lowering log, drained at the lowering handoff. |
| `DerivationSession` | A phase-local log for error attribution, also written when table capture is disabled. |

Session installation is non-reentrant, checked with debug assertions. A phase scope cannot open
while lowering's log is installed. A derivation session also excludes lowering. Guards clear
their installed state on drop, including ordinary unwinding.

The mint and copy hooks ignore `NodeId::PLACEHOLDER`. Outside lowering, they debug-assert that
an active phase has an open recording to capture each event. Without that phase, an uncaptured
event is permitted and writes nothing. The coverage assertion checks the open frame, not the
correctness of the node it names.

`RecordingGuard` provides two additional channels:

- `also_consumes(id)` adds an ancestor for minted products, supporting fusion. It ignores the
  placeholder sentinel. It is not a death declaration.
- `blame(ids)` adds related IDs whose spans augment the minted products' ancestry attribution.

Both methods require their guard to be innermost; a debug assertion checks its stack depth.
Drop has the same LIFO precondition. In release builds these assertions do not protect a caller
that addresses or drops the wrong frame.

`copy_frame(label)` opens a recording with no named node and `Nature::Machinery`.
It is for standalone duplication: each copy hook supplies the origin that the frame lacks.
It cannot capture consumed IDs or mints; `assert_copy_only` debug-asserts that restriction.
A rewrite that also creates nodes uses `enter` instead.
Under lowering, captured copies become `LoweringStep::Copy` entries; their folded attribution
mirrors the origin verbatim. Under a phase scope, each copy becomes its own table row.

Lowering leaf mints use `lowering_leaf` directly, supplying a literal source span.
`lowering_predicate_leaf` skips already-recorded IDs so a sweep does not overwrite precise
existing attribution. `fold_lowering` processes the log at the lowering handoff.
The distinct log and fold contracts are specified under [The seam](#the-seam).

`PANES` in `src/ccl/panes.rs` and the phase scopes opened by `compile_program` in
`src/ccl/context.rs` define the retained boundaries and the phases whose recordings each pair
folds. Lowering records leaf appends and copies through its separate log. Rewrite labels are
supplied at recording sites, not enumerated here.

Table capture is enabled by default and disabled by `CAMBRA_PROVENANCE=0` or a named audit span.
When enabled, pipeline boundaries install the phase scopes. Shared helpers record under their
caller's phase, not under a phase inferred from the helper's module or label.
A phase that produces no nodes writes no rows.

An audit selected by `CAMBRA_PROVENANCE_AUDIT` opens its own scope over the chosen span and
prints coverage and leak measurements on completion. Naming an audit disables ordinary pane
capture so the two modes do not install competing phase scopes.
See [Gate and audit coverage](#gate-and-audit-coverage) for endpoints and configuration.

### Where to open a recording

A recording names the node whose rewrite produces the captured material. It surrounds the
local rewrite, after recursive child work and early returns that abandon the rewrite.
If every recursive frame opens its own recording, an outer frame may surround recursion:
the inner frame captures its own products while it is active. Operator conversion uses this
pattern through `converting`; [Operator conversion](#operator-conversion) specifies it.

A rule-table wrapper can record every attempt:

```rust
fn ruled(label: RewriteLabel, expr: &mut Expr, rule: impl FnOnce(&mut Expr) -> bool) -> bool {
    let _g = provenance::enter(expr.node_id(), label, Nature::Machinery);
    rule(expr)
}
```

A declined rule costs a push and pop but writes nothing if it minted or copied nothing.
The recorder does not use the returned Boolean. A consuming traversal reads the input ID
before destructuring the node; the ID is sufficient to open the recording.

The recording's scope follows the attribution required by its products:

- A product replacing several constructs names their enclosing input node, not a synthetic
  stand-in minted only for attribution.
- A recording may name a node just produced by this phase, provided its creation was recorded.
  The fold then composes that intermediate ancestry.
- Arms with different `Nature` values open separate recordings on the same input ID.
  Each recording carries one nature and label and writes its own products.
- An expansion with products attributable to different source constructs opens nested recordings
  per construct. `mut_elim` records accumulator slots and feeds inside the enclosing loop.
  The outer recording retains only the products it builds outside those nested scopes.

An accumulator slot can represent several writes to one variable. Its recording names the first
write and blames later writes; all contribute attribution, but only the named write contributes
ancestry. Conversely, one product spanning several constructs cannot be divided into per-construct
products: a conditional feed's lambda over the loop body stays on the enclosing recording.

When an enclosing construct mints nothing, its source can still be blamed by its children's
products. An accumulator-free mutation loop uses `StmtSite::blamed_in` for that case.
A recording does not manufacture an ancestry edge merely to make the enclosing construct visible.

#### Choosing between `Expansion` and `Machinery`

`Expansion` identifies products that express the source construct's meaning.
`Machinery` identifies an implementation strategy or administrative transformation.
The choice is made at each recording site and carried into attribution.

`planning.groupby` is `Expansion`: its bucketize chain implements the meaning of `groupby`.
`planning.hash_join` is `Machinery`: an equality-refined comprehension admits that strategy,
with iteration and restriction as the fallback when recognition does not apply.
`lambda_elim.filter` is `Expansion` because the guard becomes a domain refinement;
algebraic simplification is `Machinery`.

`Nature::Source` is lowering-only and marks a lowered source expression's root.
The phase-table attribution helper debug-asserts that a phase row does not use it.
`planning_labels_carry_their_declared_nature` checks the group-by and hash-join labels.

An empty leak vector checks recording coverage, not attribution precision. A recording on the
program root can explain IDs while attributing them to the wrong source construct. Recording-site
correctness therefore needs source-specific tests as well as the fold's structural checks.

### The fold

`fold(table, phases, input_ids, output_ids, upstream_attr)` returns four products:

| Product | Meaning |
|---|---|
| `ProvenanceMap<NodeId, NodeId>` | Bidirectional, labelled relation from input IDs to output IDs. |
| `SourceProjection` | Available source attribution restricted to output IDs. |
| Deaths | Sorted `input_ids ∖ output_ids`, independent of the recorded rows. |
| Leaks | Sorted, deduplicated recording-integrity failures. |

Only rows tagged with a phase in `phases` participate. An input node's row from an earlier
phase is not followed: the relation stops at this fold's input boundary. Recorded intermediate
nodes compose away from the emitted relation when they are absent from the output.

An input ID with no selected row contributes an ancestry self-edge if it survives into the
output. Its attribution passes through unchanged. Re-minting a pass-through node instead
creates a new ID and records a rewrite, so a consumer cannot distinguish that case from other
rewrites by identity alone.

#### The edge labels

Each endpoint pair has one nonempty set of labels. A `parents` hop contributes ancestry;
a `blame` hop contributes relatedness without ancestry. Naming the same ID in both columns
produces one hop with both labels.

Path composition is defined by `EdgeLabels::then`:

- Ancestry is present only if both the accumulated path and the next hop have ancestry.
- Blame is present if either the accumulated path or the next hop has blame.

Alternative paths between the same endpoints union their labels. Thus a pair can carry both
labels, whether one hop has both or separate paths supply them. An ancestry-only self-edge
is the identity for path composition.

Unknown ancestry endpoints produce `DanglingParent`. Unknown blame-only endpoints contribute
neither an edge nor a leak. Source attribution likewise ignores unknown source IDs, but combines
known spans from both columns.

#### The fold is order-free

The table's row insertion order does not determine the result. Recordings flush when their
guards close, so an enclosing rewrite can write its rows after nested rewrites have written
rows for later products.

The fold uses these sets:

- Vertices: selected rows' IDs together with `input_ids`.
- Roots of a vertex: input IDs reachable through its parents or blame, with path labels.
- Attribution: upstream entries extended with each selected row's derived attribution.

Before the sweep, every vertex without a selected row is assigned itself as an ancestry root.
These are input-boundary nodes. Pre-seeding them permits a selected row to name an input ID
greater than its own ID, as can happen when operator conversion reuses an existing operator.

Selected rows are then processed in ascending `NodeId` order. A dependency whose upstream ID
also has a selected row must have a smaller ID than its product. The sweep debug-asserts this
condition for both parent and blame hops. Dependencies on pre-seeded input IDs need not satisfy
that numerical order. One row per product and this ordering requirement permit a single sweep;
monotone allocation alone does not validate every manually constructed row.

For a selected row `x`, the fold extends each upstream root's path label by the hop into `x`
and unions labels at common roots. A recorded vertex retains an entry even if its root map is
empty. This distinguishes known material with no input ancestry from an unknown output ID.

Label union is associative, commutative and idempotent; path composition distributes over it.
Together with unique rows and the dependency ordering, these properties make the relation
independent of row insertion order. Attribution also requires unique rows: competing rewrite
tags have no merge operation.

`sweep_metrics` counts vertices, distinct upstream hops per row and dependencies that violate
the selected-row ordering. Its `backward_edges` count is a count of edges, not vertices to revisit
or the cost of a hypothetical fixed-point algorithm.
`the_write_order_of_the_rows_does_not_change_the_fold` checks insertion-order independence.

#### Source attribution

A row's attribution combines spans from its parents in order, then from its blame IDs in order,
retaining the first occurrence of each span. Unknown source IDs contribute nothing.
The row's tag becomes the product's `rewritten` tag; it is not inherited from its parents.

An attributed node may have an empty span vector. This is distinct from an ID absent from the
projection. At the output boundary, the fold retains only entries for `output_ids`; it does
not create an entry for an output whose attribution is unknown.

`SourceAttribution::rewritten` is mandatory. `RewriteTag::direct_image()` represents a lowered
expression root with `{via: Lower, nature: Source, label: "lower.image"}`.
A preserved ID can carry that tag through later panes. A new phase row must not use
`Nature::Source`; `attribute` debug-asserts the restriction. Wire encoding is owned by
[The inspector consumers](#the-inspector-consumers-srcinspector_model), not the fold.

#### Recording leaks

The two leak classes identify where missing recording becomes visible:

| Leak | Detection |
|---|---|
| `Unrecorded { output }` | An output ID is neither an input ID nor the product of a selected row. |
| `DanglingParent { parent }` | A selected row names an ancestry ID absent from the input and selected products. |

`DanglingParent` is checked while visiting every selected row, including rows whose products
do not survive into the output. `Unrecorded` is checked only for output IDs. A missing mint
can therefore cause either class or both, depending on whether it survives or is named by
another row. Neither class alone identifies the missing recording site.

Zero `Unrecorded` entries do not prove that every mint was recorded: an unrecorded intermediate
may have been discarded or may appear only as a dangling parent. Likewise, zero leaks establish
neither precise attribution nor correctness of the rewritten program.

Leaks are deduplicated by class and ID, so several rows naming one unknown parent produce one
`DanglingParent` entry. Deaths are a separate product, not an error. Duplicate live IDs are
checked by the tree-identity checks under [Node identity](#node-identity), not by the fold.

There is no requirement that every recorded product survive. A substitution template can be
recorded, copied into several occurrences and then discarded. Its row still explains the
copies. Unused rows are permitted; a row with an unknown parent is still checked even when
its product is unused. Write-time row preconditions are specified under
[Table access and write invariants](#table-access-and-write-invariants).

`fold_lowering` uses a sequential log rather than this phase-filtered table algorithm.
Its last-write-wins attribution and copy ordering are specified under [The seam](#the-seam).

### Gate and audit coverage

`gate_leaks` asserts that a fold's leak vector is empty when either `debug_assertions` or
`test` is enabled. It returns without asserting otherwise. Lowering always computes its
projection and calls this gate at the handoff.

Later pair checking has two entry points:

- `pane_pair_folds_have_no_structural_leaks` checks the pipeline corpus's gated pairs.
- `compile_program` materializes and checks gated pairs when the environment enables it.

All current adjacent pairs in `PANES` are marked gated, including the operator-conversion pair.
This marks which assertions to run; it does not prove coverage for untested programs.
A new pair must cover its producers' recording before its gate can require zero leaks.

The environment switches are read by the accessors in `context.rs`:

| Variable | Behavior |
|---|---|
| `CAMBRA_PROVENANCE=0` | Disable ordinary phase-table capture; snapshots and diagnostic projections remain. |
| `CAMBRA_PROVENANCE_GATE` | A set value other than `0` enables pair materialization/checking, provided ordinary capture is enabled. |
| `CAMBRA_PROVENANCE_AUDIT` | Select a named audit span and disable ordinary phase scopes. |
| `CAMBRA_PROVENANCE_PREDICATES=0` | Exclude predicate interiors from audit ID sets only. |

An unset gate variable leaves per-compile pair checking off. CI's test job sets it to `1`.
Disabling capture or setting an audit variable suppresses that gate even if its variable is set.
An unrecognized audit name still disables ordinary capture but matches no audit span.

Audit predicate inclusion defaults on, matching pane enumeration. Turning it off can report
dangling parents for predicate IDs that were recorded correctly but omitted from the audit's
input set. That comparison measures the narrower domain, not missing compiler instrumentation.

#### What gating every pair does not retire

`ProvenanceAudit` measures selected pipeline spans rather than asserting zero leaks:

| Name | Input | Output | Included work |
|---|---|---|---|
| `full` | Post-inference | Post-planning (`join_planned`) | Inlining through planning. |
| `letrec` | Post-inference | Post-letrec | Inlining, transaction lowering and induction lowering. |
| `mutelim` | Post-transact | Post-letrec | Induction lowering. |

The `full` audit stops before operator conversion even though that phase has node identities
and a gated pane pair. The name does not mean every compiler phase is included.
The narrower spans remain useful because their endpoints are not both retained panes.

An enabled audit opens one `PhaseScope` over its whole span with nominal tag
`AUDIT_VIA = Phase::Planning`. This is a grouping key, not the actual phase of each rewrite.
The audit closes its scope, reads the active table, and folds with an empty upstream projection.
Its report includes row, input, output, attributed-entry and death counts, plus leak counts.
An attributed entry need not have known spans.

The audit's table must remain installed until measurement completes. Ordinary capture and
audit scopes are mutually exclusive because phase scopes are non-reentrant.
Changing an audit endpoint requires checking which producers it includes; it need not follow
a pane boundary. `PaneSpec::gated` remains a per-pair assertion setting independently of audits.

## The seam

Lowering and phase rewriting have different attribution inputs. Lowering knows literal source
spans; later phases name existing nodes whose spans must be resolved. They therefore use separate
logs and folds. The phase table supplies relations between retained pipeline snapshots, while
the always-on lowering and derivation projections support error reporting even without that table.

### Lowering attribution

`LoweringSession` is installed throughout lowering in every build. Leaf-tagging helpers append
one `LoweringStep::Leaf` with a node ID, literal span, nature and label. Ordinary mint hooks do
not create these leaf records. Copy-only frames capture freshened template interiors and
reused comparison operands as `LoweringStep::Copy` entries.

`Nature::Source` marks the root returned by lowering a `Spanned<ChlExpr>`.
The `lower_expr` wrapper calls `tag_source` after the arm returns, so its leaf entry replaces
any earlier attribution for that root when the log is folded. Interior nodes and statement-level
images do not receive Source merely because they correspond to source text. Conversely, a
generated wrapper at an expression's root receives Source even if that wrapper was not written.

Lowering uses these tags:

| Helper | Nature | Label |
|---|---|---|
| `tag_source` | `Source` | `"lower.image"` |
| `tag_image` | `Machinery` | `"lower.image"` |
| `tag_machinery` | `Machinery` | The supplied rule label. |

`tag_image` records a lowering site's classification of an image. The label does not establish
a cross-site one-to-one correspondence with a written construct. Nature alone also does not
separate interior images from generated material: both use Machinery. The nature/label taxonomy
remains provisional; consumers must rely on the stated guarantees rather than infer a finer
classification from those names. Source nature does affect the inspector's null encoding.

`tag_predicate` visits a finished predicate before it is placed in a refinement type.
It records missing leaf attribution without replacing entries already supplied by the predicate's
subexpressions. This preserves their narrower spans and tags; structural leak checks would not
detect a replacement by a coarser but present attribution.

### The lowering fold

`fold_lowering(log, output_ids)` reads the log in order:

- A leaf establishes the ID and assigns its literal span and tag, with `via: Lower`.
  A later leaf for the same ID replaces that attribution.
- A copy requires its origin to have been established earlier. Each produced ID receives the
  origin's complete attribution, including its tag.
- A copy with an unknown origin reports `DanglingParent` and does not establish its products.
- An output ID not established by either kind of record reports `Unrecorded`.

The returned projection is restricted to `output_ids`; leak entries are sorted and deduplicated.
A recorded template can be copied and then discarded without a leak. Lowering has no input
pane, relation output or death set. Unlike table rows, its repeated leaf records have defined
last-write-wins semantics. Log order therefore matters.

The pipeline drains and folds the lowering log before uniquification and later phase scopes.
Its output IDs are the union of `collect_tree_ids` for the linked program and each module's
standalone check tree, including predicate interiors. It retains the result as
`CompiledProgram::lowering_projection`. The fold runs in release builds because
diagnostics need its result. Boundary uniqueness and leak assertions are debug/test checks;
they do not make release builds reject a missing record.

### The derivation log

A phase under `DerivationSession` appends closed recordings to a `DerivationLog`, independently
of table capture. The comprehension phase uses it so errors on its generated nodes can resolve
to source spans even when `compile_to` does not capture provenance rows.

`fold_derivation(log, base, via)` processes closing order. It looks up an input in `base` first,
then in the projection already built by this fold. A mint copies its named input's spans and
uses the recording's nature and label with the supplied phase. A copy mirrors its origin's
complete attribution. If neither lookup finds the named input or origin, the step adds no
entries; there is no leak result from this fold.

Dependencies must therefore be available in the base projection or from an earlier log step.
An inner recording closes before its enclosing recording, so the latter can use the former's
products. This is not the table fold's insertion-order-independent algorithm.

Recordings under a derivation session must not add extra consumed IDs or blame.
`log_derivation` debug-asserts that restriction because the derivation fold attributes births
only to their named input. Logging those extra channels without folding them would make this
projection narrower than table attribution.

### Error attribution

`Blame` resolves a `Located` error's node in this order:

1. Look up the node in the lowering projection, then the accumulated derivation projection.
   Use the selected entry's first span.
2. If no span was found, breadth-first search the active table's parents and blame IDs.
   For each visited node, parents precede blame; already-visited IDs are skipped.
3. If a containing expression tree was supplied, search its enclosing nodes nearest-first
   for a projected span. Predicate nodes in type slots are enclosed by the expression holding
   the slot.
4. If no source is found, panic in debug builds; otherwise use the whole root-file span.

An existing attribution with no spans does not resolve an error. The fallback table walk requires
an active table, so capture-disabled compiles rely on projections and the optional enclosing tree.
The derivation projection supplements lowering; it does not replace it.

Standalone module checks share the lowering projection but accumulate separate derivation
projections through `Blame::fresh`. Linked-program diagnostics also use `RunSites` to label the
statements that bring in a run's copy. Attribution supplies the primary source span;
[module diagnostics](../../../docs/modules.md#diagnostics) specifies copy-error merging and
secondary run/import labels.

### Retained snapshots

`PANES` is the authoritative ordered topology. Its first entry anchors materialization at
`pre-inference`; each later entry declares the phases since its predecessor.
The `CompiledProgram` fields retain these boundaries:

| Snapshot | Boundary and content |
|---|---|
| `pre_inference_ir` | After uniquification, before A-normalization; unresolved expression types. |
| `post_inference_ir` | After inference and its checks, before inlining; typed expressions with lambdas. |
| `post_channelize_ir` | After inlining, transaction/induction lowering and channelization. |
| `post_as_of_read_ir` | After the fed-out mutable-read rewrite. |
| `post_lambda_elim_ir` | After explicit lambdas are converted to point-free combinators. |
| `ast` | After planning; retained in a stable allocation for the expression-to-operator map. |
| `operator_graph` | After conversion, captured before subscription consumes graph inputs. |

Snapshots clone with IDs preserved; they observe the same nodes rather than create new products.
The first snapshot precedes A-normalization so its IDs can use the lowering projection.
New A-normalization products are explained by the first pair's selected rows.
Uniquification can remove `LetType` nodes, and standalone module-check trees are not retained
panes. The lowering projection can therefore contain keys absent from the first snapshot.

`pane_trees` supplies the expression snapshots in topology order. `IR_PANE_COUNT` and its
compile-time assertion require IR entries to precede operator entries and match the array's arity.
`pane_ids` uses the predicate-inclusive expression walk for IR panes and graph IDs for operators.
`every_recorded_phase_belongs_to_exactly_one_pane_pair` checks corpus-recorded phases against
the declared phase sets.

### Pane materialization

`CompiledProgram::materialize_panes` uses `PANES` to fold each adjacent snapshot pair.
The first projection is the lowering projection. Each later pair uses the preceding projection
and its declared phase set. It returns maps, projections, deaths and leaks without asserting
that the leaks are empty. The inspector and the compile-time leak gate both use this operation.

[Gate and audit coverage](#gate-and-audit-coverage) owns assertion configuration and audit spans.
[Operator conversion](#operator-conversion) specifies the non-expression output domain.

## Operator conversion

The final pair relates post-planning expression IDs to post-conversion operator-graph IDs.
`Phase::Convert` writes provenance rows using the same `NodeId` domain as expression phases.
`PaneSpec::content` selects expression-tree or operator-graph enumeration; the fold itself
accepts ID sets and does not inspect either representation.

Conversion opens a recording per expression frame through `converting`. A nested frame
captures its own operators. Products constructed after a child returns are attributed to the
parent frame unless the site opens a finer recording, as per-writer commit-store construction
does. The operator graph includes output sink nodes, which also have identities and attribution.

Graph-edge recording is distinct from provenance parent recording. Deferred inputs are registered
when a `CycleSlot` is filled. The graph is captured before subscription takes slots and keyed
inputs; a later traversal cannot recover those consumed inputs. The graph is retained even when
phase-table capture is disabled.

Planning's predicate-to-term copies use predicate origins, as specified under
[Walking the ids](#walking-the-ids). They do not need an operator-conversion attribution rule.

## The inspector consumers (`src/inspector_model/`)

The inspector model consumes pane projections and relations. Its
[design reference](../../inspector_model/design.md) owns payload shape, queries and schema
versioning. This section specifies only the boundary with provenance.

`build_node_table` uses each available attribution's spans and tag. `wire_spans` orders spans
by length and then position/file; it does not preserve the fold's parent-first span order.
`rewrite_info` encodes a Source-nature tag as null and other tags as `{via, nature, label}`.
An absent attribution also leaves the node's spans empty and its wire tag null; consumers cannot
infer presence of an internal attribution from null alone.

`dense_edges` emits every relation endpoint pair, including self-edges, but omits edge labels.
The wire therefore does not distinguish ancestry from blame. Endpoint membership is checked by
producer tests and payload validation. Predicate interiors are node-table entries and relation
endpoints, following the [ID traversal contract](#walking-the-ids).

**Planned:** name occurrences are node-table entries and relation endpoints too
([Name occurrences](#name-occurrences)).

The payload's `meta.schema` belongs to the inspector protocol. The CCL layer supplies identities,
attributions and relations without depending on that version number.

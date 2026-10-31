# Dependent types

A CCL type can read a term or a binder: a function's result can depend on its argument, a
collection's domain can be some member of a kind, and a tuple's component can depend on the
components before it. This document maps those forms. For each it says what binds, how a reference
to the binder is stored, and what eliminates it, and it follows a dependent type through the
pipeline. The mechanisms themselves are specified in the sections it links.

## The forms

| Form | Written | Binds, over | A reference is stored as | Eliminated by | Specified in |
| --- | --- | --- | --- | --- | --- |
| Pi function | `(𝑥 : 𝐴) ⇒ 𝐵`, or `(𝑥 : 𝐴) ⤇ 𝐵` for a collection: `Type::Fun` with a `name` | `𝑥`, over the codomain | `Name::PiBound`, an index of binder crossings; a name while opened | application, which discharges `𝑥` to the argument | [4.5](type-inference.md#45-dependent-refinements-via-pi-types) |
| Refinement | `{𝐵 \| 𝑝}` | `__elem`, over the predicate | `__elem^𝑛`, `𝑛` counting the refinements crossed | nothing; a substitution reaching it rewrites the predicate (`Subst::force_refinement`) | [A refinement's element is referenced by index](type-inference.md#a-refinements-element-is-referenced-by-index) |
| Dependent tuple | `(𝑎 : 𝐴) × 𝐷(𝑎)`: `Type::DepTuple` | each component, over the components after it | `Name::PiBound`, as in a Pi | projection `𝑝.𝑘`, which opens component `𝑘` at the projections before it | [4.8](type-inference.md#48-dependent-tuples) |
| Dependent sum | `Σ (σ : 𝐾). 𝐷 ⤇ 𝑉`: a data `FunKind` carrying witnesses | the witness `σ`, over the sum's own type only | `Type::WitnessRef`, by id | `unbox(𝑐)` and `σᵢ(𝑐)`, through a term; planning realizes a conditional or erases a determined witness | [4.7](type-inference.md#47-dependent-sums) |
| Witness projection | `σᵢ(𝑐)`: `Type::WitnessProjection` | nothing; it quotes the term `𝑐` | the term, compared by normal form, and the binder's position | erasure of a determined witness, to its candidate | [Projecting a sum's witness](collections.md#projecting-a-sums-witness) |
| History | `(𝑘 : 𝐷) ⤇ 𝑉` inside `Type::History` | the position `𝑘`, over the value | as in a Pi | mutability elimination and `channelize`, which erase the history to its function | [A history's value may depend on its position](type-inference.md#a-historys-value-may-depend-on-its-position) |
| Generalized type | `∀ (𝐷 <: 𝑇). …`: `Type::Poly` over generalized `Type::Param`s | its parameters, over the type | `Type::Param` | the check, which instantiates it at each use | [Generalized types](type-parameters.md#generalized-types) |
| Family application | `𝐷₁(𝑘)`: `Type::FamilyApp` | nothing; it applies a family parameter to binders of the type around it | the parameter and its argument terms | instantiation, which binds the family to a type over the binders it pairs with | [Generalized types](type-parameters.md#generalized-types) |

A term quoted in a type, such as a predicate, a projection's term or a family's argument, keeps its
own binders named, and two such terms compare with their interior binders paired by position
([Interior term binders stay named, and compare by position](type-inference.md#interior-term-binders-stay-named-and-compare-by-position)).

`List`, `Set`, `Map` and `Collection` annotations are sums over a kind
([The six collection types](collections.md#the-six-collection-types)).

## What binds where

One rule says which names a stored type may hold, at every phase:
[Every stored type is well-scoped](ir.md#every-stored-type-is-well-scoped). Two mechanisms keep it
while inference runs:

- **Term binders.** An inference variable carries the telescope of term binders it was minted
  under and resolves to a type naming those binders and nothing else
  ([The invariant](type-inference.md#the-invariant)). The solver checks each bound against its
  holder's telescope as the edge records it.
- **Witnesses.** A sum binds its witnesses within its own type, so a type outside the sum names one
  only through a term, as `σᵢ(𝑐)`. Comparing two sums puts their binders in correspondence
  positionally ([The witness context](type-inference.md#the-witness-context)).

A stored type spells a reference to a binder inside it as an index and one to a binder around it as
a name ([A binder reference is stored in one of two
forms](type-inference.md#a-binder-reference-is-stored-in-one-of-two-forms)). [Closing and opening
stored binders](type-inference.md#closing-and-opening-stored-binders) says where each conversion
runs.

## Moving a type across a binder

A `Subst` carries a type from one scope to another. Its entries are a rename, a discharge (a
binder replaced by a term, which is applying a dependent type to an argument), a join (a binder
whose values a contribution is joined over), a witness rename or discharge, and an elimination,
which reads a sum through a term
([Substitution and bound transport](type-inference.md#substitution-and-bound-transport),
[An elimination reads a sum through a term](type-inference.md#an-elimination-reads-a-sum-through-a-term)).
A substitution that reaches an unresolved inference variable stands for the variable under it, a
suspension
([A substitution reaching a variable suspends on it](type-inference.md#a-substitution-reaching-a-variable-suspends-on-it)).

Each binder has its own exit when a type leaves its scope
([A type leaving a binder's scope](type-inference.md#a-type-leaving-a-binders-scope)).

## Through the pipeline

1. **Lowering** writes a collection annotation's sum, and the comprehension encoding writes each
   filter as a refinement its `cast` acquires
   ([`Cast` — explicit refinement acquisition](ir.md#cast--explicit-refinement-acquisition)).
2. **Inference** names a lambda's parameter as its Pi binder and discharges it at each application.
   `box` introduces a sum, `unbox` eliminates one, and `uncurry(𝑛)` keys a flattened comprehension
   by a dependent tuple. A feed keyed by the positions of the loops around it has a history whose
   value reads them. A sum's kinds are decided where the types holding them materialize ([Membership
   is decided at materialization](type-inference.md#membership-is-decided-at-materialization)).
   Coalescing closes the references to binders inside each type it materializes to indices. A
   specialization stands under the binders its instance reads ([A specialization stands where its
   types are in scope](type-inference.md#a-specialization-stands-where-its-types-are-in-scope)).
3. **The post-inference check** derives every node's type again by the same rules, and after
   planning it takes a dependent result as recorded
   ([After planning, a dependent result is the recorded one](type-inference.md#after-planning-a-dependent-result-is-the-recorded-one)).
4. **Lambda elimination** gives a body whose type alone reads the parameter the Pi-constant form
   ([A parameter only the type reads: the Pi-constant form](optimization.md#a-parameter-only-the-type-reads-the-pi-constant-form)),
   and packs two binders whose second reads the first into a dependent tuple
   ([Where a dependent tuple is born](type-inference.md#where-a-dependent-tuple-is-born)). A
   morphism lifted out of a binder's scope whose type still names the binder is given a generalized
   type, a family where the named part also reads the type's own binders
   ([Generalized types](type-parameters.md#generalized-types)).
5. **Planning** realizes a conditional collection where it stands and erases determined witnesses
   ([Which `Case` a site realizes, and what a leg instantiates](type-inference.md#which-case-a-site-realizes-and-what-a-leg-instantiates)),
   and iterates a dependent tuple through a family of keys, one collection per row
   ([Iterating a dependent tuple](type-inference.md#iterating-a-dependent-tuple)).
6. **Operator conversion** bounds a projected witness by its witness's key bound and a dependent
   tuple component by component (`extent_of`), and runs a family of keys beneath the levels standing
   over it.

## Vocabulary

| Term | Meaning |
| --- | --- |
| Telescope | The term binders an inference variable may name, in the order entered; also a dependent tuple, whose components bind in order. |
| Discharge | Replacing a binder by a term: applying a dependent type to an argument. |
| Join | Taking a contribution's type over every value of a binder it crosses. |
| Suspension | The variable standing for an unresolved variable under a substitution. |
| Elimination | Reading a sum through a term: `unbox(𝑐)`, whose binders become `σᵢ(𝑐)`. |
| Witness | A sum's binder, standing for the domain a value has. |
| Type kind | What a witness ranges over: candidates, every dense range, the subtypes of a type, or every type. |
| Funkind | A function's data or compute kind, carrying a sum's witnesses; a funkind variable is one not settled yet. |
| Pi-constant form | `const(body) : (𝑥 : 𝐷) ⇒ body.ty`, a lambda whose parameter only the body's type reads. |
| Generalized parameter | A parameter standing for a part of a lifted morphism's type that named a binder out of scope. |
| Family | A generalized parameter taking terms, one type per value of the binders it is applied to. |

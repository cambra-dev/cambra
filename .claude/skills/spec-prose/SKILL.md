---
name: spec-prose
description: Write or revise prose in a design doc, a doc comment, or a code comment so it reads as specification rather than as a blog post. Use when adding or editing a `*/design*.md` section, a `///`/`//!` doc comment, a module-level comment, or any explanatory prose in this repo.
---

# Specification prose

The reader arrives to look one thing up and already knows they need it. Lead with the claim and
stop.

The rules are
[Prose style: specifications, not blog posts](../../../CLAUDE.md#prose-style-specifications-not-blog-posts).
This skill is what to do at the keyboard: the transformations, the voice to avoid, and the
exemplars to imitate. None of it is a metric — a sentence is not better for being short, and a
document is not conforming for containing no banned words.

## Imitate these, not the nearest paragraph

Before writing a doc section, read the scalar and function paragraphs under
[Instances](../../../docs/operational-semantics/semantics.md#instances). They introduce each
representation, define combination, and state completion conditions. Use the examples under
[Linear sentence structure](#linear-sentence-structure) for sentence shape. These selections do
not endorse the surrounding documents as uniformly good style.

The dense design docs carry the content you need but not the form:
`src/ccl/design/type-inference.md`, `mutability.md`, `provenance.md`. Take facts from them, not
sentence shape.

## Voice

Specification prose has no speaker. The failure that reads most like a blog post is a voice in the
text — stress, evaluation, and argument, all of which ask the reader to hear a person rather than
read a claim.

**Stress italics.** The design docs italicize `is` and `not` dozens of times. Italicizing a copula
is the written form of leaning in and saying it aloud.

> Before (`mutability.md`): a watermark *is* a `domain_predicate` advancing over `Txn`

> After: a watermark is a `domain_predicate` advancing over `Txn`

Nothing was lost, which is the tell: the stress was doing no work. Where stress carries a real
contrast, name the contrast instead of marking it.

> Before: the read is that accumulator's **final** value

> After: the read is that accumulator's final value, not its per-iteration one

**Evaluation.** `deliberately`, `genuinely`, `precisely`, `the payoff`, `the interesting part` —
each asks the reader to agree with a judgment. State the constraint the design satisfies and let it
stand.

**Argument.** A design doc records a decision; it does not persuade anyone of it. Prose that answers
an objection nobody raised, or that reassures the reader two sections agree with each other, is
arguing. Cut it or turn it into a stated invariant.

One shape reads like argument and stays: the approach that looks right and does not work.
[Code Comments](../../../CLAUDE.md#code-comments) permits it, because a reader who reaches for that
approach needs to know where it fails. `ir.md`, "`Copair` and `DisjointJoin` — two
collection-combining operations, not one" is the model — a `Case` fan-out assembled as a copairing
would carry a `Variant` domain that every consumer then has to undo, which is a fact about the
alternative. The line: naming what breaks is a claim, naming what is better is a judgment. Keep the
first, cut the second.

## Invented vocabulary

A coined term spreads. It is memorable, so the next agent reads the doc and reuses it, and within a
few changes it sits in code comments as though it were established, still with no definition and
nothing to look it up in. Further along it reaches identifiers, and then the coinage is in the code
rather than only in the prose.

`wall` shows the collision that follows. `strict wall` names the strict `typecheck` pass in
`mutability.md` and four files under `src/ccl/`. `consistency wall`, shortened to a bare `the wall`,
names the type-consistency check in `infer/api.rs`, `infer/check.rs`, and `infer/solve.rs`.
`planning/loops.rs` uses `the wall` for the boundary between what a phase emitted and what the
engine consumed. One metaphor, three mechanisms, no definition for any of them.

`gate` shows the later stage. It is a second name for the refinement a partition leg already carries
— the type is `Type::Refinement` — and it has reached `lambda_elim.rs`'s locals as `gate_value` and
`gate_fn`. An identifier is not evidence that a term is legitimate. It is evidence that the coinage
got further.

Before introducing a term, ask whether the codebase already names the concept. Where it does, use
that name; a second name for one concept is the defect, whichever name is better.

Two habits to drop:

- **Metaphor.** `wall`, `bridge`, `pane` stick precisely because they float free of the mechanism
  they stand for. A mechanical description survives a rename; a metaphor drifts, shortens, and
  collides.
- **Naming a step in an argument.** A rule number, or a hyphenated slogan for a rewrite, reads like
  a citation while pointing at nothing checkable.

When a concept recurs and the codebase does not name it, give it a heading in the doc that owns it
so `./ci.sh doc_refs` validates references, then use that one spelling everywhere.

### Finding it already spread

Report existing coined vocabulary before deciding whether to change it. The author decides
whether the correction belongs in the current change or a follow-up, based on its reach and other
work in flight. Worst to best:

1. **Silently keeping the redundant term** — the spread continues, and the change endorses it.
2. **Silently converting it** — the vocabulary improves, and a rename the author did not ask for
   arrives inside an unrelated diff, sometimes touching identifiers.
3. **Flagging it in the session** — say it in the turn where you found it: where the term reaches,
   how many sites, whether identifiers are involved, and what a full pass would touch. Then convert
   what the change already touches and leave the rest.

Report it in the session while the author can still respond. Commit messages and PR descriptions
may be read too late or not at all. Asking after the change has landed leaves the decision already
made.

Converting only part of a passage manufactures the two-names-one-concept problem, so extend to the
enclosing passage — the section, the doc comment, the blockquote — even when the change did not
otherwise touch all of it. Stop at the file boundary, and stop before identifiers.

## Linear sentence structure

Find each clause's subject and predicate. If another clause or a long aside separates them,
move that material before or after the main assertion. Do not fix a nested relative by adding
more relative pronouns: the reader would still have to hold several incomplete clauses open.

For example, the dependency-order restriction in
[The fold is order-free](../../../src/ccl/design/provenance.md#the-fold-is-order-free):

> Before: A dependency whose upstream ID also has a selected row must have a smaller ID than its
> product.

> After: If a dependency's upstream ID also has a selected row, that ID must be smaller than the
> product's ID.

The restriction applies only when the upstream ID has a selected row. Pre-seeded input IDs are
exempt in both versions. Splitting this into "A dependency has an upstream ID. That ID must be
smaller than the product's ID" would remove the condition and change the contract. Preserve
restrictions and exceptions when moving them; do not add an unstated converse.

An omitted object relative pronoun is a separate question. Both `the level they name` and
`the level that they name` can be clear. Add the pronoun if it makes a boundary easier to recognize,
but do not insert `that` mechanically. Likewise, `the node that the pass creates contains ...`
still interrupts `the node ... contains`: restoring the marker alone has not made it linear.

Keep short modifiers such as `a stateless producer`. There is no requirement to turn them into
conditionals. A sentence can also retain a contrast: `The grammar consumes those tokens rather
than computing indentation` need not become two sentences. Repeat a technical noun when a pronoun
would obscure its referent, not merely to avoid all pronouns.

## The transformation

Both pairs are real. The "before" is prose currently in the repo.

**Aside-stacking.** The claim gets interrupted twice, so the reader assembles it from fragments.

> Before (`provenance.md`): It is decided in exactly one place — the `lower_expr` wrapper re-tags
> every lowered expression's root, last tag wins via the fold's re-image path — so no lowering arm
> makes a judgment call.

> After: Exactly one place decides it. The `lower_expr` wrapper re-tags every lowered expression's
> root, and the fold's re-image path makes the last tag win, so no lowering arm makes a judgment
> call.

**Subordinated conclusion.** Well-foundedness and its reason are the load-bearing facts, and both
trail three clauses behind the setup.

> Before (`mutability.md`): The history functions of a program's mutable variables form one
> **mutually recursive definition group** (a `letrec`), whose unique solution is **well-founded**
> because every recursive reference is **causal** — it consults only *strictly earlier* positions of
> the domain, through one of two **causal accessor** builtins.

> After: The history functions of a program's mutable variables form one **mutually recursive
> definition group** (a `letrec`). Its solution is unique and **well-founded**: every recursive
> reference is causal, consulting only strictly earlier positions of the domain through one of two
> **causal accessor** builtins.

Bold stays on the terms being defined; the stress italics go. Nothing was cut — neither pair is a
length exercise.

## Read it back

The rules in
[Prose style: specifications, not blog posts](../../../CLAUDE.md#prose-style-specifications-not-blog-posts)
are the checklist; re-read against them rather than against a restatement here. Check sentence
structure as a separate pass: locate subjects and predicates, remove intervening clauses, and
confirm that the same conditions and exceptions still apply. Then ask:

- **Does this repeat what the document already said?** Repetition across sections is the largest
  source of length here, and the hardest thing to see while writing.
- **Is there a voice in it?** Stress, evaluation, or argument, as above.

## Comments specifically

Comments inherit the rules, plus the constraint in [Code Comments](../../../CLAUDE.md#code-comments):
explain why, not history. Two failure modes are specific to comments:

- **The narrated walkthrough.** A comment that recounts what the following lines do in order
  duplicates the code. Say what invariant the block maintains and why it is not type-enforced.
- **The essay above a small function.** When a doc comment outgrows its item, the content usually
  belongs in the module's design doc, with the comment citing the heading. See
  [Referencing docs and sections](../../../CLAUDE.md#referencing-docs-and-sections) for the citable
  form.

## Editing existing prose

A prose fix asserts something about the code, so read the code before asserting it. Rewriting a
passage that describes a mechanism restates that mechanism's behavior, and the sentence being
replaced is not evidence: it may be describing what the code did two changes ago. This repo has
already shipped a doc claim that a `Σ` reconciles arms at differing domains where the code rejects
them, and the cleanup that fixed the staleness around it carried the wrong claim forward one
revision further. Check the claim against the mechanism, not against the sentence.

Convert older-style prose in the affected passage; do not imitate it. Fix documentation defects
found during the work in the same change. Otherwise later agents can copy the old sentence
structures from that passage. Rewriting an unrelated document remains a separate change.

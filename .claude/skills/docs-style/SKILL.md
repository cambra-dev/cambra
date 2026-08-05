---
name: docs-style
description: Author, update, or review technical documentation — design docs, specs, how-tos, READMEs — and review rustdoc or comment prose. Use when writing or editing any *.md in this repo, when asked to document a change or review docs, and when rendering a CCL AST or a type in symbolic notation.
---

# Documentation

Code-comment rules live in `CLAUDE.md`, "Code Comments" — this skill does not restate them. Use it for doc prose, document structure, and notation.

## Scope gate

Amending an existing doc: skip to the checklist. New doc or substantial new section: run the whole workflow.

## Phase 1 — Intent

Name the audience (a contributor to this subsystem, an external CCL author, a future maintainer) and the mode. A section belongs to exactly one mode:

- **Explanation** — design docs. Why the abstraction exists, the law it obeys, the trade-offs taken. Most of `docs/` and all `*/design*.md`.
- **How-To** — goal-oriented recipes: "get a CCL program running against a live source", "add an operator". Baseline domain knowledge assumed, the goal in the heading, the first command early. A how-to that has to explain the model first means the explanation belongs in a design doc it links to.
- **Reference** — specifications and enumerations (`docs/chl-spec.md`, operator tables, CLI flags). Tables and lists, no narrative.
- **Tutorial** — learning-oriented, executed start to finish. Rare here; don't invent one where a how-to is what's wanted.

A design doc legitimately interleaves Explanation and Reference — the law, then the table of what implements it. Separate headings, not separate documents.

Placement follows the mode: subsystem design beside its source (`src/ccl/design/ir.md`), cross-cutting docs and **all how-tos** in `docs/` — a how-to crosses subsystems by nature, and a reader asking "how do I…" won't look in `src/interpreter/`. Status, plans, and issue tracking go in `vault/`, not in the repo; a repo doc that narrates in-flight work is stale the moment the work lands.

## Phase 2 — Ground the draft

Read the source, the tests, and the adjacent design doc before writing. Extract the things a reader cannot infer from the code in front of them:

- the invariant or law, and where it is enforced
- the pass that owns it, and what erases or establishes it
- the test that pins it
- the failure mode when it is violated
- the alternative that was evaluated and rejected, and why

Cite a number only when a benchmark produced it, and say which one. "Reduces allocations in the coalesce pass" without a measurement is a claim, not a fact.

## Phase 3 — Structure

Progressive disclosure: problem and motivation, then the model, then how the passes realize it, then trade-offs and rejected alternatives. A reader who stops after the first section should have a correct if incomplete picture.

Headings are the citation API. Every section anyone might cite needs a real heading, spelled exactly as it will be cited; a bold paragraph lead-in is not citable. Renaming a heading is a breaking change — `./ci.sh doc_refs` finds every inbound link and citation, from code and from docs, and they get fixed in the same change. Citation forms and the never-cite list: `CLAUDE.md`, "Referencing docs and sections".

Document the current design, not the route to it: no "previously", no changelog sections, no PR or date references. Describing an approach that looks reasonable but doesn't work is worth keeping when it prevents a wrong turn.

Tables for comparative matrices, multi-variable configs, and API specs; bullets for sequential steps and prerequisites.

Notation is documented, not improvised. For metavariables and the function-type/term forms in prose, follow [docs/design.md](../../../docs/design.md), "Notation conventions". For rendering a CCL AST or a `Type`, follow [src/ccl/design/ir.md](../../../src/ccl/design/ir.md), "Symbolic rendering" — read it before writing either, since both are pinned by tests and a form invented from memory will be wrong.

## Checklist

- [ ] Active voice, direct imperatives — "Run the script", not "The script should be executed".
- [ ] No filler adjectives — robust, fast, seamless, significantly.
- [ ] Mechanism named rather than graded; every number traced to a benchmark.
- [ ] Opens on content — no greeting, no "this document describes".
- [ ] No "Summary" or "Conclusion" header.
- [ ] Fenced code blocks hold literal source, in plain characters; symbolic and metavariable notation appears only in prose and inline code.
- [ ] Every cited heading exists and is spelled exactly; `./ci.sh doc_refs` clean.
- [ ] Placement correct: subsystem design beside source, how-to in `docs/`, status in `vault/`.

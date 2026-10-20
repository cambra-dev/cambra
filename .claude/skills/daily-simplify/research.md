# Evidence behind the pipeline

These notes come from a deep-research pass run on 2026-10-08: 21 sources fetched, 25 claims put
through 3-vote adversarial verification, 2 claims refuted. Almost all of the evidence is Java or
Python, uses 2023–2025 models, and works on small classes. The percentages below describe those
setups. Do not read them as predictions for cambra. The direction of each finding is what the
skill relies on.

| Finding | Evidence | Where the skill uses it |
|---|---|---|
| Targeted discovery beats open-ended discovery | Open-ended discovery found 15.6% of real refactorings. Hinting the subcategory and narrowing the search raised it to 86.7%, though the hints came from ground truth, so that figure is an upper bound ([Liu et al.](https://arxiv.org/abs/2411.04444)) | One finder per category, each over focus files |
| Seed from static and history signals. Hotspot = complexity × churn | RefAgent's planner is seeded by a dependency graph and metrics, with smell labels withheld ([RefAgent](https://arxiv.org/pdf/2511.03153)). Hotspots: [CodeScene](https://docs.enterprise.codescene.io/versions/4.1.4/guides/technical/hotspots.html) | `seed.sh` |
| Raw suggestions are mostly noise until filtered | Up to 62% of Extract Method suggestions were hallucinated ([EM-Assist](https://arxiv.org/html/2401.15298v1)), and up to 80% of Move Method suggestions ([MMpro](https://conf.researchr.org/details/icsme-2025/icsme-2025-papers/29/Together-We-Are-Better-LLM-IDE-and-Semantic-Embedding-to-Assist-Move-Method-Refacto)). Usefulness rules drop one-line extractions and extractions covering most of a method | Triage: re-read cited code, usefulness filter |
| Applied refactors silently change behaviour, and passing tests are not proof | 6.6–7.4% of applied refactors were unsafe ([Liu et al.](https://arxiv.org/abs/2411.04444)). About 1 in 6 GPT-4o refactors broke tests, including a three-way guard collapsed to two ways ([Midolo et al.](https://arxiv.org/pdf/2601.13139v1)). Root causes: misread context 24%, inconsistent renaming 15%, added functionality 14%, unhandled edge cases 9% ([RefactorAssist](https://arxiv.org/pdf/2608.00924)) | Reviewer checklist; implementer's break-it-to-confirm-the-test step |
| Bounded compile/test loops with an explicit abandon rule | RefAgent caps its compile and test loops at 20 iterations and excludes classes that still fail. Gains plateau at about 12 iterations | Implementer's five-round cap |
| Compound refactors fail about twice as often as atomic ones | 39.4% success on compound instances vs 82.6% on atomic ones, n=33 compound ([SWE-Refactor](https://papers.cool/arxiv/2602.03712)) | Atomicity in triage; dispatch-time budget; `scope-creep` abandonment |
| Verification has three parts: compiles, tests pass, the intended change actually happened | SWE-Refactor confirms each refactoring by AST with RefactoringMiner. Rust has no equivalent tool | A cold reviewer substitutes for the AST check |
| LLMs over-abstract | Generic helpers taking lambdas. Low confidence: a single preprint, and the readability delta was not significant ([Midolo et al.](https://arxiv.org/pdf/2601.13139v1)) | "Fewer lines, more indirection" is rejected |

Refuted during verification, so not relied on:

- the claim that hybrid static+LLM detection beats an LLM alone on non-contiguous clones (0–3);
- specific skew statistics for Clippy warnings on crates.io (1–2).

The evidence says nothing about:

- consistency with design docs;
- PR granularity;
- run logs;
- workspace isolation;
- tightening comments.

Those parts of the skill rest on cambra's own conventions (`cambra/CLAUDE.md`) and on judgement.

Open questions worth revisiting as the run accumulates history:

- Is a cold LLM reviewer an adequate substitute for AST-level confirmation in Rust?
- Which diff-size thresholds best predict that an attempt has turned compound?
- How often do triage and the reviewer disagree?

The logs answer the last one.

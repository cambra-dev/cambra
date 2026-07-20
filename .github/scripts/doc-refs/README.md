# Doc-reference checker

`check_doc_refs.py` fails CI when a cross-reference into the docs no longer
resolves, so links and citations can't silently rot as sections move or get
renamed. It runs as part of `./ci.sh` (the `doc_refs` step) and on every PR —
including docs-only ones, which the main CI job otherwise skips.

Stdlib Python only; no external dependencies.

```bash
./ci.sh doc_refs                                   # what CI runs
python3 .github/scripts/doc-refs/check_doc_refs.py # just the check
python3 -m unittest                                # the checker's own tests
```

## What it checks

**A. Markdown link → target (doc → doc).** Every intra-repo link
`[text](path#anchor)` in a `*.md` file must point at a file (or directory) that
exists. When the target is another Markdown file and the link carries a
`#fragment`, that anchor must exist among the target's headings, computed with
GitHub's heading-slug rules (lowercase, drop punctuation, each whitespace run
becomes hyphens without collapsing, duplicate headings get `-1`/`-2`/… in
document order). Same-file `#anchor` links and explicit `<a id="…">` anchors are
honored. Links that escape the repo root (`../../security/advisories/new`) are
treated as GitHub-relative web links and skipped. Links inside fenced or inline
code are not checked.

**B. Rust comment → doc (code → doc).** Every `<name>.md` mentioned in a Rust
*comment* (string literals are excluded) must resolve to a doc that exists,
matched by unique path-suffix so `mutability.md`, `design/mutability.md`, and the
full path all resolve to the same file (an ambiguous suffix is an error — write a
longer path). Any **section title quoted immediately after** the reference must
exist as a heading in that doc.

## The code → doc citation convention

To cite a section from code in a way the checker can verify, put the doc path and
then the section's **exact heading text** in double quotes, directly adjacent:

```rust
// See `src/ccl/design/mutability.md`, "The model" / "`LetRec`".
```

Multiple titles may be joined by ` / `, `, `, `and`, or wrapped in `(…)`. The run
of titles must come *immediately* after the doc reference — the first ordinary
word (or a `:`-introduced clause) ends it, so an incidental body-text quote later
in the sentence is not mistaken for a heading:

```rust
// mutability.md, rule 1: "a Mut-typed value must be bare"  <- quote NOT checked
```

Prefer this quoted-title form over a `#anchor` fragment in code: a title survives
section reordering and reads naturally in prose, whereas an anchor slug does not.
See the "Referencing docs and sections" section of the top-level `CLAUDE.md` for
the reference forms to prefer and the uncheckable ones to avoid.

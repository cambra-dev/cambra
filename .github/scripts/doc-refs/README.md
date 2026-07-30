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
code are not checked. A link whose *text* wraps across the hard-wrapped prose is
still found (see "Wrapped references" below).

**B. Prose → doc section (the quoted-title citation).** Every `<name>.md`
mentioned in a Rust *comment* (string literals are excluded) must resolve to a
doc that exists, matched by unique path-suffix so `ir.md`, `design/ir.md`, and
the full path all resolve to the same file (an ambiguous suffix is an error —
write a longer path). Any **section title quoted immediately after** the
reference must exist as a heading in that doc.

The same citation is checked in **doc prose**, where it is often written hanging
off a link:

```markdown
see [mutability.md](mutability.md), "The model: histories and causal recursion"
```

The title is taken from after the closing paren, and the link's own path and
anchor stay check A's business. A doc naming another doc *without* quoting a
section is left alone: in
prose that is just prose, as legitimately loose as the paths check C tolerates.
Quoting a title is what makes it a citation — and that is exactly when the path
must be unambiguous, since otherwise there is nothing to check the title
against. **In a doc, prefer a link over a quoted title**: it survives the same
renames and check A validates the anchor as well.

**C. Doc prose → source (doc → source).** Every backtick (inline-code) mention
of a source file in doc prose — `ast.rs`, `src/ccl/lower/loops.rs`, `Cargo.toml`
(optionally with a `:line` suffix) — must resolve to a file that exists, by
path-suffix match. A bare name that matches several files (`mod.rs`, `main.rs`)
counts as resolved — only a mention that matches *nothing* is flagged, since the
point is to catch deleted/renamed files, not to demand precise paths in prose.
Mentions inside fenced code (or matching nothing path-like) are not checked.

## Opting a line out

A line carrying a `doc-refs-ignore` marker (in Markdown, an HTML comment —
`<!-- doc-refs-ignore -->`) is skipped by **all three** checks. It is for the
cases a pure existence check can't distinguish from rot: a deliberate mention of
a deleted or renamed file (migration notes), an illustrative example path, and
prose that demonstrates the reference syntax itself. Fencing the example works
too, and reads better when it is more than a phrase — a fenced block is skipped
by every check without a marker.

## The quoted-title citation convention

To cite a section in a way the checker can verify — from code, where there is no
link syntax to use, or in doc prose alongside a link — put the doc path and then
the section's **exact heading text** in double quotes, directly adjacent:

```rust
// See `src/ccl/design/ir.md`, "Application shape" / "`Cast` — explicit refinement acquisition".
```

Multiple titles may be joined by ` / `, `, `, `and`, or wrapped in `(…)`. The run
of titles must come *immediately* after the doc reference — the first ordinary
word (or a `:`-introduced clause) ends it, so an incidental body-text quote later
in the sentence is not mistaken for a heading:

```rust
// ir.md, rule 1: "a Mut-typed value must be bare"  <- quote NOT checked
```

An opening quote where a title belongs, with no closing quote to pair with it,
is reported as an *unterminated quoted citation* rather than passed over: an
unparseable citation must not be silently indistinguishable from having written
no citation at all.

Only *headings* are citable. The design docs also open paragraphs with a bold
lead-in, and those read like landmarks but carry no anchor and cannot be checked
— if code needs to cite one, promote it to a heading in the same change rather
than quoting the bold text.

**Exact**, too: `"The model"` does not cite the heading *The model: histories and
causal recursion*. An abbreviated title reads fine to a person and is invisible
to the checker, which is how it survives the rename that invalidates it.

Prefer this quoted-title form over a `#anchor` fragment in code: a title survives
section reordering and reads naturally in prose, whereas an anchor slug does not.
See the "Referencing docs and sections" section of the top-level `CLAUDE.md` for
the reference forms to prefer and the uncheckable ones to avoid.

## Wrapped references

Prose here is hard-wrapped, in docs and in Rust comments alike, so a reference
near the right margin continues on the next line. Both the link scanner and the
citation scanner read whole prose rather than one line at a time, so a wrapped
reference is checked like any other:

```rust
// See `src/ccl/design/mutability.md`, "mut_elim: eliminating overwrite
// mutability".
```

Consecutive line comments are one comment (a comment trailing *code* starts a new
one), and a cited title's line break — plus the next line's comment marker and
indentation — collapses back to the single space it stands for before the title
is slugged.

The scanners bound how far a run may wrap: a link text or a quoted title over at
most two further lines, and never across a blank line, which ends the thought a
reference belongs to. Past that, an unpaired `[` or `"` would pair with an
unrelated one and invent a reference out of ordinary prose. A citation that needs
more than three lines is too long to be a heading — fix the citation, not the
budget.

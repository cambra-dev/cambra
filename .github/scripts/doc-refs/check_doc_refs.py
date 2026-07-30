#!/usr/bin/env python3
"""Validate cross-references into the docs so they can't silently rot.

Three checks, run together (see `.github/scripts/doc-refs/README.md`):

  A. doc -> doc: every intra-repo Markdown link `[text](path#anchor)` resolves
     to a file that exists, and when it carries a `#fragment` into a Markdown
     file, that anchor exists among the target's headings (GitHub slug rules).

  B. prose -> doc section: every `<name>.md` mentioned in a Rust *comment* or in
     doc prose resolves to a doc that exists, and any section title quoted
     immediately after it (the checkable citation convention) exists as a
     heading in that doc.

  C. doc -> source: every backtick source-path mention in doc prose (e.g.
     `ast.rs`, `src/ccl/lower/loops.rs`) resolves to a file that exists. A line
     may opt out with a `doc-refs-ignore` marker (deleted/renamed files,
     illustrative examples).

A and B share one primitive: the set of valid anchors for a Markdown file,
computed with GitHub's heading-slug algorithm — an anchor link and a quoted
heading are the same reference in two notations. No dependencies — stdlib only.

Exit status is non-zero if any reference is broken, so `ci.sh` can gate on it.
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import NamedTuple

# Repo root: this file lives at <root>/.github/scripts/doc-refs/check_doc_refs.py
REPO_ROOT = Path(__file__).resolve().parents[3]

# Directories that are not source-of-truth for references.
SKIP_DIRS = {".git", "target", ".claude", "node_modules"}

# Link targets that are external / non-file and never checked.
EXTERNAL_SCHEME = re.compile(r"^(https?:|mailto:|tel:|ftp:|#!)", re.IGNORECASE)


# --------------------------------------------------------------------------- #
# GitHub heading-slug algorithm                                               #
# --------------------------------------------------------------------------- #
#
# GitHub renders a heading, lowercases it, drops every character that is not a
# word char / whitespace / hyphen, then turns each remaining whitespace char
# into a hyphen (WITHOUT collapsing runs — `A — B` -> `a--b`), and finally
# disambiguates repeats within a file by appending `-1`, `-2`, ... in document
# order. `_slug_base` is the per-heading transform; `heading_anchors` applies
# the document-order de-duplication.

_SLUG_STRIP = re.compile(r"[^\w\s-]", re.UNICODE)
_SLUG_WS = re.compile(r"\s", re.UNICODE)


def _slug_base(text: str) -> str:
    s = _SLUG_STRIP.sub("", text.strip().lower())
    return _SLUG_WS.sub("-", s)


def heading_anchors(md_text: str) -> set[str]:
    """All anchors a GitHub-rendered Markdown file exposes.

    Covers ATX headings (`## Foo`, including closed `## Foo ##`) with the
    document-order de-duplication GitHub applies, plus explicit HTML anchors
    (`<a id="x">` / `<a name="x">`) so hand-authored stable IDs also validate.
    Setext headings are intentionally unsupported — the docs use none, and a
    lone `---`/`===` line here is always a horizontal rule.
    """
    anchors: set[str] = set()
    seen: Counter[str] = Counter()
    for line in _outside_code_fences(md_text):
        m = re.match(r"\s{0,3}(#{1,6})\s+(.*?)\s*$", line)
        if m:
            title = re.sub(r"\s+#+\s*$", "", m.group(2))  # strip closing ###
            base = _slug_base(title)
            n = seen[base]
            seen[base] += 1
            anchors.add(base if n == 0 else f"{base}-{n}")
        for am in re.finditer(r'<a\s+(?:id|name)\s*=\s*"([^"]+)"', line):
            anchors.add(am.group(1))
    return anchors


def _outside_code_fences(md_text: str):
    """Yield the lines of `md_text` that are not inside a ``` / ~~~ fence."""
    fence: str | None = None
    for line in md_text.splitlines():
        m = re.match(r"\s{0,3}(`{3,}|~{3,})", line)
        if m:
            tok = m.group(1)[0]
            if fence is None:
                fence = tok
            elif fence == tok:
                fence = None
            continue
        if fence is None:
            yield line


# --------------------------------------------------------------------------- #
# Repo file index                                                             #
# --------------------------------------------------------------------------- #


class Repo:
    """File index + anchor cache for the tree under `root`.

    The root is a parameter, not the module global, so the checks can run over
    a fixture tree: every check takes a `Repo` and reads through it, which is
    what makes them testable at all.
    """

    def __init__(self, root: Path = REPO_ROOT) -> None:
        self.root = root
        self.files: list[Path] = []
        # Prune the skipped directories rather than walking them and filtering
        # after — `target/` alone dwarfs the rest of the tree.
        stack = [root]
        while stack:
            for p in sorted(stack.pop().iterdir()):
                if p.is_dir():
                    if p.name not in SKIP_DIRS and not p.is_symlink():
                        stack.append(p)
                    continue
                self.files.append(p.relative_to(root))
        self._file_set = set(self.files)
        # For suffix resolution of loosely-written path references (a bare
        # filename, a partial path, or a full repo path): map every path-suffix
        # of every file to the file(s) it could mean.
        self._by_suffix: dict[str, list[Path]] = {}
        for f in self.files:
            parts = f.parts
            for i in range(len(parts)):
                suffix = "/".join(parts[i:])
                self._by_suffix.setdefault(suffix, []).append(f)
        self._anchor_cache: dict[Path, set[str]] = {}

    def exists(self, rel: Path) -> bool:
        # Normalize `.`/`..` without touching the filesystem, then confirm the
        # path is inside the repo and indexed (files) or a real directory.
        try:
            norm = Path(*rel.parts)
            resolved = (self.root / rel).resolve()
            resolved.relative_to(self.root.resolve())
        except ValueError:
            return False
        if resolved.is_dir():
            return True
        return norm in self._file_set or resolved.is_file()

    def read(self, rel: Path) -> str:
        return (self.root / rel).read_text(encoding="utf-8", errors="replace")

    def anchors(self, rel: Path) -> set[str]:
        if rel not in self._anchor_cache:
            self._anchor_cache[rel] = heading_anchors(self.read(rel))
        return self._anchor_cache[rel]

    def resolve_suffix(self, written: str) -> tuple[Path | None, list[Path]]:
        """Resolve a loosely-written path (e.g. `design/mutability.md`, a bare
        `ast.rs`, or a full repo path) by unique path-suffix match. Returns
        (resolved, candidates); resolved is None when zero or >1 candidates."""
        # `lstrip("./")` would eat the leading dot of a dotfile path such as
        # `.github/scripts/...`; only a `./` prefix is noise.
        cands = self._by_suffix.get(re.sub(r"^(?:\./)+", "", written), [])
        return (cands[0] if len(cands) == 1 else None, cands)


# --------------------------------------------------------------------------- #
# Wrapping matches                                                            #
# --------------------------------------------------------------------------- #
#
# Prose here is hard-wrapped, in docs and in Rust comments alike, so a reference
# near the right margin routinely continues on the next line: a Markdown link
# whose text wraps, a quoted section title split across two `///` lines. A
# scanner that reads one line at a time simply does not see those references —
# and an unchecked reference is worse than a broken one, because nothing says so.
#
# The counter-pressure is that a delimiter allowed to roam too far pairs up with
# an unrelated one and invents a match out of ordinary prose. So a wrapping run
# is bounded twice: by a line budget, and by never crossing a blank line, which
# ends the thought a reference belongs to.


def _wrapping(chars: str, breaks: int = 2) -> str:
    """A run of `chars` (a newline-free character class) that may continue onto
    up to `breaks` further lines, each of which must carry content."""
    cont = rf"\n[ \t]*(?![\n \t]){chars}*"
    return rf"{chars}*(?:{cont}){{0,{breaks}}}"


def _line_at(text: str, offset: int, first_line: int = 1) -> int:
    """The source line an offset falls on, for text whose newlines are intact."""
    return first_line + text.count("\n", 0, offset)


# --------------------------------------------------------------------------- #
# Problem reporting                                                           #
# --------------------------------------------------------------------------- #


@dataclass
class Problem:
    source: str  # repo-relative "path:line"
    detail: str


# --------------------------------------------------------------------------- #
# Check A — Markdown link targets and anchors                                 #
# --------------------------------------------------------------------------- #

# Inline `[text](target)`, whose text may wrap. Targets with spaces/`)` are rare
# here; take up to the first whitespace or `)` and drop an optional `"title"`
# suffix. (The `](` seam never wraps — Markdown does not read `[text]\n(url)` as
# a link — so only the text needs the wrapping treatment.)
_MD_LINK = re.compile(r"\[" + _wrapping(r"[^\]\n]") + r"\]\(\s*(<[^>]+>|[^)\s]+)")
_INLINE_CODE = re.compile(r"`[^`\n]*`")


def check_markdown_links(repo: Repo, problems: list[Problem]) -> int:
    checked = 0
    for rel in repo.files:
        if rel.suffix != ".md":
            continue
        text = repo.read(rel)
        prose = _prose_lines(text)
        for m in _MD_LINK.finditer(prose):
            target = m.group(1).strip("<>")
            if EXTERNAL_SCHEME.match(target):
                continue
            if IGNORE_MARKER in _line_of(prose, m.start()):
                continue
            checked += 1
            _check_one_link(repo, rel, _line_at(prose, m.start()), target, problems)
    return checked


def _prose_lines(md_text: str) -> str:
    """`md_text` with everything that is not prose blanked out: fenced-code
    lines and inline code spans (an example link must not be checked). Line
    breaks survive, so offsets still map back to source lines."""
    fenced = set(_fenced_line_numbers(md_text))
    return "\n".join(
        "" if lineno in fenced else _INLINE_CODE.sub("", line)
        for lineno, line in enumerate(md_text.splitlines(), start=1)
    )


def _check_one_link(
    repo: Repo, rel: Path, lineno: int, target: str, problems: list[Problem]
) -> None:
    src = f"{rel}:{lineno}"
    path_part, _, frag = target.partition("#")
    if path_part == "":
        # Same-file anchor.
        if frag and frag not in repo.anchors(rel):
            problems.append(Problem(src, f"anchor #{frag} not found in {rel.name}"))
        return
    if path_part.startswith("/"):
        tgt = Path(path_part.lstrip("/"))
    else:
        tgt = (rel.parent / path_part)
    try:
        # A target that escapes the repo root is a GitHub-relative *web* link
        # (e.g. `../../security/advisories/new`), not a file — leave it alone.
        (repo.root / tgt).resolve().relative_to(repo.root.resolve())
    except ValueError:
        return
    if not repo.exists(tgt):
        problems.append(Problem(src, f"link target does not exist: {target}"))
        return
    if frag and tgt.suffix == ".md":
        # Fragment normalized like the repo path: resolve `..`/`.`.
        norm = Path(*(repo.root / tgt).resolve().relative_to(repo.root.resolve()).parts)
        if frag not in repo.anchors(norm):
            problems.append(
                Problem(src, f"anchor #{frag} not found in {tgt.name} ({target})")
            )


def _fenced_line_numbers(md_text: str):
    fence: str | None = None
    for lineno, line in enumerate(md_text.splitlines(), start=1):
        m = re.match(r"\s{0,3}(`{3,}|~{3,})", line)
        if m:
            tok = m.group(1)[0]
            yield lineno  # the fence line itself is not prose
            if fence is None:
                fence = tok
            elif fence == tok:
                fence = None
            continue
        if fence is not None:
            yield lineno


# --------------------------------------------------------------------------- #
# Check C — source-path mentions in doc prose                                 #
# --------------------------------------------------------------------------- #

# Backtick (inline-code) mentions of a source file in doc prose — `ast.rs`,
# `src/ccl/lower/loops.rs`, `Cargo.toml`, optionally with a `:line` suffix.
# These are the path references the link check never sees (it only parses
# `[text](target)` link syntax), yet docs cite paths in backticks constantly.
_SRC_EXT = ("rs", "md", "sh", "toml", "py", "svg")
_INLINE_SPAN = re.compile(r"`([^`\n]+)`")
_SRC_PATH = re.compile(
    r"^([A-Za-z0-9_][\w./-]*\.(?:" + "|".join(_SRC_EXT) + r"))(?::\d+(?:-\d+)?)?$"
)
# A line carrying this marker opts out of *every* check on that line — links,
# citations, source paths alike. For the legitimate cases a pure existence check
# can't tell from rot: prose that illustrates the reference syntax itself, and
# deliberate mentions of a deleted/renamed file (migration notes, changelogs —
# "`foo.rs` was deleted").
IGNORE_MARKER = "doc-refs-ignore"


def check_doc_source_paths(repo: Repo, problems: list[Problem]) -> int:
    checked = 0
    for rel in repo.files:
        if rel.suffix != ".md":
            continue
        text = repo.read(rel)
        fenced = set(_fenced_line_numbers(text))
        for lineno, line in enumerate(text.splitlines(), start=1):
            if lineno in fenced or IGNORE_MARKER in line:
                continue
            for m in _INLINE_SPAN.finditer(line):
                pm = _SRC_PATH.match(m.group(1).strip())
                if not pm:
                    continue
                tok = pm.group(1)
                checked += 1
                _, cands = repo.resolve_suffix(tok)
                # A unique OR ambiguous match both mean the file exists; only a
                # zero-candidate mention is rot. Unlike a code citation (check
                # B), a bare name in prose (`mod.rs`, `main.rs`) is legitimately
                # ambiguous and must not be flagged.
                if cands:
                    continue
                problems.append(
                    Problem(
                        f"{rel}:{lineno}",
                        f"source-path mention does not resolve: `{tok}` "
                        f"(if the file was removed or renamed on purpose, "
                        f"add a `{IGNORE_MARKER}` marker on this line)",
                    )
                )
    return checked


# --------------------------------------------------------------------------- #
# Check B — quoted-title citations, from Rust comments and from doc prose      #
# --------------------------------------------------------------------------- #

# A `<name>.md` path token as written in prose (backticks, quotes, and other
# wrappers are handled by the extraction step around it).
_MD_REF = re.compile(r"(?<![\w./-])([\w./-]+\.md)")

# A ref sitting inside a `[text](destination)`. The link's own path and anchor
# are check A's; re-reporting them here would double up on one link.
_LINK_DEST = re.compile(r"\]\(\s*<?[^)\s]*$")


def _citation_tail(text: str, ref: re.Match) -> tuple[int, bool] | None:
    """Where a citation after the doc ref `ref` would begin, and whether the ref
    is a link destination.

    A citation commonly hangs off a link rather than a bare path —
    `[x](doc.md), "Title"` is the usual shape in doc prose — so there the title
    follows the closing paren, not the path. `None` if the link never closes.
    """
    if _LINK_DEST.search(text, 0, ref.start()) is None:
        return ref.end(), False
    close = text.find(")", ref.end())
    return None if close == -1 else (close + 1, True)

# The checkable-citation tail: after a doc ref, a run of one-or-more quoted
# section titles joined only by "glue" (separators/wrappers/§N/`and`). Any other
# word (`rule`, a `:`- introduced clause, a sentence) ends the run, so incidental
# body-text quotes further along the sentence are NOT treated as titles.
#
# Both the glue and the title itself may wrap onto the next comment line (see
# "Wrapping matches" above): the glue by one break — the title starts on this
# line or the next — and the title by the general budget.
_GLUE = r"(?:[ \t,/()`§\d.]|and\b|—)*"
_WRAP = r"(?:\n" + _GLUE + r")?"  # at most one line break inside the glue
_QUOTED_TITLE = '"(' + _wrapping(r'[^"\n]') + ')"'
_CITATION_STEP = re.compile(_GLUE + _WRAP + _QUOTED_TITLE)
# The same window with only an *opening* quote: a citation that never closes,
# which is exactly what an over-long wrap or a typo looks like.
_DANGLING_QUOTE = re.compile(_GLUE + _WRAP + '"')


def check_doc_citations(repo: Repo, problems: list[Problem]) -> int:
    """Check B over both places the quoted-title convention is written: Rust
    comments, and doc prose (a doc citing a *section* of another doc names it
    the same way). A link is the better form in a doc and check A validates it
    end to end — but the quoted form is what rots unnoticed, so it is the one
    that needs checking."""
    checked = 0
    for rel in repo.files:
        if rel.suffix not in (".rs", ".md"):
            continue
        text = repo.read(rel)
        units = _rust_comments(text) if rel.suffix == ".rs" else [_doc_prose(text)]
        for unit in units:
            for m in _MD_REF.finditer(unit.text):
                written = m.group(1)
                if IGNORE_MARKER in _line_of(unit.text, m.start()):
                    continue
                tail = _citation_tail(unit.text, m)
                if tail is None:
                    continue
                tail_at, in_link = tail
                cites = _cited_titles(unit.text[tail_at:])
                # In a *comment* the `.md` mention is itself the citation —
                # there is no link syntax to use — so it must resolve. In a doc,
                # the citation form is a link (check A), and a bare doc name in
                # prose is just prose, as legitimately loose as the source paths
                # check C stays lenient about. What makes it a citation is a
                # quoted title, and that is exactly when the path has to be
                # pinned down: an ambiguous one leaves nothing to check against.
                if rel.suffix == ".md" and not cites.titles and not cites.dangling:
                    continue
                checked += 1
                resolved, cands = repo.resolve_suffix(written)
                src = f"{rel}:{unit.line_at(m.start())}"
                if resolved is None:
                    if in_link:
                        continue  # check A already reports a bad link target
                    if not cands:
                        problems.append(
                            Problem(src, f"doc ref does not resolve: {written}")
                        )
                    else:
                        opts = ", ".join(str(c) for c in cands)
                        problems.append(
                            Problem(
                                src,
                                f"doc ref {written} is ambiguous "
                                f"(matches {opts}); write a longer path",
                            )
                        )
                    continue
                for title in cites.titles:
                    slug = _slug_base(_normalize_title(title))
                    if slug not in repo.anchors(resolved):
                        problems.append(
                            Problem(
                                src,
                                f'cited section "{_one_line(title)}" not found as a '
                                f"heading in {resolved} (see the citation "
                                f"convention in the doc-refs README)",
                            )
                        )
                if cites.dangling:
                    problems.append(
                        Problem(
                            src,
                            f"unterminated quoted citation after {written}: the "
                            f"opening quote has no closing quote within the next "
                            f"few lines, so no section title could be checked "
                            f"(see the citation convention in the doc-refs "
                            f"README)",
                        )
                    )
    return checked


class Citations(NamedTuple):
    """What follows a doc ref: the quoted titles, and whether a citation was
    left hanging.

    `dangling` is an opening quote sitting exactly where a title would be, with
    nothing closing it inside the citation window — an unclosed or over-wrapped
    citation. It is reported rather than skipped precisely because the
    alternative — treating an unparseable citation as "no citation" — is how a
    title goes unchecked without anyone noticing.
    """

    titles: list[str]
    dangling: bool


def _cited_titles(tail: str) -> Citations:
    """The adjacent quoted-citation run at the start of `tail`."""
    titles: list[str] = []
    pos = 0
    while True:
        m = _CITATION_STEP.match(tail, pos)
        if not m:
            return Citations(titles, _DANGLING_QUOTE.match(tail, pos) is not None)
        titles.append(m.group(1))
        pos = m.end()


def _one_line(text: str) -> str:
    """`text` with every whitespace run — a wrap's line break and the next
    line's indentation included — collapsed to the single space it stands for."""
    return " ".join(text.split())


def _normalize_title(title: str) -> str:
    """A cited title as it would read in a heading: on one line (headings never
    contain a newline, and `_slug_base` maps each whitespace character to its
    own hyphen), with Markdown code ticks dropped as the slug drops them."""
    return _one_line(title.replace("`", ""))


@dataclass
class Prose:
    """A run of prose to scan for citations, with its line breaks intact.

    The unit a *sentence* is written in — a Rust comment run, or a whole doc —
    because a citation near the right margin wraps, and a scanner that reads
    one line at a time would not see it. Markup that is not prose is stripped
    in place (comment markers, code fences) rather than deleted, so `line_at`
    stays an exact offset→line map for reporting.
    """

    first_line: int
    text: str

    def line_at(self, offset: int) -> int:
        return _line_at(self.text, offset, self.first_line)


def _doc_prose(md_text: str) -> Prose:
    """A Markdown file as one prose run: fenced code blanked out, inline code
    *kept* — a cited heading routinely contains backticks (`` "`Mut` is a CCL
    type" ``), and dropping the spans would mangle the title."""
    fenced = set(_fenced_line_numbers(md_text))
    return Prose(
        1,
        "\n".join(
            "" if lineno in fenced else line
            for lineno, line in enumerate(md_text.splitlines(), start=1)
        ),
    )


def _line_of(text: str, offset: int) -> str:
    """The whole line `offset` falls on — for the opt-out marker, which applies
    to the line that carries it."""
    return text[text.rfind("\n", 0, offset) + 1 :].partition("\n")[0]


# A line whose content begins with a line comment, i.e. one that continues a
# run. A comment trailing *code* does not continue a run: the code between them
# means they are two separate thoughts on two separate lines.
_LINE_COMMENT_START = re.compile(r"[ \t]*//")
# `///`, `//!`, `//` — the marker itself carries no prose.
_LINE_MARKER = re.compile(r"^[ \t]*//[/!]?")
# Block-comment decoration: the leading `*` of a continuation line.
_BLOCK_DECORATION = re.compile(r"(?m)^[ \t]*\*")


def _rust_comments(text: str):
    """Yield every comment in `text` as a `Prose` run, in source order — a block
    comment, or a run of consecutive line comments, markers stripped.

    A small scanner that tracks strings (incl. raw `r#".."#`), char/lifetime
    tokens, line comments, and *nesting* block comments, so a `.md` inside a
    string literal is never mistaken for a doc reference.
    """
    i, n = 0, len(text)
    line = 1
    while i < n:
        c = text[i]
        prev = i
        if c == "\n":
            line += 1
            i += 1
        elif c == "/" and i + 1 < n and text[i + 1] == "/":
            start_line = line
            parts = []
            while True:
                j = text.find("\n", i)
                j = n if j == -1 else j
                parts.append(_LINE_MARKER.sub("", text[i:j]))
                nxt = _LINE_COMMENT_START.match(text, j + 1) if j < n else None
                if nxt is None:
                    break
                i = nxt.end() - 2  # the `//` opening the next line's comment
                line += 1
            yield Prose(start_line, "\n".join(parts))
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            start_line = line
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i] == "/" and i + 1 < n and text[i + 1] == "*":
                    depth += 1
                    i += 2
                elif text[i] == "*" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            yield Prose(start_line, _BLOCK_DECORATION.sub("", text[prev:i]))
            line += text.count("\n", prev, i)
        elif c == '"':
            i = _skip_string(text, i)
            line += text.count("\n", prev, i)
        elif c == "r" and _raw_string_prefix(text, i) is not None:
            i = _skip_raw_string(text, i)
            line += text.count("\n", prev, i)
        elif c == "'":
            i = _skip_char_or_lifetime(text, i)
        else:
            i += 1


def _skip_string(text: str, i: int) -> int:
    i += 1
    n = len(text)
    while i < n:
        if text[i] == "\\":
            i += 2
        elif text[i] == '"':
            return i + 1
        else:
            i += 1
    return n


def _raw_string_prefix(text: str, i: int):
    m = re.match(r'r(#*)"', text[i:])
    return m.group(1) if m else None


def _skip_raw_string(text: str, i: int) -> int:
    hashes = _raw_string_prefix(text, i)
    close = '"' + "#" * len(hashes)
    start = i + 1 + len(hashes) + 1  # past r, hashes, opening quote
    end = text.find(close, start)
    return len(text) if end == -1 else end + len(close)


def _skip_char_or_lifetime(text: str, i: int) -> int:
    # `'a` lifetime or `'x'`/`'\n'` char literal. Only a real closing quote ends
    # a char literal; a lifetime has none, so just advance past the tick.
    m = re.match(r"'(?:\\.|[^'\\])'", text[i:])
    return i + m.end() if m else i + 1


# --------------------------------------------------------------------------- #
# Main                                                                        #
# --------------------------------------------------------------------------- #


def main() -> int:
    repo = Repo()
    problems: list[Problem] = []
    n_links = check_markdown_links(repo, problems)
    n_paths = check_doc_source_paths(repo, problems)
    n_refs = check_doc_citations(repo, problems)

    if problems:
        problems.sort(key=lambda p: p.source)
        print("Broken doc references:\n", file=sys.stderr)
        for p in problems:
            print(f"  {p.source}: {p.detail}", file=sys.stderr)
        print(
            f"\n{len(problems)} broken reference(s) across {n_links} Markdown "
            f"link(s), {n_paths} source-path mention(s), and {n_refs} doc citation(s).",
            file=sys.stderr,
        )
        return 1

    print(
        f"doc-refs OK: {n_links} Markdown link(s), {n_paths} source-path "
        f"mention(s), {n_refs} doc citation(s) checked."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

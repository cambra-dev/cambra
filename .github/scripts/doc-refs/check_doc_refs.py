#!/usr/bin/env python3
"""Validate cross-references into the docs so they can't silently rot.

Two checks, run together (see `.github/scripts/doc-refs/README.md`):

  A. doc -> doc: every intra-repo Markdown link `[text](path#anchor)` resolves
     to a file that exists, and when it carries a `#fragment` into a Markdown
     file, that anchor exists among the target's headings (GitHub slug rules).

  B. code -> doc: every `<name>.md` mentioned in a Rust *comment* resolves to a
     doc that exists, and any section title quoted immediately after it (the
     checkable citation convention) exists as a heading in that doc.

Both share one primitive: the set of valid anchors for a Markdown file, computed
with GitHub's heading-slug algorithm. No external dependencies — stdlib only.

Exit status is non-zero if any reference is broken, so `ci.sh` can gate on it.
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

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
    """File index + anchor cache, all rooted at REPO_ROOT."""

    def __init__(self) -> None:
        self.files: list[Path] = []
        for p in REPO_ROOT.rglob("*"):
            if p.is_dir():
                continue
            rel = p.relative_to(REPO_ROOT)
            if any(part in SKIP_DIRS for part in rel.parts):
                continue
            self.files.append(rel)
        self._file_set = set(self.files)
        # For suffix resolution of loosely-written code refs: map every
        # path-suffix of every Markdown file to the file(s) it could mean.
        self._md_by_suffix: dict[str, list[Path]] = {}
        for f in self.files:
            if f.suffix != ".md":
                continue
            parts = f.parts
            for i in range(len(parts)):
                suffix = "/".join(parts[i:])
                self._md_by_suffix.setdefault(suffix, []).append(f)
        self._anchor_cache: dict[Path, set[str]] = {}

    def exists(self, rel: Path) -> bool:
        # Normalize `.`/`..` without touching the filesystem, then confirm the
        # path is inside the repo and indexed (files) or a real directory.
        try:
            norm = Path(*rel.parts)
            resolved = (REPO_ROOT / rel).resolve()
            resolved.relative_to(REPO_ROOT)
        except ValueError:
            return False
        if resolved.is_dir():
            return True
        return norm in self._file_set or resolved.is_file()

    def anchors(self, rel: Path) -> set[str]:
        if rel not in self._anchor_cache:
            text = (REPO_ROOT / rel).read_text(encoding="utf-8", errors="replace")
            self._anchor_cache[rel] = heading_anchors(text)
        return self._anchor_cache[rel]

    def resolve_md_suffix(self, written: str) -> tuple[Path | None, list[Path]]:
        """Resolve a loosely-written doc path (e.g. `design/mutability.md` or a
        bare `mutability.md`) by unique path-suffix match. Returns
        (resolved, candidates); resolved is None when zero or >1 candidates."""
        cands = self._md_by_suffix.get(written.lstrip("./"), [])
        return (cands[0] if len(cands) == 1 else None, cands)


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

# Inline `[text](target)`. Targets with spaces/`)` are rare here; take up to the
# first whitespace or `)` and drop an optional `"title"` suffix.
_MD_LINK = re.compile(r"\[[^\]]*\]\(\s*(<[^>]+>|[^)\s]+)")
_INLINE_CODE = re.compile(r"`[^`]*`")


def check_markdown_links(repo: Repo, problems: list[Problem]) -> int:
    checked = 0
    for rel in repo.files:
        if rel.suffix != ".md":
            continue
        text = (REPO_ROOT / rel).read_text(encoding="utf-8", errors="replace")
        # Number lines but only scan those outside code fences; inline code
        # spans within a prose line are stripped so example links don't count.
        fenced = set(_fenced_line_numbers(text))
        for lineno, raw in enumerate(text.splitlines(), start=1):
            if lineno in fenced:
                continue
            line = _INLINE_CODE.sub("", raw)
            for m in _MD_LINK.finditer(line):
                target = m.group(1).strip("<>")
                if EXTERNAL_SCHEME.match(target):
                    continue
                checked += 1
                _check_one_link(repo, rel, lineno, target, problems)
    return checked


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
        (REPO_ROOT / tgt).resolve().relative_to(REPO_ROOT)
    except ValueError:
        return
    if not repo.exists(tgt):
        problems.append(Problem(src, f"link target does not exist: {target}"))
        return
    if frag and tgt.suffix == ".md":
        # Fragment normalized like the repo path: resolve `..`/`.`.
        norm = Path(*(REPO_ROOT / tgt).resolve().relative_to(REPO_ROOT).parts)
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
# Check B — Rust comment references to docs                                    #
# --------------------------------------------------------------------------- #

# A `<name>.md` path token as written in a comment (backticks, quotes, and other
# wrappers are handled by the comment-extraction step around it).
_MD_REF = re.compile(r"(?<![\w./-])([\w./-]+\.md)")

# The checkable-citation tail: after a doc ref, a run of one-or-more quoted
# section titles joined only by "glue" (separators/wrappers/§N/`and`). Any other
# word (`rule`, a `:`- introduced clause, a sentence) ends the run, so incidental
# body-text quotes further along the sentence are NOT treated as titles.
_CITATION_STEP = re.compile(r'(?:[\s,/()`§\d.]|and\b|—)*"([^"]+)"')


def check_code_refs(repo: Repo, problems: list[Problem]) -> int:
    checked = 0
    for rel in repo.files:
        if rel.suffix != ".rs":
            continue
        text = (REPO_ROOT / rel).read_text(encoding="utf-8", errors="replace")
        for lineno, comment in _rust_comment_spans(text):
            for m in _MD_REF.finditer(comment):
                written = m.group(1)
                checked += 1
                resolved, cands = repo.resolve_md_suffix(written)
                src = f"{rel}:{lineno}"
                if resolved is None:
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
                # Validate any section titles cited right after the ref.
                for title in _cited_titles(comment[m.end():]):
                    slug = _slug_base(_strip_md_markers(title))
                    if slug not in repo.anchors(resolved):
                        problems.append(
                            Problem(
                                src,
                                f'cited section "{title}" not found as a '
                                f"heading in {resolved} (see the citation "
                                f"convention in the doc-refs README)",
                            )
                        )
    return checked


def _cited_titles(tail: str):
    """Titles in the adjacent quoted-citation run at the start of `tail`."""
    pos = 0
    while True:
        m = _CITATION_STEP.match(tail, pos)
        if not m:
            return
        yield m.group(1)
        pos = m.end()


def _strip_md_markers(title: str) -> str:
    return title.replace("`", "")


def _rust_comment_spans(text: str):
    """Yield (line_number, comment_text) for every Rust comment in `text`.

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
            j = text.find("\n", i)
            j = n if j == -1 else j
            yield line, text[i:j]
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
            yield start_line, text[prev:i]
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
    n_refs = check_code_refs(repo, problems)

    if problems:
        problems.sort(key=lambda p: p.source)
        print("Broken doc references:\n", file=sys.stderr)
        for p in problems:
            print(f"  {p.source}: {p.detail}", file=sys.stderr)
        print(
            f"\n{len(problems)} broken reference(s) "
            f"across {n_links} Markdown link(s) and {n_refs} code ref(s).",
            file=sys.stderr,
        )
        return 1

    print(f"doc-refs OK: {n_links} Markdown link(s), {n_refs} code ref(s) checked.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

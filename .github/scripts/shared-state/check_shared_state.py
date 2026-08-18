#!/usr/bin/env python3
"""Gate the interpreter's no-back-channel invariant.

`src/interpreter/CLAUDE.md`, "Core invariant: data flows between operators as
Tiles, nothing else", says every operator-to-operator handoff goes through
`subscribe`/`get`/`release`. A back channel — two operators sharing an
`Rc<RefCell<…>>` of values — breaks that *silently*: the dependency is real but
invisible to the producer graph, every test still passes, and the graph no
longer describes the dataflow. That failure mode is why the rule is checked
rather than only stated.

The check is deliberately shallow: it flags **shared mutable state by shape**
inside `src/interpreter/`, and asks for each site to be either a known-legitimate
inner type or explicitly justified. It cannot prove the absence of a back channel
(a raw pointer, a global, a captured cell would all slip past); it makes the easy
way to build one impossible to add without writing down why.

Legitimate shared state falls into a few named kinds, listed in `ALLOWED_INNER`:
notification handles, late-wired operator slots, a fan-out's own branch state,
and external source handles. Anything else needs a justification comment:

    // shared-state-ok: <why this is not an operator-to-operator back channel>
    some_field: Rc<RefCell<Whatever>>,

Two things keep those justifications from becoming the way past the gate rather
than an argument about the code:

- **Test code is not scanned** (`_blank_test_items`). A spy recording what it was
  handed is shared state by shape but not a back channel, so justifying it buys
  nothing.
- **The justified sites are themselves listed** (`EXPECTED_EXCEPTIONS`). Adding
  one means editing this file, which puts the question in a diff a reviewer
  reads: is the exception necessary, or is there a tile shape that removes the
  need for it?

Run: python3 .github/scripts/shared-state/check_shared_state.py
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SCANNED_DIR = Path("src/interpreter")

# The cells whose contents can change through a shared reference.
INTERIOR = r"(?:RefCell|Cell|Mutex|RwLock|OnceLock|OnceCell)"

# The shapes that can carry values between two owners. The inner type is taken
# by matching angle brackets rather than by regex: `Rc<RefCell<Option<Box<dyn
# TileOperator>>>>` nests deeper than a non-greedy `.+?` can follow, and a
# truncated inner type would silently miss its `ALLOWED_INNER` entry.
SHARED_CELL_OPEN = re.compile(rf"\b(?:Rc|Arc)\s*<\s*{INTERIOR}\s*<")
# The same cell reached without a sharing wrapper of its own: a struct field
# whose *owner* supplies the sharing. `Arc<State>` where `State` holds a `Mutex`
# is `Arc<Mutex<…>>` with the layers swapped, and exactly as much of a back
# channel, so it is checked by the same rules.
BARE_CELL_OPEN = re.compile(
    rf"^[ \t]*(?:pub(?:\([^)]*\))?\s+)?[a-z_][a-z0-9_]*\s*:\s*{INTERIOR}\s*<", re.MULTILINE
)
# Ambient mutable state, which needs no sharing wrapper at all to be a back
# channel: a `static` is reachable from everywhere by name, whether its
# mutability comes from `mut` or from an interior-mutable cell.
AMBIENT = re.compile(rf"\bstatic\s+mut\b|\bthread_local!|\bstatic\s+\w+\s*:\s*{INTERIOR}\s*<")

JUSTIFICATION = re.compile(r"//\s*shared-state-ok:\s*\S")

# The justified exceptions the interpreter holds, as `(path, what)`. An exception is
# a permanent hole in the invariant, so adding one has to be a deliberate act rather
# than the cheapest way past a red build — editing this list is where the question
# gets asked. Listed rather than counted: a count gates only how many holes there
# are, so closing one and opening an unrelated one passes unseen, and the diff that
# adds an entry names the file it lands in. Removals fail too, so a hole that closes
# is given up rather than banked against the next one.
#
# Duplicate entries are meaningful — two sites in one file with the same shape are
# two exceptions. Test code is not listed: `_blank_test_items` skips it entirely.
EXPECTED_EXCEPTIONS = [
    ("src/interpreter/http_server.rs", "ambient mutable state"),
    ("src/interpreter/http_server.rs", "cell of `HashMap<usize, tiny_http::Request>`"),
    ("src/interpreter/http_server.rs", "shared cell of `HashMap<(String, String), RouteSender>`"),
    ("src/interpreter/mod.rs", "shared cell of `C`"),
    ("src/interpreter/tile_operators/cycle_slot.rs", "shared cell of `Option<Box<T>>`"),
    ("src/interpreter/tile_operators/fanout.rs", "cell of `bool`"),
    ("src/interpreter/tile_operators/fanout.rs", "shared cell of `Box<dyn TileOperator>`"),
    ("src/interpreter/tile_operators/fanout.rs", "shared cell of `Box<dyn TileOperator>`"),
    ("src/interpreter/tile_operators/mod.rs", "ambient mutable state"),
    ("src/interpreter/types/extent.rs", "shared cell of `Restriction`"),
    ("src/interpreter/types/extent.rs", "shared cell of `Restriction`"),
]

# Inner types that are legitimate by construction. Matched against the inner
# type with whitespace collapsed, so `Box<dyn Consumer>` and `Box< dyn Consumer >`
# are the same entry.
ALLOWED_INNER = {
    # Notification handles: a wakeup carries no value, only "pull me again".
    "dyn Consumer": "notification handle",
    "Box<dyn Consumer>": "notification handle",
    "Vec<SharedConsumer>": "notification queue",
    # Late-wired slots: a cycle cannot be built bottom-up, so the operator is
    # installed after construction. These hold *operators*, never values.
    #
    # No entry here spells a *slot*. `Option<Box<dyn TileOperator>>` and the bare
    # `Box<dyn TileOperator>` are both deliberately absent, because either shape
    # hand-rolls what `CycleSlot` already is, and `CycleSlot` carries its own
    # justification — a second copy has to argue for itself. `FanOut`'s owned
    # input is the one live site of the bare form and is listed by path in
    # `EXPECTED_EXCEPTIONS` instead, so allowing the *kind* would blanket-excuse
    # every future hand-rolled one to save a single annotation.
    "Option<Box<dyn TileProducer>>": "late-wired producer slot",
    "Option<Box<dyn TileProducer>>": "late-wired producer slot",
    # A fan-out and its branches are one logical operator; the shared state is
    # that operator's own bookkeeping, including the cyclic-mode tile memo.
    "FanOutShared": "fan-out branch state",
    # The external-world boundary: a data source's arrival state, shared with the
    # scheduler that feeds it. Side effects live at the boundary by design.
    "dyn DataSourceDomainExtentImpl": "external source handle",
}


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    text: str
    what: str


def _normalize(inner: str) -> str:
    """Canonical spelling: one space between words, none around punctuation.

    `Box< dyn Consumer >` and `Box<dyn Consumer>` are the same type and must hash
    to the same `ALLOWED_INNER` key, but `dyn Consumer` must keep its space —
    stripping all whitespace would fuse it into `dynConsumer`.
    """
    collapsed = re.sub(r"\s+", " ", inner).strip()
    collapsed = re.sub(r"\s*([<>])\s*", r"\1", collapsed)
    return re.sub(r"\s*,\s*", ", ", collapsed)


def _inner_type(text: str, start: int) -> str | None:
    """The balanced contents of the cell's type argument opening at `start`.

    `None` if the brackets do not close within `text` — a type split across
    lines, which the caller reports rather than guesses at.
    """
    depth = 1
    for i in range(start, len(text)):
        ch = text[i]
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth -= 1
            if depth == 0:
                return text[start:i]
    return None


def _justified(lines: list[str], idx: int) -> bool:
    """A justification sits on the offending line or the lines just above it.

    Doc comments often separate the annotation from the field, so scan upward
    past comment and attribute lines rather than requiring adjacency.
    """
    if JUSTIFICATION.search(lines[idx]):
        return True
    for prev in range(idx - 1, -1, -1):
        stripped = lines[prev].strip()
        if JUSTIFICATION.search(stripped):
            return True
        if stripped.startswith(("//", "#[")) or not stripped:
            continue
        return False
    return False


RAW_STRING = re.compile(r"b?r(#*)\"")


def _code_view(text: str) -> str:
    """`text` with comments and literals blanked to spaces, offsets preserved.

    Everything below reads Rust *syntax*, so a brace inside a string and a type
    named in a doc comment are both noise — and both desync the brace matching
    that skipping `#[cfg(test)]` items and reading a wrapped inner type depend
    on. Blanked rather than removed so a finding still maps to its line, and so a
    `//` comment ending a line cannot swallow the type wrapping onto the next.
    """
    out = list(text)
    n = len(text)

    def blank(start: int, end: int) -> None:
        for k in range(start, end):
            if out[k] != "\n":
                out[k] = " "

    i = 0
    while i < n:
        if text.startswith("//", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
        elif text.startswith("/*", i):
            depth, end = 1, i + 2
            while end < n and depth:
                if text.startswith("/*", end):
                    depth, end = depth + 1, end + 2
                elif text.startswith("*/", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
        elif (raw := RAW_STRING.match(text, i)) is not None:
            close = '"' + raw.group(1)
            found = text.find(close, raw.end())
            end = n if found < 0 else found + len(close)
        elif text[i] == '"':
            end = i + 1
            while end < n:
                if text[end] == "\\":
                    end += 2
                elif text[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
        elif text[i] == "'":
            # A char literal closes; a lifetime (`'a`) does not, and skipping to
            # the next quote would blank everything between two of them.
            if text.startswith("'\\", i):
                close = text.find("'", i + 2)
                end = n if close < 0 else close + 1
            elif i + 2 < n and text[i + 2] == "'":
                end = i + 3
            else:
                i += 1
                continue
        else:
            i += 1
            continue
        blank(i, end)
        i = max(end, i + 1)
    return "".join(out)


CFG_TEST = re.compile(r"#\[cfg\(test\)\]")


def _blank_test_items(code: str) -> str:
    """`code` with every `#[cfg(test)]`-gated item blanked out.

    Test code is not the runtime. A spy that records what it was handed is shared
    state by shape and a back channel by no definition, and making each one argue
    for itself spends the reader's attention where there is nothing to decide —
    and inflates the exception count, whose whole value is that it is small enough
    to be read.

    Only `#[cfg(test)]` is skipped. `#[cfg(any(test, feature = "test-helpers"))]`
    is *not*: it compiles into a real library build, so it is production code that
    tests happen to also use, and it is checked like any other.

    The gated item is found by matching its braces (or its `;`, for a gated `use`),
    because a `#[cfg(test)]` is not always the trailing `mod tests` — it also gates
    single functions mid-file.
    """
    out = list(code)
    for attr in CFG_TEST.finditer(code):
        end, depth, started = attr.end(), 0, False
        while end < len(code):
            ch = code[end]
            if ch == "{":
                depth, started = depth + 1, True
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end += 1
                    break
            elif ch == ";" and not started:
                end += 1
                break
            end += 1
        for k in range(attr.start(), min(end, len(code))):
            if out[k] != "\n":
                out[k] = " "
    return "".join(out)


# How far past a cell's opening bracket to look for its closing one. A wrapped
# type spans a few lines at most; scanning further would let an unbalanced `<`
# elsewhere in the file pair up with something unrelated and report a nonsense
# inner type instead of the honest `<unterminated type>`.
INNER_SCAN_CHARS = 400


def check_file(path: Path, text: str) -> tuple[list[Finding], list[Finding]]:
    """`(findings, exceptions)` for one file.

    An *exception* is a site that matched a shape and was excused by a
    `shared-state-ok` on it. They are returned rather than merely suppressed
    because the set of them is itself gated — see [`EXPECTED_EXCEPTIONS`].
    """
    findings: list[Finding] = []
    exceptions: list[Finding] = []
    lines = text.splitlines()
    rel = str(path.relative_to(ROOT))
    # Scanned over the whole file rather than line by line, because rustfmt wraps
    # a long type: `Rc<\n    RefCell<…>>` is the same cell as the one-line
    # spelling, and matching per line would not see it at all — the opposite of
    # the deliberate `<unterminated type>` report, which at least fails the gate.
    code = _blank_test_items(_code_view(text))

    def record(idx: int, what: str) -> None:
        # `_justified` reads the *raw* lines: the annotation is a comment, and the
        # code view has blanked every comment away.
        (exceptions if _justified(lines, idx) else findings).append(
            Finding(rel, idx + 1, lines[idx].strip(), what)
        )

    for pattern, what in ((SHARED_CELL_OPEN, "shared cell"), (BARE_CELL_OPEN, "cell")):
        for match in pattern.finditer(code):
            idx = code.count("\n", 0, match.start())
            raw = _inner_type(code[: match.end() + INNER_SCAN_CHARS], match.end())
            inner = _normalize(raw) if raw is not None else "<unterminated type>"
            if inner in ALLOWED_INNER:
                continue
            record(idx, f"{what} of `{inner}`")
    for match in AMBIENT.finditer(code):
        record(code.count("\n", 0, match.start()), "ambient mutable state")
    findings.sort(key=lambda f: f.line)
    exceptions.sort(key=lambda f: f.line)
    return findings, exceptions


def main() -> int:
    root = ROOT / SCANNED_DIR
    if not root.is_dir():
        print(f"shared-state: {SCANNED_DIR} not found (run from the repo)", file=sys.stderr)
        return 1
    findings: list[Finding] = []
    exceptions: list[Finding] = []
    scanned = 0
    for path in sorted(root.rglob("*.rs")):
        scanned += 1
        found, excused = check_file(path, path.read_text(encoding="utf-8"))
        findings.extend(found)
        exceptions.extend(excused)
    if findings:
        print("shared-state: unjustified shared mutable state in the interpreter\n")
        for f in findings:
            print(f"  {f.path}:{f.line}: {f.what}")
            print(f"      {f.text}")
        print(
            "\nData flows between operators only as tiles, pulled by `get` "
            '(src/interpreter/CLAUDE.md, "Core invariant: data flows between '
            'operators as Tiles, nothing else").\n'
            "If this is genuinely not an operator-to-operator back channel, say why:\n"
            "    // shared-state-ok: <reason>\n"
            "and if the reason is a *kind* that will recur, add it to ALLOWED_INNER "
            "in this checker instead."
        )
        return 1
    have = Counter((f.path, f.what) for f in exceptions)
    added = sorted((have - Counter(EXPECTED_EXCEPTIONS)).elements())
    removed = sorted((Counter(EXPECTED_EXCEPTIONS) - have).elements())
    if added or removed:
        print("shared-state: the justified-exception list is out of date.\n")
        for path, what in added:
            print(f"  + {path}: {what}")
        for path, what in removed:
            print(f"  - {path}: {what}")
        if added:
            print(
                f"\n{len(added)} new exception(s). Before adding to EXPECTED_EXCEPTIONS "
                "in this checker,\nsettle the question the list exists to force: is the "
                "exception necessary,\nor is there a tile shape that removes the need for "
                "it? A justification is not\na cost-free annotation — it is a permanent "
                "hole in the invariant."
            )
        if removed:
            print(
                f"\n{len(removed)} exception(s) no longer present — drop them from "
                "EXPECTED_EXCEPTIONS.\nThe list only ratchets down."
            )
        return 1
    print(
        f"shared-state OK: {scanned} interpreter source file(s) checked, "
        f"{len(exceptions)} justified exception(s)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

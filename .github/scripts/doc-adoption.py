#!/usr/bin/env python3
"""Fail on an item inserted at the bottom of another item's doc block.

The inserted item adopts the doc above it and the item it displaced is left
undocumented. Both halves are silent: the new item reads as documented, and the
displaced one is only missing a comment.

The signature is in the diff, not the file. A run of added lines that begins with
a comment line, whose immediately-preceding context line is also a comment line,
and that declares an item. An item added *after* an existing one anchors on the
blank line or the closing brace above it, so it never matches; only an item
inserted *into* a doc block does.

Scanning per commit rather than the branch diff: a region rewritten by a later
commit hides the insertion in the squashed diff.

Suppress a deliberate merge with `doc-adoption-ok` on any line of the added run.
"""

import re
import subprocess
import sys

ITEM = {
    "rs": re.compile(
        r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:default\s+)?(?:async\s+)?(?:unsafe\s+)?"
        r'(?:extern\s+"[^"]*"\s+)?(?:fn|enum|struct|trait|impl|type|const|static|mod|union)\b'
    ),
    "ts": re.compile(
        r"^\s*(?:export\s+)?(?:default\s+)?(?:async\s+)?"
        r"(?:function|class|interface|type|const|enum)\b"
    ),
}
DOC = {"rs": re.compile(r"^\s*(?:///|//!)"), "ts": re.compile(r"^\s*//")}
ATTR = re.compile(r"^\s*(?:#\[|@)")
SUPPRESS = "doc-adoption-ok"


def lang(path):
    if path.endswith(".rs"):
        return "rs"
    if path.endswith((".ts", ".tsx")):
        return "ts"
    return None


def scan(diff):
    """Every (path, context_line, item_line) the diff inserts into a doc block."""
    hits, path, kind, ctx = [], None, None, None
    lines = diff.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("+++ b/"):
            path = line[6:]
            kind, ctx = lang(path), None
        elif line.startswith("@@"):
            ctx = None
        elif kind and line.startswith("+") and not line.startswith("+++"):
            run, j = [], i
            while j < len(lines) and lines[j].startswith("+") and not lines[j].startswith("+++"):
                run.append(lines[j][1:])
                j += 1
            inserted_into_doc = ctx is not None and DOC[kind].match(ctx) and DOC[kind].match(run[0])
            if inserted_into_doc and not any(SUPPRESS in r for r in run):
                for n, row in enumerate(run):
                    if not ITEM[kind].match(row) or DOC[kind].match(row):
                        continue
                    m = n - 1
                    while m >= 0 and ATTR.match(run[m]):
                        m -= 1
                    if m >= 0 and DOC[kind].match(run[m]):
                        hits.append((path, ctx.strip(), row.strip()))
                    break
            i, ctx = j, None
            continue
        elif kind and line.startswith(" "):
            ctx = line[1:]
        elif kind and line.startswith("-"):
            ctx = None
        i += 1
    return hits


def main(base, tip):
    revs = subprocess.run(
        ["git", "rev-list", f"{base}..{tip}"], capture_output=True, text=True, check=True
    ).stdout.split()
    found = 0
    for rev in revs:
        diff = subprocess.run(
            ["git", "show", "--unified=3", "--no-color", "--format=", rev],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        for path, ctx, item in scan(diff):
            found += 1
            print(
                f"{path}: `{item}` was inserted under the doc block ending\n"
                f"    {ctx}\n"
                f"  which documents the item below it. Split the block: the new item takes\n"
                f"  its own doc and the displaced item keeps the one it had ({rev[:9]})."
            )
    if found:
        print(f"\ndoc-adoption: {found} adopted doc block(s).")
        return 1
    print(f"doc-adoption OK: {len(revs)} commit(s) checked.")
    return 0


if __name__ == "__main__":
    sys.exit(
        main(
            sys.argv[1] if len(sys.argv) > 1 else "origin/main",
            sys.argv[2] if len(sys.argv) > 2 else "HEAD",
        )
    )

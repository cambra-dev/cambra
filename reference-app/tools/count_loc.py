#!/usr/bin/env python3
"""Counts both implementations by purpose, and prints the tables in docs/REPORT.md.

Physical source lines come from `cloc`, which is the mechanical part: it decides
what is code, what is comment, and what is blank, and this script never
second-guesses it. The purpose of a line is the manual part, and it comes from
`classification.json` — a file glob for a whole file, a line range for a file
that mixes purposes. Every line of both implementations is assigned exactly one
purpose, and the run fails if any file is unclassified, so nothing is quietly
dropped.

The two mechanisms are reported separately because they are not equally
trustworthy: a glob assignment is checkable by reading one path, a range
assignment by reading the range.

    python3 tools/count_loc.py            # the tables
    python3 tools/count_loc.py --json     # the same numbers, machine-readable
"""

import argparse
import fnmatch
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = json.loads((HERE / "classification.json").read_text())
ROOT = HERE.parent


class Unclassified(Exception):
    pass


def cloc(root: Path, include: list[str], force_lang: list[str]) -> dict:
    """Per-file physical SLOC, comments, and blanks, as cloc reports them.

    Scope comes from `include` alone. cloc's own `--exclude-dir` matches a bare
    directory name at any depth, which silently drops `storefront/tools/` along
    with the repository's `tools/`; naming what to count avoids the question.
    """
    cmd = ["cloc", "--by-file", "--json", "--quiet"]
    cmd += [f"--force-lang={spec}" for spec in force_lang]
    cmd += include
    out = subprocess.run(cmd, cwd=root, capture_output=True, text=True, check=True).stdout
    return {
        path.removeprefix("./"): stats
        for path, stats in json.loads(out).items()
        if path not in ("header", "SUM")
    }


def classify_file(rel: str) -> str:
    for pattern, category in SPEC["globs"]:
        if fnmatch.fnmatch(rel, pattern) or fnmatch.fnmatch(Path(rel).name, pattern):
            return category
    raise Unclassified(rel)


def is_code(line: str) -> bool:
    """The range splitter's own code test.

    Only used to divide a file that mixes purposes; the per-file total always
    comes from cloc, and `split_by_range` scales to it, so a disagreement
    between this test and cloc's shifts lines between categories within one file
    and never changes a total.
    """
    stripped = line.strip()
    return bool(stripped) and not stripped.startswith(("#", "--", "//"))


def split_by_range(path: Path, ranges: list, cloc_code: int) -> dict[str, int]:
    lines = path.read_text().splitlines()
    counted: dict[str, int] = defaultdict(int)
    for start, end, category in ranges:
        counted[category] += sum(
            1 for line in lines[start - 1 : end] if is_code(line)
        )
    total = sum(counted.values())
    if total == 0:
        return {}
    if total != cloc_code:
        # Hand the difference to the largest bucket rather than losing it.
        biggest = max(counted, key=lambda c: counted[c])
        counted[biggest] += cloc_code - total
    return dict(counted)


def count(name: str) -> dict:
    impl = SPEC["implementations"][name]
    root = (ROOT / impl["root"]).resolve()
    files = cloc(root, impl["include"], impl.get("force_lang", []))

    by_category: dict[str, int] = defaultdict(int)
    comments = 0
    from_ranges = 0
    from_globs = 0
    unclassified = []
    for rel, stats in sorted(files.items()):
        comments += stats["comment"]
        ranges = SPEC["ranges"].get(rel) or SPEC["ranges"].get(Path(rel).name)
        if ranges:
            for category, lines in split_by_range(root / rel, ranges, stats["code"]).items():
                by_category[category] += lines
            from_ranges += stats["code"]
            continue
        try:
            by_category[classify_file(rel)] += stats["code"]
        except Unclassified:
            unclassified.append(rel)
            continue
        from_globs += stats["code"]
    if unclassified:
        raise Unclassified(", ".join(unclassified))

    excluded = set(SPEC["excluded_from_application_total"])
    return {
        "files": len(files),
        "by_category": dict(by_category),
        "comments": comments,
        "total": sum(by_category.values()),
        "application_total": sum(
            n for c, n in by_category.items() if c not in excluded
        ),
        "classified_by_range": from_ranges,
        "classified_by_glob": from_globs,
    }


def markdown(results: dict[str, dict]) -> str:
    order = list(SPEC["categories"])
    excluded = set(SPEC["excluded_from_application_total"])
    rows = ["| Purpose | Cambra | Conventional | Ratio |", "|---|---:|---:|---:|"]
    for category in order:
        cam = results["cambra"]["by_category"].get(category, 0)
        con = results["conventional"]["by_category"].get(category, 0)
        if cam == 0 and con == 0:
            ratio = "—"
        elif cam == 0:
            ratio = "n/a"
        else:
            ratio = f"{con / cam:.1f}×"
        label = f"{category} *(excluded)*" if category in excluded else category
        rows.append(f"| {label} | {cam} | {con} | {ratio} |")
    cam = results["cambra"]["application_total"]
    con = results["conventional"]["application_total"]
    rows.append(f"| **Application total** | **{cam}** | **{con}** | **{con / cam:.1f}×** |")
    cam_all = results["cambra"]["total"]
    con_all = results["conventional"]["total"]
    rows.append(
        f"| **Everything, tests and stubs included** | **{cam_all}** | **{con_all}** "
        f"| **{con_all / cam_all:.1f}×** |"
    )

    provenance = [
        "",
        "| | Cambra | Conventional |",
        "|---|---:|---:|",
        f"| Files | {results['cambra']['files']} | {results['conventional']['files']} |",
        f"| Code lines classified by file glob | {results['cambra']['classified_by_glob']} "
        f"| {results['conventional']['classified_by_glob']} |",
        f"| Code lines classified by hand-written line range "
        f"| {results['cambra']['classified_by_range']} "
        f"| {results['conventional']['classified_by_range']} |",
        f"| Comment lines (not counted above) | {results['cambra']['comments']} "
        f"| {results['conventional']['comments']} |",
    ]
    return "\n".join(rows + provenance)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit the raw numbers")
    args = parser.parse_args()
    try:
        results = {name: count(name) for name in SPEC["implementations"]}
    except Unclassified as exc:
        print(f"unclassified files (add a glob to classification.json): {exc}", file=sys.stderr)
        return 1
    except FileNotFoundError:
        print("cloc is not installed; see docs/REPORT.md for the method", file=sys.stderr)
        return 1
    print(json.dumps(results, indent=2) if args.json else markdown(results))
    return 0


if __name__ == "__main__":
    sys.exit(main())

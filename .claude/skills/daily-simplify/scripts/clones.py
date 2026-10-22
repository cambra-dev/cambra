#!/usr/bin/env python3
"""Report near-duplicate regions across Rust files, as seeds for an LLM finder.

    clones.py <root> [--window 8] [--top 40] [--rename]

Lines are normalized (comments, blank lines and brace-only lines dropped; string and number
literals replaced), then every run of `--window` consecutive normalized lines is hashed. Two
locations sharing consecutive window hashes form a clone region. `--rename` also replaces
identifiers, which finds renamed copies (type-2 clones) at the price of more noise: a sequence of
match arms on the same enum looks alike under renaming.

The output is a candidate list, not a verdict. A clone region is worth a finder's time only when
the two copies encode the same decision; parallel structure over different enums is often the
right shape for a compiler.
"""
import argparse
import collections
import hashlib
import os
import re
import sys

SKIP_DIRS = {"target", "node_modules", ".jj", ".git", "web", "formal"}
KEYWORDS = set(
    "as break const continue crate else enum extern false fn for if impl in let loop match mod "
    "move mut pub ref return self Self static struct super trait true type unsafe use where while "
    "Some None Ok Err".split()
)
STR = re.compile(r'r#*"(?:[^"\\]|\\.)*"#*|"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)\'')
NUM = re.compile(r"\b\d[\d_]*(?:\.\d+)?\w*\b")
IDENT = re.compile(r"\b[A-Za-z_]\w*\b")
TRIVIAL = re.compile(r"^[\s{}()\[\];,]*$")


def normalize(path, rename):
    out = []  # (original line number, normalized text)
    with open(path, encoding="utf-8", errors="replace") as f:
        for no, line in enumerate(f, 1):
            s = line.split("//", 1)[0].strip()
            if not s or TRIVIAL.match(s) or s.startswith(("#[", "use ", "pub use ", "mod ")):
                continue
            s = STR.sub('"S"', s)
            s = NUM.sub("N", s)
            if rename:
                s = IDENT.sub(lambda m: m.group(0) if m.group(0) in KEYWORDS else "I", s)
            out.append((no, re.sub(r"\s+", " ", s)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--window", type=int, default=8)
    ap.add_argument("--top", type=int, default=40)
    ap.add_argument("--rename", action="store_true")
    ap.add_argument("--max-occurrences", type=int, default=6,
                    help="skip window hashes seen more often (boilerplate)")
    args = ap.parse_args()
    w = args.window

    files = {}
    for dirpath, dirnames, filenames in os.walk(args.root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS and not d.startswith(".")]
        for fn in filenames:
            if fn.endswith(".rs"):
                p = os.path.join(dirpath, fn)
                files[os.path.relpath(p)] = normalize(p, args.rename)

    occ = collections.defaultdict(list)
    for f, lines in files.items():
        for i in range(len(lines) - w + 1):
            h = hashlib.blake2b("\n".join(t for _, t in lines[i:i + w]).encode(),
                                digest_size=8).digest()
            occ[h].append((f, i))

    pairs = collections.defaultdict(list)  # (fa, fb) -> [(ia, ib)]
    for locs in occ.values():
        if not 2 <= len(locs) <= args.max_occurrences:
            continue
        for a in range(len(locs)):
            for b in range(a + 1, len(locs)):
                (fa, ia), (fb, ib) = sorted((locs[a], locs[b]))
                if fa == fb and abs(ia - ib) < w:
                    continue  # overlapping windows of one region
                pairs[(fa, fb)].append((ia, ib))

    regions = []
    for (fa, fb), hits in pairs.items():
        hits.sort()
        hitset = set(hits)
        for ia, ib in hits:
            if (ia - 1, ib - 1) in hitset:
                continue  # not the start of a run
            n = 1
            while (ia + n, ib + n) in hitset:
                n += 1
            span = n + w - 1
            la, lb = files[fa], files[fb]
            regions.append((span, fa, la[ia][0], la[ia + span - 1][0],
                            fb, lb[ib][0], lb[ib + span - 1][0]))

    regions.sort(key=lambda r: -r[0])
    kind = "renamed (type-2)" if args.rename else "exact (type-1)"
    print(f"# {kind} clone regions, window={w}, top {args.top} of {len(regions)}")
    print("# normalized-lines  fileA:start-end  <->  fileB:start-end")
    for span, fa, sa, ea, fb, sb, eb in regions[:args.top]:
        print(f"{span:4d}  {fa}:{sa}-{ea}  <->  {fb}:{sb}-{eb}")


if __name__ == "__main__":
    sys.exit(main())

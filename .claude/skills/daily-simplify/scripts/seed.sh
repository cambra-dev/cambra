#!/usr/bin/env bash
# Collect the deterministic signals that seed the finders.
#
#   seed.sh <workspace-dir> <out-dir> [--no-clippy]
#
# Writes <out-dir>/seeds.md (the digest the finders read) plus the raw files it summarizes.
# Every section is a candidate list, not a verdict: lint and clone output is noisy, and a
# hotspot is where simplification pays back, not proof that something is wrong.
#
# The clippy pass builds in the scout workspace's persistent target dir, so day two onward is
# incremental. Thresholds are lowered from clippy's defaults because at the defaults
# `cognitive_complexity` fires on two sites in the whole repo
# (vault/projects/code-health-tooling/_index.md).
set -euo pipefail

WS="${1:?workspace dir}"
OUT="${2:?out dir}"
CLIPPY=1
[[ "${3:-}" == "--no-clippy" ]] && CLIPPY=0

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="" TODAY=""
paths="$("${HERE}/workspace.sh" paths)"
eval "${paths}"
TARGET="$("${HERE}/workspace.sh" target scout)"
mkdir -p "${OUT}"
cd "${WS}"

ROOTS=(src chl-parser/src chl-interp/src)
DIGEST="${OUT}/seeds.md"
: > "${DIGEST}"
section() { printf '\n## %s\n\n' "$1" >> "${DIGEST}"; }

base="$(jj log -r @- --no-graph -T 'commit_id.short(12)')"
echo "# Seed signals — ${TODAY}, main@origin ${base}" >> "${DIGEST}"

# --- Hotspots: 120-day change count x code lines. -------------------------------------------
section "Hotspots (commits touching the file in 120 days × code lines)"
git -C "${REPO}" log origin/main --since=120.days --name-only --format= -- '*.rs' \
  | sort | uniq -c | awk '{print $2"\t"$1}' > "${OUT}/churn.tsv"
tokei -t Rust -o json "${ROOTS[@]}" > "${OUT}/tokei.json"
python3 -I - "${OUT}/churn.tsv" "${OUT}/tokei.json" >> "${DIGEST}" <<'PY'
import json, sys
churn = dict(l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if "\t" in l)
loc = {r["name"].lstrip("./"): r["stats"]["code"]
       for r in json.load(open(sys.argv[2]))["Rust"]["reports"]}
rows = sorted(((int(churn.get(f, 0)) * n, int(churn.get(f, 0)), n, f) for f, n in loc.items()),
              reverse=True)[:30]
print("| score | commits | code lines | file |\n|---|---|---|---|")
for s, c, n, f in rows:
    print(f"| {s} | {c} | {n} | `{f}` |")
PY

# --- Clones. ----------------------------------------------------------------------------------
section "Exact clone regions (production code)"
{
  echo '```'
  for r in "${ROOTS[@]}"; do python3 -I "${HERE}/clones.py" "${r}" --top 15; done
  echo '```'
} >> "${DIGEST}"
section "Renamed clone regions (production code; noisier — parallel match arms look alike)"
{
  echo '```'
  python3 -I "${HERE}/clones.py" src --rename --window 10 --top 25
  echo '```'
} >> "${DIGEST}"
if command -v cargo-dupes > /dev/null 2>&1; then
  section "cargo-dupes (AST-normalized clones)"
  { echo '```'; cargo dupes 2>&1 | awk 'NR<=80'; echo '```'; } >> "${DIGEST}"
fi

# --- Module coupling. -------------------------------------------------------------------------
section "Cross-module \`use crate::\` edges in src/ (back-edges against the pipeline are debt)"
python3 -I - >> "${DIGEST}" <<'PY'
import collections, os, re
edges = collections.Counter()
for d, _, fs in os.walk("src"):
    for f in fs:
        if not f.endswith(".rs"):
            continue
        p = os.path.join(d, f)
        parts = p.split(os.sep)
        frm = parts[1].removesuffix(".rs")
        for m in re.finditer(r"\bcrate::(\w+)", open(p, encoding="utf-8").read()):
            if m.group(1) != frm:
                edges[(frm, m.group(1))] += 1
print("| from | to | references |\n|---|---|---|")
for (a, b), n in edges.most_common(20):
    print(f"| {a} | {b} | {n} |")
PY

# --- Change coupling: files that change together with no import between them. -------------
section "Files that change together (120 days, commits touching ≤ 15 files; pairs in different directories first)"
git -C "${REPO}" log origin/main --since=120.days --name-only --format='format:@@' -- '*.rs' \
  > "${OUT}/cochange.txt"
python3 -I - "${OUT}/cochange.txt" "${ROOTS[@]}" >> "${DIGEST}" <<'PY'
import collections, itertools, os, re, sys
roots = tuple(r.rstrip("/") + "/" for r in sys.argv[2:])
commits, cur = [], set()
for line in open(sys.argv[1]):
    line = line.strip()
    if line == "@@":
        if cur:
            commits.append(cur)
        cur = set()
    elif line.startswith(roots) and os.path.exists(line):
        cur.add(line)
if cur:
    commits.append(cur)
n, co = collections.Counter(), collections.Counter()
for files in commits:
    if len(files) > 15:
        continue  # sweeping renames say nothing about coupling
    n.update(files)
    co.update(itertools.combinations(sorted(files), 2))
rows = []
for (a, b), c in co.items():
    ratio = c / min(n[a], n[b])
    if c >= 4 and ratio >= 0.5:
        same_dir = os.path.dirname(a) == os.path.dirname(b)
        rows.append((same_dir, -ratio, -c, a, b, n[a], n[b]))
rows.sort()
# No import column: cambra imports through re-exports (`crate::interpreter::tiling::{Tile, ..}`),
# so a textual import check reports most real dependencies as absent.
print("| together | ratio | file A (commits) | file B (commits) |\n|---|---|---|---|")
for _, r, c, a, b, na, nb in rows[:25]:
    print(f"| {-c} | {-r:.2f} | `{a}` ({na}) | `{b}` ({nb}) |")
PY

# --- Defensive handling of supposedly impossible cases. --------------------------------------
section "Defensive-handling markers (code that handles a case it believes cannot happen)"
{
  echo '```'
  grep -rniE --include='*.rs' \
    '//.*(should never|can.?t happen|cannot happen|should(n.?t| not) happen|defensive|just in case|to be safe|in case (it|the|a|we))' \
    "${ROOTS[@]}" | cut -c1-200 | awk 'NR<=50'
  echo '```'
} >> "${DIGEST}"

# --- Acknowledged complexity in comments. -----------------------------------------------------
section "Comments that admit a workaround (TODO/FIXME/HACK/for now/workaround/temporary)"
{
  echo '```'
  grep -rnE --include='*.rs' '(TODO|FIXME|HACK|XXX|for now|workaround|temporar(y|ily)|until we)' \
    "${ROOTS[@]}" | cut -c1-200 | awk 'NR<=60'
  echo '```'
  echo
  allows="$(grep -rn --include='*.rs' '#\[allow(' "${ROOTS[@]}" || true)"
  echo "\`#[allow(...)]\` sites: $(grep -c . <<< "${allows}" || true)"
} >> "${DIGEST}"

# --- Clippy, with complexity thresholds lowered. ----------------------------------------------
if (( CLIPPY )); then
  section "Clippy candidates (lowered thresholds; candidates, not defects)"
  CONF="$(mktemp -d)"
  trap 'rm -rf "${CONF}"' EXIT
  cp clippy.toml "${CONF}/clippy.toml"
  printf '\ncognitive-complexity-threshold = 15\ntoo-many-lines-threshold = 120\n' >> "${CONF}/clippy.toml"
  LINTS=(cognitive_complexity too_many_lines match_same_arms redundant_clone unnecessary_wraps
         needless_pass_by_value unused_self redundant_pub_crate needless_collect
         option_if_let_else manual_let_else if_same_then_else branches_sharing_code)
  FLAGS=()
  for l in "${LINTS[@]}"; do FLAGS+=(-W "clippy::${l}"); done
  CARGO_TARGET_DIR="${TARGET}" CLIPPY_CONF_DIR="${CONF}" \
    cargo clippy -p cambra -p chl-parser -p chl-interp --message-format=json -q -- "${FLAGS[@]}" \
    > "${OUT}/clippy.jsonl" 2> "${OUT}/clippy.stderr" || true
  python3 -I - "${OUT}/clippy.jsonl" >> "${DIGEST}" <<'PY'
import collections, json, sys
seen, by_lint = set(), collections.defaultdict(list)
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    msg = m.get("message") if m.get("reason") == "compiler-message" else None
    if not msg or not msg.get("code") or not msg["spans"]:
        continue
    code = msg["code"]["code"]
    if not code.startswith("clippy::") and code != "dead_code":
        continue
    sp = next((s for s in msg["spans"] if s["is_primary"]), msg["spans"][0])
    key = (code, sp["file_name"], sp["line_start"])
    if key in seen:
        continue
    seen.add(key)
    by_lint[code].append(f'{sp["file_name"]}:{sp["line_start"]}  {msg["message"][:110]}')
if not by_lint:
    print("(no clippy output — see clippy.stderr; did the build fail?)")
for code, hits in sorted(by_lint.items(), key=lambda kv: -len(kv[1])):
    print(f"### `{code}` — {len(hits)}\n\n```")
    print("\n".join(hits[:25]))
    if len(hits) > 25:
        print(f"... {len(hits) - 25} more in clippy.jsonl")
    print("```\n")
PY
fi

echo "seeds: ${DIGEST}"

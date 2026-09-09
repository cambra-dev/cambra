#!/usr/bin/env bash
# Dump every named gallery program's snapshot and render its operator pane,
# writing <out>/<name>.snapshot.json, <name>.report.json and <name>.graph.html.
#
#   scripts/render-corpus.sh <out-dir> [program ...]
#
# A debugging tool. It runs the pane's own code — `drawGraphOf`, the rule list
# and `ElkLayout`, imported from `web/src/` — so what it reports is what the
# inspector draws, and it cannot drift from it.
set -euo pipefail

out=${1:?usage: render-corpus.sh <out-dir> [program ...]}
shift
progs=("$@")
if [[ ${#progs[@]} -eq 0 ]]; then
  progs=(list_min udf_closure arithmetic prefix_lines streaming_echo polymorphic defer_lift
    source_shared groupby_rollup filter_and_aggregate generator_pipeline
    groupby_filtered_rollup for_accumulator join_then_groupby inner_join txn_multi_read
    order_ledger asset_cart)
fi

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(cd -- "${here}/../.." && pwd)
mkdir -p -- "${out}"

for p in "${progs[@]}"; do
  src="${root}/tests/programs/${p}/program.cambra"
  [[ -f ${src} ]] || src="${root}/tests/programs/${p}/v0.cambra"
  if [[ ! -f ${src} ]]; then
    echo "skip ${p}: no source" >&2
    continue
  fi
  if ! (cd -- "${root}" && cargo run -q -- --dump-snapshot "${src}") \
    >"${out}/${p}.snapshot.json" 2>"${out}/${p}.dump.err"; then
    echo "skip ${p}: --dump-snapshot failed" >&2
    continue
  fi
  npx vite-node "${here}/render-graph.ts" -- "${out}/${p}.snapshot.json" \
    --html "${out}/${p}.graph.html" >"${out}/${p}.report.json" 2>/dev/null
  OPG_NAME=${p} OPG_REPORT="${out}/${p}.report.json" python3 - <<'PY'
import json
import os

report = json.load(open(os.environ["OPG_REPORT"]))
print(
    "%-24s wire %4d  boxes %4d  chips %4d  glyphs %4d  edges %4d (back %d)"
    % (
        os.environ["OPG_NAME"],
        report["wire"]["nodes"],
        report["drawn"]["boxes"],
        report["drawn"]["chips"],
        report["drawn"]["glyphs"],
        report["drawn"]["edges"],
        report["drawn"]["backEdges"],
    )
)
PY
done

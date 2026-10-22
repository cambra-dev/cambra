#!/usr/bin/env bash
# Clear room for today's run, or stop it when the machine has too little disk.
#
#   preflight.sh <log-file>
#
# Removes run directories older than 14 days and sweeps each workspace's cargo target down to
# `SIMPLIFY_TARGET_MAX` (default 12GB) with `cargo sweep`. Prints the free disk under the cache. A
# run needs 50 GB free, since each target grows by a test build; with less, appends the reason to
# <log-file> and exits 3.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
LOG="${1:?log file}"
REPO="" CACHE="" TODAY=""
paths="$("${HERE}/workspace.sh" paths)"
eval "${paths}"

stop() {
  mkdir -p "$(dirname "${LOG}")"
  if [[ ! -e "${LOG}" ]]; then
    printf -- '---\ntype: log\ndate: %s\n---\n\n# Simplification run — %s\n' "${TODAY}" "${TODAY}" \
      > "${LOG}"
  fi
  now="$(TZ=America/Denver date +%H:%M)"
  printf '\n## Run skipped — %s\n\n%s\n' "${now}" "$1" >> "${LOG}"
  echo "preflight: $1" >&2
  exit 3
}

mkdir -p "${CACHE}/runs"
find "${CACHE}/runs" -mindepth 1 -maxdepth 1 -type d -mtime +14 -exec rm -rf {} +

command -v cargo-sweep > /dev/null || stop "cargo-sweep is not installed (cargo install cargo-sweep)."
for target in "${CACHE}"/target-*; do
  [[ -d "${target}" ]] || continue
  CARGO_TARGET_DIR="${target}" cargo sweep --maxsize "${SIMPLIFY_TARGET_MAX:-12GB}" "${REPO}" >&2
done

disk="$(df -BG --output=avail "${CACHE}" | tail -n 1)"
disk_gb="${disk//[!0-9]/}"
(( disk_gb >= 50 )) || stop "Only ${disk_gb} GB free under ${CACHE}; a run needs 50 GB."

printf 'free_disk_gb=%s\n' "${disk_gb}"

#!/usr/bin/env bash
# Run a command in a simplify workspace, under that workspace's cargo target and a timeout.
#
#   in-workspace.sh <workspace-dir> <seconds> <command> [args...]
#
# Agents run every build and test through this script, so each uses the workspace's persistent
# target. The timeout ends a test that a temporary break sent into a loop.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ws="${1:?workspace dir}"
secs="${2:?timeout in seconds}"
shift 2

name="$(basename "${ws}")"
target="$("${HERE}/workspace.sh" target "${name#cambra-simplify-}")"
cd "${ws}"
export CARGO_TARGET_DIR="${target}"
exec timeout "${secs}" "$@"

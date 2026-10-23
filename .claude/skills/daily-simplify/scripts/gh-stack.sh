#!/usr/bin/env bash
# Run `gh stack` in the run's scratch clone of cambra.
#
#   gh-stack.sh <run-dir> <gh stack arguments...>
#
# `gh stack` needs a git checkout on a branch, and its `checkout`, `init` and `submit` write local
# branches and tracking state. Run workspaces have no `.git`, and the default workspace holds the
# user's working copy, so every `gh stack` call runs in `<run-dir>/stack-clone`: a shallow,
# blob-less clone on `main`, made on first use and removed with the run directory. Pass PR URLs
# rather than branch names to `link`: it pushes a branch argument from this clone, and resolves a
# URL through the API alone.
set -euo pipefail

run="${1:?run dir}"
shift
clone="${run}/stack-clone"

if [[ ! -d "${clone}/.git" ]]; then
  git clone --quiet --depth 1 --filter=blob:none https://github.com/cambra-dev/cambra "${clone}" >&2
fi
cd "${clone}"
exec gh stack "$@"

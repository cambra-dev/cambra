#!/usr/bin/env bash
# Manage the daily-simplify jj workspaces.
#
#   workspace.sh fetch                 jj git fetch; print main@origin
#   workspace.sh add <name>            new workspace on a fresh commit atop main@origin; prints its dir
#   workspace.sh remove <name>         forget + delete; abandons the workspace's unbookmarked commits
#   workspace.sh remove-all            remove every simplify-* workspace jj knows about
#   workspace.sh list                  every simplify-* workspace jj knows about
#   workspace.sh target <name>         the workspace's persistent CARGO_TARGET_DIR
#   workspace.sh paths                 SRCS, REPO, CACHE, VAULT, LOGDIR and TODAY, as assignments
#
# A run has two workspaces, `scout` and `attempt`. Workspace `simplify-<name>` lives at
# <srcs>/cambra-simplify-<name>. <srcs> is the directory holding the cambra workspaces:
# `CAMBRA_SRCS`, by default the parent of the workspace this script is in. The directory name is
# stable across runs so the workspace's cargo target, which lives outside the workspace, builds
# incrementally from the previous day instead of cold. Targets and run directories live under
# `CAMBRA_BUILD_CACHES`, by default <srcs>/cambra_build_caches, in `simplify-cache/`.
#
# Run logs live in the vault, at automation/daily-simplify/outputs/. The vault is `CAMBRA_VAULT`,
# by default <srcs>/vault, and must hold _system/AI-CONTEXT.md. Dates are America/Denver, as for
# the vault's other jobs.
#
# Every jj call runs from the default workspace with --ignore-working-copy, so it never
# snapshots or rewrites the user's working copy in cambra/.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
SRCS="${CAMBRA_SRCS:-$(cd "${HERE}/../../../../.." && pwd)}"
REPO="${SRCS}/cambra"
CACHE="${CAMBRA_BUILD_CACHES:-${SRCS}/cambra_build_caches}/simplify-cache"
TODAY="$(TZ=America/Denver date -I)"
JJ=(jj -R "${REPO}" --ignore-working-copy --config ui.editor=true --config ui.paginate=never)

die() { echo "workspace.sh: $*" >&2; exit 1; }

check_name() {
  [[ "$1" =~ ^(scout|attempt)$ ]] || die "bad workspace name '$1' (want scout or attempt)"
}

find_vault() {
  local dir="${CAMBRA_VAULT:-${SRCS}/vault}"
  [[ -f "${dir}/_system/AI-CONTEXT.md" ]] || die "${dir} is not the vault (no _system/AI-CONTEXT.md)"
  echo "${dir}"
}

ws_name() { echo "simplify-$1"; }
ws_dir() { echo "${SRCS}/cambra-simplify-$1"; }

cmd="${1:-}"
case "${cmd}" in
  fetch)
    "${JJ[@]}" git fetch
    "${JJ[@]}" log -r 'main@origin' --no-graph \
      -T 'commit_id.short(12) ++ "  " ++ committer.timestamp().ago() ++ "  " ++ description.first_line() ++ "\n"'
    ;;
  add)
    short="${2:-}"; check_name "${short}"
    name="$(ws_name "${short}")"; dir="$(ws_dir "${short}")"
    if "${JJ[@]}" workspace list -T 'name ++ "\n"' | grep -qx "${name}"; then
      die "workspace ${name} already exists; run: workspace.sh remove ${short}"
    fi
    [[ -e "${dir}" ]] && die "${dir} exists but jj does not track it; inspect and delete it by hand"
    # `workspace add` cannot check out under --ignore-working-copy: it registers the workspace
    # at an empty root commit and then errors. Tolerate exactly that error, then move the new
    # workspace onto main@origin from inside it, which snapshots only the new (empty) checkout.
    # The root-based commit is empty and undescribed, so `jj new` abandons it.
    if ! err="$("${JJ[@]}" workspace add --name "${name}" "${dir}" 2>&1)"; then
      grep -q 'must be able to update the working copy' <<< "${err}" || die "${err}"
    fi
    jj -R "${dir}" --config ui.editor=true new 'main@origin' >&2
    mkdir -p "${CACHE}/target-${short}"
    echo "${dir}"
    ;;
  remove)
    short="${2:-}"; check_name "${short}"
    name="$(ws_name "${short}")"; dir="$(ws_dir "${short}")"
    if "${JJ[@]}" workspace list -T 'name ++ "\n"' | grep -qx "${name}"; then
      # The workspace's own commits that no bookmark keeps alive: a discarded attempt, or the empty
      # working-copy commit left on top of a pushed one. Abandoned commits stay recoverable by
      # commit id through `jj op log`.
      revset="(main@origin..${name}@) ~ ::bookmarks() ~ ::remote_bookmarks()"
      ids="$("${JJ[@]}" log -r "${revset}" --no-graph -T 'commit_id.short(12) ++ "\n"')"
      "${JJ[@]}" workspace forget "${name}"
      if [[ -n "${ids}" ]]; then
        # shellcheck disable=SC2086 # one id per word
        "${JJ[@]}" abandon ${ids} >&2
        echo "abandoned or already hidden: ${ids//$'\n'/ }" >&2
      fi
    fi
    case "${dir}" in
      "${SRCS}"/cambra-simplify-*) rm -rf "${dir}" ;;
      *) die "refusing to delete ${dir}" ;;
    esac
    echo "removed ${name}" >&2
    ;;
  remove-all)
    names="$("${JJ[@]}" workspace list -T 'name ++ "\n"')"
    for name in $(grep '^simplify-' <<< "${names}" || true); do
      "$0" remove "${name#simplify-}"
    done
    ;;
  list)
    "${JJ[@]}" workspace list | grep '^simplify-' || true
    ;;
  paths)
    vault="$(find_vault)"
    printf 'SRCS=%q\nREPO=%q\nCACHE=%q\nVAULT=%q\nLOGDIR=%q\nTODAY=%q\n' "${SRCS}" "${REPO}" \
      "${CACHE}" "${vault}" "${vault}/automation/daily-simplify/outputs" "${TODAY}"
    ;;
  target)
    short="${2:-}"; check_name "${short}"
    echo "${CACHE}/target-${short}"
    ;;
  *)
    sed -n '2,11p' "$0" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac

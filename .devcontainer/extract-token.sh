#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(dirname "$0")"
UNAME="$(uname)"

if [[ "${UNAME}" == "Darwin" ]]; then
    RAW=$(security find-generic-password -s "Claude Code-credentials" -w 2>/dev/null || true)
    if [[ -z "${RAW}" ]]; then
        echo "WARNING: No Claude Code credentials found in macOS Keychain." >&2
        echo "Run 'claude auth login' on the host before rebuilding the container." >&2
        echo '{}' > "${SCRIPT_DIR}/.claude-token"
    else
        CREDS=$(echo "${RAW}" | python3 -c "import json,sys; d=json.load(sys.stdin); print(json.dumps(d['claudeAiOauth']))" 2>/dev/null || true)
        if [[ -z "${CREDS}" ]]; then
            echo "ERROR: Found Claude Code credentials in Keychain but could not parse them." >&2
            exit 1
        fi
        echo "${CREDS}" > "${SCRIPT_DIR}/.claude-token"
    fi
else
    # On Linux/WSL, Claude Code stores credentials in ~/.claude/.credentials.json
    # which is bind-mounted into the container — no token injection needed.
    echo '{}' > "${SCRIPT_DIR}/.claude-token"
fi

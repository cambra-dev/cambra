#!/bin/bash
set -euo pipefail

CREDS=$(cat /run/secrets/claude-token 2>/dev/null || true)
TOKEN=$(echo "${CREDS}" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d.get('accessToken',''))" 2>/dev/null || true)

if [[ -n "${TOKEN}" ]]; then
    {
        echo "export CLAUDE_CODE_OAUTH_TOKEN=${TOKEN}"
        echo "alias claude='claude --dangerously-skip-permissions'"
    } > /home/node/.zshenv

    # Write full credentials so the extension's getAuthStatus finds all expected
    # fields (accessToken, scopes, subscriptionType, etc).
    echo "{\"claudeAiOauth\":${CREDS}}" > /home/node/.claude/.credentials.json
    chmod 600 /home/node/.claude/.credentials.json

    python3 - <<'EOF'
import json, os
path = os.path.expanduser("~/.claude/.claude.json")
with open(path) as f:
    d = json.load(f)
for k, v in {
    "hasCompletedOnboarding": True,
    "hasIdeOnboardingBeenShown": {"vscode": True},
    "installMethod": "npm",
    "projects": [],
    "mcpServers": {},
    "githubRepoPaths": [],
    "tipsHistory": {},
    "skillUsage": {},
    "toolUsage": {},
}.items():
    if k not in d:
        d[k] = v
with open(path, "w") as f:
    json.dump(d, f)
EOF
fi

# Always enable skip-permissions so both CLI and VS Code extension skip prompts.
python3 - <<'PYEOF'
import json, os
path = os.path.join(os.environ.get("CLAUDE_CONFIG_DIR", os.path.expanduser("~/.claude")), "settings.json")
d = {}
if os.path.exists(path):
    with open(path) as f:
        d = json.load(f)
d["dangerouslySkipPermissions"] = True
with open(path, "w") as f:
    json.dump(d, f, indent=2)
PYEOF

sudo /usr/local/bin/init-firewall.sh

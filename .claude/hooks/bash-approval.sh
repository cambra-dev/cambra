#!/bin/bash
# PreToolUse hook: auto-approve bash commands that contain multiline content
# (heredocs, PR bodies, commit messages) which don't match settings.json patterns.
# See: https://github.com/anthropics/claude-code/issues/11932

INPUT=$(cat)
COMMAND=$(echo "${INPUT}" | jq -r '.tool_input.command')

# gh pr create: heredoc body breaks normal wildcard matching
if echo "${COMMAND}" | grep -q "^gh pr create"; then
  echo '{"permissionDecision": "allow"}'
  exit 0
fi

# gs branch submit: heredoc body breaks normal wildcard matching
if echo "${COMMAND}" | grep -q "^gs branch submit"; then
  echo '{"permissionDecision": "allow"}'
  exit 0
fi

# git commit: heredoc message breaks normal wildcard matching
if echo "${COMMAND}" | grep -q "^git commit"; then
  echo '{"permissionDecision": "allow"}'
  exit 0
fi

# Fall through to normal permission flow
exit 0

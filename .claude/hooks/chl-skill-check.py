#!/usr/bin/env python3
"""Remind an agent changing CHL's surface to update the `cambra-coding` skill.

The skill tells program authors what CHL has: builtins, std modules, syntax, and
each refusal's diagnostic. A change to any of those leaves the skill stale with
no test failing, unless it breaks an example program. CLAUDE.md lists when to
update the skill ("Keeping the cambra-coding skill current"), but that section
is far from the code being edited.

The hook fires on an Edit or Write under a path that defines the surface, and at
most once per session, so iterating on one change does not repeat it. It makes
no judgment about whether the change needs a skill update.
"""

import hashlib
import json
import os
import sys
import tempfile

SURFACE = (
    "chl-parser/src/",
    "stdlib/",
    "src/ccl/lower/",
    "docs/chl-spec.md",
)

REMINDER = (
    "This edit touches CHL's surface ({path}). If it adds, removes or renames a "
    "builtin, std module, library function, keyword or syntax, or changes a "
    "refusal's diagnostic, update `.claude/skills/cambra-coding/` in the same "
    "change: `SKILL.md`, `references/python-habits.md` (rows quote diagnostics "
    "verbatim) and the example programs. The skill is user-facing: it states "
    "the language CHL authors write, so a compiler bug, crash, slow compile or "
    "its workaround stays out of it. See CLAUDE.md, \"Keeping the "
    "cambra-coding skill current\", for what to update and how."
)


def already_reminded(session: str) -> bool:
    """True when this session has already had the reminder.

    Best-effort: any filesystem problem reports "not yet reminded", which repeats
    the notice rather than losing it.
    """
    key = hashlib.sha256(f"chl-skill\0{session}".encode()).hexdigest()[:32]
    marker = os.path.join(tempfile.gettempdir(), "cambra-chl-skill-reminders", key)
    try:
        os.makedirs(os.path.dirname(marker), exist_ok=True)
        fd = os.open(marker, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    except FileExistsError:
        return True
    except OSError:
        return False
    os.close(fd)
    return False


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except (json.JSONDecodeError, ValueError):
        return 0
    path = (payload.get("tool_input") or {}).get("file_path") or ""
    root = os.environ.get("CLAUDE_PROJECT_DIR") or payload.get("cwd") or ""
    rel = os.path.relpath(path, root) if root and os.path.isabs(path) else path
    if not rel.startswith(SURFACE):
        return 0
    if already_reminded(str(payload.get("session_id") or "")):
        return 0
    print(
        json.dumps(
            {
                "hookSpecificOutput": {
                    "hookEventName": "PostToolUse",
                    "additionalContext": REMINDER.format(path=rel),
                }
            }
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

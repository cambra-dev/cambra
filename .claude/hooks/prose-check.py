#!/usr/bin/env python3
"""Point an Edit/Write that added prose at the `spec-prose` skill.

The hook makes no judgment about the prose. Specification style is not
mechanically checkable — a word-level check catches `it turns out` and stays
blind to a paragraph that says one thing three ways — so scoring the text would
report dash counts as if they were quality. The reminder solves the one problem a
hook is actually suited to: the style rule sits in CLAUDE.md, tens of thousands of
tokens behind the sentence being written, while the surrounding prose an agent
imitates is right there.

Two conditions keep it from becoming noise. Prose has to be present (comment
lines for `.rs`, text outside code fences for `.md`) and substantial enough to be
worth a pass, and each file reminds at most once per session.
"""

import hashlib
import json
import os
import re
import sys
import tempfile

MIN_WORDS = 25

REMINDER = (
    "This edit added prose to {path}. Design docs and comments here are "
    "specification prose: the conclusion first, one claim per sentence in the "
    "main clause, no stress italics, no coined vocabulary, and no arguing for "
    "the design. Load the `spec-prose` skill before writing more, and convert "
    "any older-style passage you touch rather than matching it."
)


def markdown_prose(text: str) -> str:
    text = re.sub(r"```.*?```", "", text, flags=re.S)  # fenced code
    text = re.sub(r"^\s*```.*$", "", text, flags=re.M)  # an unclosed fence
    text = re.sub(r"^\s*\|.*$", "", text, flags=re.M)  # tables
    text = re.sub(r"^#+ .*$", "", text, flags=re.M)  # headings
    text = re.sub(r"`[^`]*`", "", text)  # inline code
    return text


def rust_prose(text: str) -> str:
    """Comment content only: a Rust file's prose lives in `///`, `//!`, and `//`."""
    out = []
    for line in text.splitlines():
        s = line.strip()
        for marker in ("///", "//!", "//"):
            if s.startswith(marker):
                out.append(s[len(marker) :].strip())
                break
    return re.sub(r"`[^`]*`", "", "\n".join(out))


def already_reminded(session: str, path: str) -> bool:
    """True when this session has already been reminded about `path`.

    Iterating on one document is several Edits, and an identical reminder on each
    is how a reminder becomes something to skip past. Best-effort: any filesystem
    problem reports "not yet reminded", which repeats the notice rather than
    losing it.
    """
    key = hashlib.sha256(f"{session}\0{path}".encode()).hexdigest()[:32]
    marker = os.path.join(tempfile.gettempdir(), "cambra-prose-reminders", key)
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
    tool_input = payload.get("tool_input") or {}
    path = tool_input.get("file_path") or ""
    added = tool_input.get("new_string") or tool_input.get("content") or ""
    if not added:
        return 0

    if path.endswith(".md"):
        prose = markdown_prose(added)
    elif path.endswith(".rs"):
        prose = rust_prose(added)
    else:
        return 0

    if len(prose.split()) < MIN_WORDS:
        return 0
    if already_reminded(str(payload.get("session_id") or ""), path):
        return 0

    print(
        json.dumps(
            {
                "hookSpecificOutput": {
                    "hookEventName": "PostToolUse",
                    "additionalContext": REMINDER.format(path=path),
                }
            }
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

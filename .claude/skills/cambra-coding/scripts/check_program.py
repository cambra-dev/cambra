#!/usr/bin/env python3
"""Compile CHL programs without running them and print each diagnostic as `file:line:col: message`.

Usage: check_program.py FILE.cambra [FILE.cambra ...]

Exits 0 when every file compiles, 1 when any does not, 2 when the compiler crashes or runs past
`$CAMBRA_CHECK_TIMEOUT` seconds (default 60) on any. The binary is `$CAMBRA_BIN` when set, otherwise
`cargo run --release --quiet --` from the repository root, whose first build exceeds the default
timeout.

A compile check runs the pipeline through operator conversion (`--dump-snapshot`), so it does not
see a runtime panic or a hang. Run the program for those.
"""

import json
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[4]


def compiler_command() -> list[str]:
    binary = os.environ.get("CAMBRA_BIN")
    if binary:
        return [binary]
    return ["cargo", "run", "--release", "--quiet", "--manifest-path", str(REPO_ROOT / "Cargo.toml"), "--"]


def line_col(text: bytes, offset: int) -> tuple[int, int]:
    before = text[:offset]
    line = before.count(b"\n") + 1
    col = len(before) - (before.rfind(b"\n") + 1) + 1
    return line, col


def check(path: str) -> str:
    timeout = float(os.environ.get("CAMBRA_CHECK_TIMEOUT", "60"))
    try:
        proc = subprocess.run(
            [*compiler_command(), "--dump-snapshot", path],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        sys.stderr.write(f"{path}: the compiler ran past {timeout:g}s without finishing\n")
        return "crashed"
    try:
        snapshot = json.loads(proc.stdout)
    except json.JSONDecodeError:
        # The compiler panicked before printing a snapshot: a compiler bug, not a diagnostic.
        sys.stderr.write(f"{path}: the compiler did not produce a snapshot (exit {proc.returncode})\n")
        sys.stderr.write(proc.stderr)
        return "crashed"
    source = snapshot["source"]["text"].encode()
    for diag in snapshot["diagnostics"]:
        span = diag.get("span")
        where = "%d:%d" % line_col(source, span["start"]) if span else "?"
        print(f"{path}:{where}: {diag['severity']}: {diag['message']}")
    if snapshot["meta"]["payloadKind"] == "failed":
        return "rejected"
    print(f"{path}: compiles")
    return "compiles"


def main() -> None:
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    results = [check(p) for p in sys.argv[1:]]
    if "crashed" in results:
        sys.exit(2)
    sys.exit(1 if "rejected" in results else 0)


if __name__ == "__main__":
    main()

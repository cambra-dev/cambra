#!/usr/bin/env python3
"""Run a `cargo test` command, and classify its failures by refinement order.

Usage: order_followup.py <command> [args...]

The command's output passes through and its exit status is this script's. When
`CAMBRA_REFINEMENT_ORDER` is `random:<seed>` and the command fails, each failing test is rerun
twice, with every refinement set built forward and then reversed, and a report says which
order each test fails in. The reruns annotate the failure; they never change the verdict.
"""

import os
import re
import subprocess
import sys

FAILED = re.compile(r"^---- (\S+) stdout ----$")


def run(command, env, echo):
    """Run `command`, and return its exit status and the tests it reports failing."""
    proc = subprocess.Popen(
        command, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True
    )
    failed = []
    for line in proc.stdout:
        if echo:
            sys.stdout.write(line)
        match = FAILED.match(line.rstrip("\n"))
        if match:
            failed.append(match.group(1))
    return proc.wait(), failed


def rerun(command, names, order):
    """The subset of `names` that fail with every refinement set built in `order`."""
    env = dict(os.environ, CAMBRA_REFINEMENT_ORDER=order)
    args = command + (["--exact"] if "--" in command else ["--", "--exact"]) + names
    _, failed = run(args, env, echo=False)
    return set(failed)


def main():
    command = sys.argv[1:]
    setting = os.environ.get("CAMBRA_REFINEMENT_ORDER", "")
    status, failed = run(command, os.environ, echo=True)
    if status == 0 or not setting.startswith("random:") or not failed:
        return status
    names = sorted(set(failed))
    forward = rerun(command, names, "forward")
    reverse = rerun(command, names, "reverse")
    print(f"\nRefinement order follow-up ({setting}): each failing test rerun forward, then reversed.")
    for name in names:
        if name in forward and name in reverse:
            verdict = "fails in both orders"
        elif name in reverse:
            verdict = "fails only reversed (CAMBRA_REFINEMENT_ORDER=reverse reproduces it)"
        elif name in forward:
            verdict = "fails only forward (CAMBRA_REFINEMENT_ORDER=forward reproduces it)"
        else:
            verdict = (
                f"passes in both orders (it needs {setting}'s mix across its compiles, "
                "or it is intermittent)"
            )
        print(f"  {name}: {verdict}")
        if (name in forward) != (name in reverse):
            print(f"::warning::{name} depends on refinement order: {verdict}")
    return status


if __name__ == "__main__":
    sys.exit(main())

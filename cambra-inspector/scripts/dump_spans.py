#!/usr/bin/env python3
"""Dump the program-inspector snapshot's span <-> IR (CCL) mapping.

A frontend-independent view of which IR nodes carry a source span and which do
not, for debugging the provenance substrate. The frontend's source<->tree
linking can only ever reach nodes that the backend gave a span (i.e. nodes that
appear in `spanIndex`); this script shows exactly that set, so a "the inspector
won't link X" report can be isolated to the backend (no span emitted) vs the
frontend (span present but not wired).

For each IR node it prints, indented by tree depth:

    label : type : provenance : span : #nodeId

then a coverage summary (how many nodes map to a source span vs. not, with the
unmapped ones grouped by provenance), and a spanIndex consistency check.

Usage:
    # run the inspector on a .chl program and dump it (manages the server):
    python3 cambra-inspector/scripts/dump_spans.py cambra-inspector/examples/defer_min.chl

    # or dump a snapshot JSON you already have (file arg or stdin):
    python3 cambra-inspector/scripts/dump_spans.py snapshot.json
    curl -s localhost:8080/api/snapshot | python3 cambra-inspector/scripts/dump_spans.py
"""

import json
import socket
import subprocess
import sys
import time
import urllib.request
from collections import Counter


def free_port() -> int:
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


def fetch_via_server(chl_path: str) -> dict:
    """Run `cambra-inspector <chl_path>` on an ephemeral port, fetch its
    snapshot, then shut it down. Allows for a cold `cargo` build."""
    port = free_port()
    proc = subprocess.Popen(
        ["cargo", "run", "-q", "-p", "cambra-inspector", "--", chl_path, "--port", str(port)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = f"http://localhost:{port}/api/snapshot"
    deadline = time.time() + 180  # generous: first run may compile the crate
    try:
        while True:
            try:
                with urllib.request.urlopen(url, timeout=2) as r:
                    return json.load(r)
            except Exception:
                if proc.poll() is not None:
                    raise SystemExit(
                        "inspector server exited before answering "
                        "(compile/run error — run the program directly to see it)"
                    )
                if time.time() > deadline:
                    raise SystemExit(f"server did not answer on {url} within timeout")
                time.sleep(0.3)
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except Exception:
            proc.kill()


def load_snapshot(arg: str | None) -> dict:
    if arg is None:
        return json.load(sys.stdin)
    if arg.endswith(".json"):
        with open(arg) as f:
            return json.load(f)
    return fetch_via_server(arg)


def span_str(s: dict | None) -> str:
    return f"{s['start']}..{s['end']}" if s else "—"  # em dash for "no span"


def node_type(n: dict) -> str:
    # The type is a first-class `type` field; fall back to the legacy positional
    # `annotations[0]` ("`: T`") for snapshots produced before that field landed.
    t = n.get("type")
    if t:
        return t
    anns = n.get("annotations") or []
    return anns[0][2:] if anns and anns[0].startswith(": ") else ""


def main() -> None:
    arg = sys.argv[1] if len(sys.argv) > 1 else None
    snap = load_snapshot(arg)

    meta = snap.get("meta", {})
    src_name = snap.get("source", {}).get("name", "?")
    print(
        f"program: {src_name}  kind={meta.get('snapshotKind')}  "
        f"diagnostics={len(snap.get('diagnostics', []))}"
    )

    ir = snap.get("ir")
    if ir is None:
        print("  (degraded snapshot — no IR; compile failed)")
        for d in snap.get("diagnostics", []):
            print(f"  {d['severity']} [{d['stage']}] {d['message']}  {span_str(d.get('span'))}")
        return

    mapped: list[dict] = []
    unmapped: list[dict] = []

    def walk(n: dict, depth: int) -> None:
        s = n.get("span")
        (mapped if s else unmapped).append(n)
        ty = node_type(n)
        tystr = f" : {ty}" if ty else ""
        print(f"{'  ' * depth}{n['label']}{tystr} : {n.get('provenance')} : {span_str(s)}  #{n['nodeId']}")
        for e in n.get("children", []):
            walk(e["node"], depth + 1)

    print("\nIR tree (label : type : provenance : span : #id):")
    walk(ir, 0)

    total = len(mapped) + len(unmapped)
    print(f"\ncoverage: {len(mapped)}/{total} IR nodes carry a source span; {len(unmapped)} do not")
    if unmapped:
        by_prov = Counter(str(n.get("provenance")) for n in unmapped)
        print("unmapped nodes by provenance:")
        for prov, cnt in sorted(by_prov.items()):
            labels = sorted({n["label"] for n in unmapped if str(n.get("provenance")) == prov})
            print(f"  {prov}: {cnt}  ({', '.join(labels)})")

    # spanIndex consistency: every node the tree gives a span to should be in
    # spanIndex (that array is what the frontend actually queries).
    idx = {(e["span"]["start"], e["span"]["end"], e["nodeId"]) for e in snap.get("spanIndex", [])}
    missing = [n for n in mapped if (n["span"]["start"], n["span"]["end"], n["nodeId"]) not in idx]
    if missing:
        print(f"\nWARNING: {len(missing)} spanned node(s) absent from spanIndex:")
        for n in missing:
            print(f"  #{n['nodeId']} {n['label']} {span_str(n['span'])}")
    else:
        print("\nspanIndex: consistent (every spanned IR node is indexed)")


if __name__ == "__main__":
    main()

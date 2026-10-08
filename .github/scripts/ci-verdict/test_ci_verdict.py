#!/usr/bin/env python3
"""Unit tests for the CI verdict reader.

The cases are the run pairs `ci.yml` left on #306's head SHAs, where a push
that force-pushed the PR's base and moved its head started two runs at one SHA.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from ci_verdict import Run, verdict  # noqa: E402


def run(id: int, status: str = "completed", conclusion: str = "") -> Run:
    return Run(id, status, conclusion, f"https://example/runs/{id}")


class Verdict(unittest.TestCase):
    def test_no_runs_is_none(self) -> None:
        self.assertEqual(verdict([]).state, "none")

    def test_cancelled_higher_id_is_discounted(self) -> None:
        # #306 at 1461a21b: the two runs were created in the same second, and
        # the concurrency group cancelled the one with the HIGHER id. Reading
        # the newest run reported a cancellation the SHA never had.
        v = verdict(
            [run(37832813191, conclusion="cancelled"), run(37832813101, conclusion="success")]
        )
        self.assertEqual((v.state, v.run.id), ("pass", 37832813101))

    def test_cancelled_lower_id_is_discounted(self) -> None:
        # #306 at 75f8b0c8: the same pair the other way round.
        v = verdict(
            [run(37710202000, conclusion="success"), run(37710199894, conclusion="cancelled")]
        )
        self.assertEqual(v.state, "pass")

    def test_pending_while_the_survivor_runs(self) -> None:
        # The cancelled run completes within seconds, its `check` job reporting
        # FAILURE; the survivor is still running. That is not a verdict yet.
        v = verdict([run(2, conclusion="cancelled"), run(1, status="in_progress")])
        self.assertEqual(v.state, "pending")

    def test_failed_survivor_fails(self) -> None:
        v = verdict([run(2, conclusion="cancelled"), run(1, conclusion="failure")])
        self.assertEqual((v.state, v.run.id), ("fail", 1))

    def test_all_cancelled_is_not_a_pass(self) -> None:
        # Nothing checked the SHA, so the verdict names the run to re-run.
        v = verdict([run(1, conclusion="cancelled"), run(2, conclusion="cancelled")])
        self.assertEqual((v.state, v.run.id), ("cancelled", 2))

    def test_rerun_attempt_in_flight_is_pending(self) -> None:
        # A re-run reuses the run id; the run reports its latest attempt.
        v = verdict([run(1, conclusion="success"), run(2, status="queued")])
        self.assertEqual(v.state, "pending")

    def test_other_conclusions_fail(self) -> None:
        for conclusion in ("timed_out", "startup_failure", "action_required", "neutral"):
            with self.subTest(conclusion=conclusion):
                self.assertEqual(verdict([run(1, conclusion=conclusion)]).state, "fail")


if __name__ == "__main__":
    unittest.main()

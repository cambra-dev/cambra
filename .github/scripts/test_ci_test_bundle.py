import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location(
    "ci_test_bundle", Path(__file__).with_name("ci-test-bundle.py")
)
bundle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bundle)


class TestBundle(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        previous = Path.cwd()
        self.addCleanup(os.chdir, previous)
        os.chdir(directory.name)
        Path("target").mkdir()
        self.root = Path.cwd()

    def artifact(self, executable, directory=".", is_test=True):
        return {
            "reason": "compiler-artifact",
            "executable": str(self.root / executable),
            "manifest_path": str(self.root / directory / "Cargo.toml"),
            "profile": {"test": is_test},
        }

    def build(self, order, records, returncode=0):
        with (
            patch.object(bundle.subprocess, "Popen") as popen,
            patch.object(bundle.subprocess, "check_output") as output,
            patch.object(bundle.subprocess, "run") as tar,
            patch("sys.stderr", new_callable=io.StringIO),
        ):
            cargo = popen.return_value.__enter__.return_value
            cargo.stderr = io.StringIO(order)
            cargo.wait.return_value = returncode
            cargo.returncode = returncode
            output.return_value = "\n".join(json.dumps(record) for record in records)
            bundle.build_bundle("tests.tar.zst")
            return tar.call_args

    def test_preserves_cargo_order_and_package_directories(self):
        tar = self.build(
            "  Executable tests/first.rs (target/debug/first)\n"
            "  Executable tests/second.rs (target/debug/second)\n",
            [
                self.artifact("target/debug/second", "chl-parser"),
                self.artifact("target/debug/cambra", is_test=False),
                self.artifact("target/debug/first"),
            ],
        )
        self.assertEqual(
            json.loads(bundle.MANIFEST.read_text()),
            [["target/debug/first", "."], ["target/debug/second", "chl-parser"]],
        )
        self.assertEqual(
            set(tar.kwargs["input"].rstrip("\0").split("\0")),
            {
                "target/debug/first", "target/debug/second", "target/debug/cambra",
                str(bundle.MANIFEST),
            },
        )

    def test_rejects_missing_test_binary(self):
        with self.assertRaisesRegex(SystemExit, "executable lists differ"):
            self.build("", [self.artifact("target/debug/first")])

    def test_rejects_an_empty_suite(self):
        with self.assertRaisesRegex(SystemExit, "executable lists differ"):
            self.build("", [self.artifact("target/debug/cambra", is_test=False)])

    def test_reports_cargo_failure(self):
        with self.assertRaises(SystemExit) as failure:
            self.build("", [], returncode=101)
        self.assertEqual(failure.exception.code, 101)

    def test_runs_every_binary_after_a_failure(self):
        bundle.MANIFEST.write_text(json.dumps(
            [["target/debug/first", "."], ["target/debug/second", "chl-parser"]]
        ))
        with (
            patch.object(bundle.subprocess, "run") as run,
            patch("sys.stdout", new_callable=io.StringIO),
        ):
            run.side_effect = [
                subprocess.CompletedProcess([], 1), subprocess.CompletedProcess([], 0)
            ]
            with self.assertRaisesRegex(SystemExit, "Failed test binaries: target/debug/first"):
                bundle.run_tests()
        self.assertEqual(run.call_count, 2)
        self.assertEqual(run.call_args.args[0], [self.root / "target/debug/second", "--quiet"])
        self.assertEqual(run.call_args.kwargs["cwd"], self.root / "chl-parser")

    def test_rejects_an_empty_bundle(self):
        bundle.MANIFEST.write_text("[]")
        with self.assertRaisesRegex(SystemExit, "contains no suites"):
            bundle.run_tests()


if __name__ == "__main__":
    unittest.main()

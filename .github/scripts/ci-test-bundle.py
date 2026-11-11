import json
from pathlib import Path
import subprocess
import sys


MANIFEST = Path("target/ci-test-bundle.json")


def bundle_files(cargo_output, cargo_order):
    root = Path.cwd()
    files = {str(MANIFEST)}
    suites = {}
    with cargo_output.open() as records:
        for line in records:
            record = json.loads(line)
            if record["reason"] != "compiler-artifact" or not record["executable"]:
                continue
            executable = Path(record["executable"]).relative_to(root)
            files.add(str(executable))
            if record["profile"]["test"]:
                directory = Path(record["manifest_path"]).parent.relative_to(root)
                suites[str(executable)] = str(directory)
    order = []
    for line in cargo_order.read_text().splitlines():
        if line.lstrip().startswith("Executable "):
            executable = line.rsplit(" (", 1)[1].removesuffix(")")
            order.append(str(Path(executable).absolute().relative_to(root)))
    if not suites or len(order) != len(suites) or set(order) != suites.keys():
        raise SystemExit("Cargo's build and test executable lists differ")
    MANIFEST.write_text(json.dumps([(path, suites[path]) for path in order]) + "\n")
    print("\n".join(sorted(files)))


def run_tests():
    root = Path.cwd()
    suites = json.loads(MANIFEST.read_text())
    if not suites:
        raise SystemExit("Test bundle contains no suites")
    failed = []
    for executable, directory in suites:
        print(f"Running {executable} from {directory}", flush=True)
        result = subprocess.run([root / executable, "--quiet"], cwd=root / directory)
        if result.returncode:
            failed.append(executable)
    if failed:
        raise SystemExit("Failed test binaries: " + ", ".join(failed))


if __name__ == "__main__":
    match sys.argv[1:]:
        case ["bundle", cargo_output, cargo_order]:
            bundle_files(Path(cargo_output), Path(cargo_order))
        case ["run"]:
            run_tests()
        case _:
            raise SystemExit("Usage: ci-test-bundle.py bundle <cargo-output> <cargo-order> | run")

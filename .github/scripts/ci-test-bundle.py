import json
from pathlib import Path
import subprocess
import sys


MANIFEST = Path("target/ci-test-bundle.json")
PACKAGES = ("cambra", "chl-parser", "chl-interp", "cambra-lsp")


def cargo_test(*flags):
    command = ["cargo"]
    for package in PACKAGES:
        command.extend(("--config", f"profile.test.package.{package}.opt-level=1"))
    return [*command, "test", "--workspace", *flags]


def build_bundle(archive):
    root = Path.cwd()
    order = []
    # Cargo lists executables in test order. Its JSON messages supply the package directories.
    with subprocess.Popen(
        cargo_test("--no-run", "--color=never"), stderr=subprocess.PIPE, text=True
    ) as cargo:
        for line in cargo.stderr:
            print(line, end="", file=sys.stderr)
            if line.lstrip().startswith("Executable "):
                executable = line.rstrip().rsplit(" (", 1)[1].removesuffix(")")
                order.append(str(Path(executable).absolute().relative_to(root)))
        if cargo.wait():
            raise SystemExit(cargo.returncode)

    records = subprocess.check_output(
        cargo_test("--no-run", "--message-format=json"), text=True
    )
    files = {str(MANIFEST)}
    suites = {}
    for line in records.splitlines():
        record = json.loads(line)
        if record["reason"] != "compiler-artifact" or not record["executable"]:
            continue
        executable = str(Path(record["executable"]).relative_to(root))
        files.add(executable)
        if record["profile"]["test"]:
            directory = Path(record["manifest_path"]).parent.relative_to(root)
            suites[executable] = str(directory)
    if not suites or len(order) != len(suites) or set(order) != suites.keys():
        raise SystemExit("Cargo's build and test executable lists differ")

    MANIFEST.write_text(json.dumps([(path, suites[path]) for path in order]) + "\n")
    subprocess.run(
        ["tar", "--use-compress-program=zstd -T0 -1", "-cf", archive, "--null", "-T", "-"],
        input="\0".join(sorted(files)) + "\0",
        text=True,
        check=True,
    )


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
        case ["build", archive]:
            build_bundle(archive)
        case ["doctest"]:
            subprocess.run(cargo_test("--doc", "-q", "--no-fail-fast"), check=True)
        case ["run"]:
            run_tests()
        case _:
            raise SystemExit("Usage: ci-test-bundle.py build <archive> | doctest | run")

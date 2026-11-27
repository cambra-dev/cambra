// The tests' payloads: every gallery program's `--dump-snapshot` output, dumped
// fresh by the Rust suite's `write_gallery_snapshots` before any test runs, so the
// frontend is tested against the wire the backend produces now rather than a
// committed copy of it. `helpers.ts`'s `dumped` reads them.
//
// The dump runs through `cargo test`, which reuses the suite's own build. CI's
// job sets `CAMBRA_SNAPSHOT_PROFILE` to the profile its suite was built with, so
// nothing compiles again; locally the default test profile is the one
// `cargo test` builds.

import { execFileSync } from "node:child_process";
import { rmSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

import type { TestProject } from "vitest/node";

declare module "vitest" {
  export interface ProvidedContext {
    /** The directory the gallery programs' payloads were dumped to. */
    snapshots: string;
  }
}

const REPO = fileURLToPath(new URL("../../..", import.meta.url));

export default function setup(project: TestProject): void {
  const dir = join(REPO, "target", "inspector-snapshots");
  const profile = process.env.CAMBRA_SNAPSHOT_PROFILE;
  // `write_gallery_snapshots` is the only code that clears the directory, and
  // `cargo test` exits 0 when the filter below matches no test. Clearing it
  // here makes such a run fail on the missing directory rather than read the
  // previous run's dumps.
  rmSync(dir, { recursive: true, force: true });
  execFileSync(
    "cargo",
    [
      "test",
      // The package set the suite is built with: a narrower one can resolve
      // features differently and rebuild the library.
      ...["-p", "cambra", "-p", "chl-parser", "-p", "chl-interp", "-p", "cambra-lsp"],
      "--lib",
      "-q",
      ...(profile === undefined ? [] : ["--profile", profile]),
      "--",
      "--ignored",
      "--exact",
      "it::inspector_wire::write_gallery_snapshots",
    ],
    { cwd: REPO, env: { ...process.env, CAMBRA_SNAPSHOT_DIR: dir }, stdio: "inherit" },
  );
  project.provide("snapshots", dir);
}

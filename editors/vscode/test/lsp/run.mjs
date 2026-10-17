// Checks the language server through VS Code's client and this extension.
//
//   node editors/vscode/test/lsp/run.mjs CAMBRA
//
// CAMBRA is the `cambra` binary the extension runs as `CAMBRA --lsp`. This
// downloads VS Code into `editors/vscode/.vscode-test/` on first use, or runs
// the one at `$CAMBRA_VSCODE`, and starts it on a fresh profile with no other
// extension installed. `suite.js` runs inside it and makes the checks
// (editors/README.md, "Language server checks"). `$CAMBRA_VSCODE_VERSION`
// picks the downloaded version; `./ci.sh vscode` pins it, and with it unset
// this downloads the latest stable release.
// On Linux VS Code runs with no window, through Chromium's headless Ozone
// platform, so no display or Xvfb is needed; `CAMBRA_VSCODE_SHOW=1` opens the
// window instead, to watch the check.

import { runTests } from "@vscode/test-electron";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const cambra = process.argv[2];
if (!cambra) {
  process.stderr.write("usage: run.mjs CAMBRA\n");
  process.exit(2);
}

const here = dirname(fileURLToPath(import.meta.url));
const extension = resolve(here, "../..");
const scratch = mkdtempSync(join(tmpdir(), "cambra-vscode-"));
const user = join(scratch, "user");
mkdirSync(join(user, "User"), { recursive: true });
writeFileSync(
  join(user, "User", "settings.json"),
  JSON.stringify({
    "cambra.server.path": resolve(cambra),
    // The check reads diagnostics, so nothing may steal focus or prompt.
    "workbench.startupEditor": "none",
    "security.workspace.trust.enabled": false,
    "update.mode": "none",
    "telemetry.telemetryLevel": "off",
  }),
);
const workspace = join(scratch, "workspace");
mkdirSync(workspace);
const file = join(workspace, "check.cambra");
writeFileSync(file, ['x = f(1]', 'y = "😀" $', "def g(a):", "    a", ""].join("\n"));

// Any process a VS Code extension starts inherits this variable, and with it
// set the VS Code binary runs as plain Node instead of opening the workbench.
delete process.env.ELECTRON_RUN_AS_NODE;

let status = 1;
try {
  status = await runTests({
    vscodeExecutablePath: process.env.CAMBRA_VSCODE,
    version: process.env.CAMBRA_VSCODE_VERSION,
    cachePath: join(extension, ".vscode-test"),
    extensionDevelopmentPath: extension,
    extensionTestsPath: join(here, "suite.js"),
    extensionTestsEnv: { CAMBRA_CHECK_FILE: file },
    launchArgs: [
      workspace,
      "--user-data-dir",
      user,
      "--extensions-dir",
      join(scratch, "extensions"),
      "--disable-workspace-trust",
      ...(process.platform === "linux" && !process.env.CAMBRA_VSCODE_SHOW
        ? ["--ozone-platform=headless"]
        : []),
    ],
  });
} catch (error) {
  process.stderr.write(`check-lsp: VS Code exited with ${error}\n`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
process.exit(status);

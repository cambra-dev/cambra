// @ts-check
// The VS Code client for the language server `cambra --lsp`
// (`cambra-lsp/design-cambra-lsp.md`, "VS Code client").

const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

/** @type {LanguageClient | undefined} */
let client;

/** @param {vscode.ExtensionContext} context */
async function activate(context) {
  context.subscriptions.push(
    vscode.commands.registerCommand("cambra.restartServer", restart),
    vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration("cambra.server.path")) {
        return restart();
      }
    }),
  );
  await start();
}

async function start() {
  const command = vscode.workspace.getConfiguration("cambra").get("server.path", "cambra");
  const server = { command, args: ["--lsp"] };
  client = new LanguageClient(
    // The id names the `cambra.trace.server` setting the client reads.
    "cambra",
    "Cambra",
    { run: server, debug: server },
    {
      // A language-only selector would also attach to the `git:` documents
      // of diff views.
      documentSelector: [
        { scheme: "file", language: "cambra" },
        { scheme: "untitled", language: "cambra" },
      ],
    },
  );
  try {
    await client.start();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    vscode.window.showErrorMessage(
      `Cambra: could not start the language server \`${command} --lsp\` (${message}). ` +
        "Set `cambra.server.path` to a `cambra` binary, or put one on PATH with " +
        "`cargo install --path .` from the repository root.",
    );
  }
}

async function restart() {
  await stop();
  await start();
}

async function stop() {
  const running = client;
  client = undefined;
  if (running?.isRunning()) {
    await running.stop();
  }
}

module.exports = { activate, deactivate: stop };

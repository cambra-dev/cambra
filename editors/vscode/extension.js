// @ts-check
// The VS Code client for the language server `cambra --lsp`
// (`cambra-lsp/design-cambra-lsp.md`, "VS Code client").

const os = require("os");
const vscode = require("vscode");
const { LanguageClient, State } = require("vscode-languageclient/node");

/** @type {LanguageClient | undefined} */
let client;
// Starts and stops run one at a time on `queue`; `generation` lets a restart
// skip when a later one has been queued behind it.
let queue = Promise.resolve();
let generation = 0;
let deactivated = false;
/** @type {NodeJS.Timeout | undefined} */
let debounce;

/** @param {vscode.ExtensionContext} context */
async function activate(context) {
  context.subscriptions.push(
    vscode.commands.registerCommand("cambra.restartServer", restart),
    vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration("cambra.server.path")) {
        // The Settings UI writes the setting on every keystroke.
        clearTimeout(debounce);
        debounce = setTimeout(restart, 500);
      }
    }),
    // An untrusted workspace's server runs from the home directory (see
    // `start`); trusting the workspace moves it to the workspace folder.
    vscode.workspace.onDidGrantWorkspaceTrust(restart),
    { dispose: () => clearTimeout(debounce) },
  );
  await restart();
}

function restart() {
  const ticket = ++generation;
  queue = queue
    .then(async () => {
      if (ticket !== generation || deactivated) return;
      await stop();
      await start();
    })
    .catch(report);
  return queue;
}

async function start() {
  const command = vscode.workspace.getConfiguration("cambra").get("server.path", "cambra");
  const server = {
    command,
    args: ["--lsp"],
    // In Restricted Mode VS Code drops the workspace's `cambra.server.path`,
    // but on Windows a bare name is looked up in the working directory before
    // `PATH`, and the client's default working directory is the workspace
    // folder.
    options: vscode.workspace.isTrusted ? undefined : { cwd: os.homedir() },
  };
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

async function stop() {
  const old = client;
  client = undefined;
  if (old === undefined) return;
  // Every start the queue runs has finished before its next stop, but the
  // client restarts itself after a crash, and `stop` throws during a start.
  if (old.state === State.Starting) {
    await old.start().catch(() => {});
  }
  // A client that failed to start has no connection to shut down.
  if (!old.isRunning()) return;
  try {
    // `dispose` also keeps the client from restarting itself afterwards.
    await old.dispose();
  } catch (error) {
    // A shutdown that fails or times out still terminates the server.
    report(error);
  }
}

/** @param {unknown} error */
function report(error) {
  console.error("Cambra: language client lifecycle failed", error);
}

function deactivate() {
  deactivated = true;
  clearTimeout(debounce);
  queue = queue.then(stop).catch(report);
  return queue;
}

module.exports = { activate, deactivate };

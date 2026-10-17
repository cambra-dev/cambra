// @ts-check
// The checks `run.mjs` runs inside VS Code. They mirror
// `editors/nvim/test/check_lsp.lua` on the same file, with columns in UTF-16
// code units, the only encoding VS Code's client accepts: the client starts
// and the server answers in UTF-16; both diagnostics arrive at their UTF-16
// columns, the mismatched bracket with its related link; the outline lists
// the file's bindings and function; the folds include the function body; and
// two edits clear the diagnostics one at a time.

const vscode = require("vscode");

const TIMEOUT = 10000;

/**
 * Polls `ready` until it returns true or the timeout passes.
 * @param {() => boolean} ready
 */
async function waitFor(ready) {
  const deadline = Date.now() + TIMEOUT;
  while (!ready() && Date.now() < deadline) {
    await new Promise((resolve) => setTimeout(resolve, 50));
  }
  return ready();
}

/** @param {vscode.Range} r */
function show(r) {
  return `${r.start.line}:${r.start.character}-${r.end.line}:${r.end.character}`;
}

async function run() {
  /** @type {string[]} */
  const failures = [];
  let checked = 0;
  /**
   * @param {boolean} ok
   * @param {string} what
   */
  const check = (ok, what) => {
    checked += 1;
    if (!ok) failures.push(what);
    return ok;
  };

  const file = process.env.CAMBRA_CHECK_FILE;
  if (!file) throw new Error("CAMBRA_CHECK_FILE is not set");
  const uri = vscode.Uri.file(file);
  const doc = await vscode.workspace.openTextDocument(uri);
  await vscode.window.showTextDocument(doc);
  check(doc.languageId === "cambra", `the file opened as ${doc.languageId}, not cambra`);

  const diagnostics = () =>
    vscode.languages
      .getDiagnostics(uri)
      .slice()
      .sort((a, b) => a.range.start.compareTo(b.range.start));
  const shown = () => JSON.stringify(diagnostics().map((d) => `${show(d.range)} ${d.message}`));
  /**
   * @param {number} count
   * @param {string} what
   */
  const waitDiagnostics = async (count, what) =>
    check(await waitFor(() => diagnostics().length === count), `${what}: ${shown()}`);

  const extension = vscode.extensions.getExtension("cambra-dev.cambra");
  check(
    await waitFor(() => extension?.isActive === true),
    "the extension did not activate on opening a .cambra file",
  );

  if (await waitDiagnostics(2, "expected two diagnostics on opening")) {
    const [bracket, dollar] = diagnostics();
    check(
      show(bracket.range) === "0:7-0:8" && bracket.message === "`]` does not match `(`",
      `the mismatched \`]\` is not reported at 0:7-0:8: ${shown()}`,
    );
    const related = bracket.relatedInformation?.[0];
    check(
      related !== undefined &&
        show(related.location.range) === "0:5-0:6" &&
        related.message === "this bracket is never closed",
      `the mismatched \`]\` does not link its \`(\`: ${JSON.stringify(bracket.relatedInformation)}`,
    );
    // `😀` is two UTF-16 units, so the `$` after it is at column 9, where a
    // server counting bytes would put it at 11.
    check(show(dollar.range) === "1:9-1:10", `the \`$\` after \`😀\` is not at 1:9-1:10: ${shown()}`);
  }

  /** @type {vscode.DocumentSymbol[] | undefined} */
  const symbols = await vscode.commands.executeCommand("vscode.executeDocumentSymbolProvider", uri);
  const names = (symbols ?? []).map((s) => s.name);
  check(JSON.stringify(names) === '["x","g"]', `the outline is not [x, g]: ${JSON.stringify(names)}`);
  const g = (symbols ?? []).find((s) => s.name === "g");
  check(
    g !== undefined && show(g.selectionRange) === "2:4-2:5" && show(g.range) === "2:0-3:5",
    `g's ranges are not 2:0-3:5 (name 2:4-2:5): ${g && `${show(g.range)} (name ${show(g.selectionRange)})`}`,
  );

  /** @type {vscode.FoldingRange[] | undefined} */
  const folds = await vscode.commands.executeCommand("vscode.executeFoldingRangeProvider", uri);
  check(
    (folds ?? []).some((f) => f.start === 2 && f.end === 3),
    `the function body does not fold over lines 2-3: ${JSON.stringify(folds)}`,
  );

  // Replace `]` with `)`, then delete ` $` after the `😀`, in UTF-16 columns.
  const editor = vscode.window.activeTextEditor;
  if (check(editor?.document === doc, "the file is not the active editor") && editor) {
    await editor.edit((e) => e.replace(new vscode.Range(0, 7, 0, 8), ")"));
    await waitDiagnostics(1, "fixing the bracket should leave one diagnostic");
    await editor.edit((e) => e.delete(new vscode.Range(1, 8, 1, 10)));
    check(doc.lineAt(1).text === 'y = "😀"', `the edit left line 2 as ${JSON.stringify(doc.lineAt(1).text)}`);
    await waitDiagnostics(0, "deleting the `$` should leave no diagnostic");
  }

  for (const failure of failures) console.error(failure);
  if (failures.length > 0) {
    throw new Error(`check-lsp: ${failures.length} of ${checked} checks fail`);
  }
  console.log(`check-lsp: all ${checked} checks pass`);
}

module.exports = { run };

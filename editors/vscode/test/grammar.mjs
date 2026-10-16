// Loads the TextMate grammar under vscode-textmate, as VS Code does, for the
// checkers in this directory.

import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
export const vsctm = require("vscode-textmate");
const oniguruma = require("vscode-oniguruma");

const GRAMMAR = fileURLToPath(new URL("../syntaxes/cambra.tmLanguage.json", import.meta.url));
export const ROOT_SCOPE = "source.cambra";

export async function loadGrammar() {
  await oniguruma.loadWASM(readFileSync(require.resolve("vscode-oniguruma/release/onig.wasm")).buffer);
  const registry = new vsctm.Registry({
    onigLib: Promise.resolve({
      createOnigScanner: (patterns) => new oniguruma.OnigScanner(patterns),
      createOnigString: (s) => new oniguruma.OnigString(s),
    }),
    loadGrammar: async (scopeName) =>
      scopeName === ROOT_SCOPE ? vsctm.parseRawGrammar(readFileSync(GRAMMAR, "utf8"), GRAMMAR) : null,
  });
  return registry.loadGrammar(ROOT_SCOPE);
}

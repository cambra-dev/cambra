// Checks `language-configuration.json`'s indentation against the shared
// indentation cases.
//
//   node editors/vscode/test/check-indent.mjs CASES
//
// CASES is `editors/indent-cases.json`. For each case this computes the indent
// VS Code gives the new line when Enter is pressed at the end of the case's
// last line, with `editor.autoIndent` at its default `full`, `tabSize` 4 and
// `insertSpaces` on. A case whose `expected_failures` names `vscode` must get a
// different indent. editors/README.md, "Indentation tests", lists the VS Code
// behaviour this models and what it leaves out.

import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { loadGrammar, vsctm } from "./grammar.mjs";

const casesPath = process.argv[2];
if (!casesPath) {
  console.error("usage: check-indent.mjs CASES");
  process.exit(2);
}

const CONFIG = fileURLToPath(new URL("../language-configuration.json", import.meta.url));
const config = JSON.parse(readFileSync(CONFIG, "utf8"));
const TAB_SIZE = 4;

const escape = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
const onEnterRules = config.onEnterRules.map((rule) => ({
  beforeText: new RegExp(rule.beforeText),
  afterText: rule.afterText === undefined ? null : new RegExp(rule.afterText),
  previousLineText: rule.previousLineText === undefined ? null : new RegExp(rule.previousLineText),
  action: rule.action,
}));
const increaseIndent = new RegExp(config.indentationRules.increaseIndentPattern);
const decreaseIndent = new RegExp(config.indentationRules.decreaseIndentPattern);
// `onEnter.ts`, `_createOpenBracketRegExp`: every configured open bracket
// starts with a non-word character, so no `\b` is prepended.
const openBracketAtEnd = config.brackets.map(([open]) => new RegExp(`${escape(open)}\\s*$`));
const anyBracket = new RegExp(config.brackets.flat().map(escape).join("|"), "g");

const grammar = await loadGrammar();

// `StandardTokenType` in a token's metadata: 1 comment, 2 string, 3 regex.
const tokenType = (metadata) => (metadata & 0x300) >>> 8;

// Each line with the configured brackets removed from its comment, string and
// regex tokens, as `IndentationLineProcessor.getProcessedTokens` removes them
// before any rule reads the line.
function processedLines(lines) {
  let ruleStack = vsctm.INITIAL;
  return lines.map((line) => {
    const result = grammar.tokenizeLine2(line, ruleStack);
    ruleStack = result.ruleStack;
    const tokens = result.tokens;
    let out = "";
    for (let i = 0; i < tokens.length; i += 2) {
      const end = i + 2 < tokens.length ? tokens[i + 2] : line.length;
      const text = line.slice(tokens[i], end);
      out += tokenType(tokens[i + 1]) === 0 ? text : text.replace(anyBracket, "");
    }
    return out;
  });
}

const leadingWhitespace = (line) => line.match(/^\s*/)[0];

// The visible width of an indentation string, a tab reaching the next stop.
function width(indentation) {
  let column = 0;
  for (const c of indentation) column = c === "\t" ? column + TAB_SIZE - (column % TAB_SIZE) : column + 1;
  return column;
}

const shift = (w) => w + TAB_SIZE - (w % TAB_SIZE);
const unshift = (w) => Math.max(0, Math.ceil(w / TAB_SIZE) * TAB_SIZE - TAB_SIZE);

// The indent of the line Enter opens after the last of `lines`, with the
// cursor at the end of that line and nothing after it.
function enter(lines) {
  const processed = processedLines(lines);
  const n = lines.length;
  const beforeText = processed[n - 1];
  const previousLineText = n > 1 ? processed[n - 2] : "";
  const afterText = "";
  const indentation = leadingWhitespace(lines[n - 1]);

  // `getEnterAction`: the first `onEnterRules` entry whose patterns all match,
  // then the open-bracket rule. The indent-outdent rule needs text after the
  // cursor, and there is none.
  let action = null;
  for (const rule of onEnterRules) {
    if (
      rule.beforeText.test(beforeText) &&
      (rule.afterText === null || rule.afterText.test(afterText)) &&
      (rule.previousLineText === null || rule.previousLineText.test(previousLineText))
    ) {
      action = rule.action;
      break;
    }
  }
  if (action === null && beforeText.length > 0 && openBracketAtEnd.some((re) => re.test(beforeText))) {
    action = { indent: "indent" };
  }
  if (action !== null) {
    const append = action.appendText ?? "";
    switch (action.indent) {
      case "none":
        return width(indentation + append);
      case "indent":
        return width(`${indentation}\t${append}`);
      case "outdent":
        return unshift(width(indentation)) + width(append);
      default:
        throw new Error(`indent action \`${action.indent}\` is not modelled`);
    }
  }

  // `getIndentForEnter`: the last non-blank line's indent, one level more when
  // it matches `increaseIndentPattern`, one less when the text after the cursor
  // matches `decreaseIndentPattern`.
  let last = n - 1;
  while (last > 0 && lines[last].trim() === "") last--;
  let indent = width(leadingWhitespace(lines[last]));
  if (increaseIndent.test(processed[last])) indent = shift(indent);
  if (decreaseIndent.test(afterText)) indent = unshift(indent);
  return indent;
}

const { cases } = JSON.parse(readFileSync(casesPath, "utf8"));
const failures = [];
for (const c of cases) {
  const got = enter(c.lines);
  const known = c.expected_failures?.vscode;
  if (known && got === c.indent) {
    failures.push(`${c.name}: now indents ${got} as expected; remove its \`vscode\` expected failure`);
  } else if (!known && got !== c.indent) {
    failures.push(`${c.name}: indents ${got}, expected ${c.indent}`);
  }
}

for (const f of failures) console.error(f);
if (cases.length === 0) {
  console.error(`check-indent: ${casesPath} holds no case`);
  process.exit(1);
}
if (failures.length > 0) {
  console.error(`check-indent: ${failures.length} of ${cases.length} cases fail`);
  process.exit(1);
}
console.log(`check-indent: VS Code indents all ${cases.length} cases as expected`);

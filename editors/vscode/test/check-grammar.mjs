// Checks the TextMate grammar against the lexer's highlight spans.
//
//   node editors/vscode/test/check-grammar.mjs DUMP TABLE
//
// DUMP is the JSON-lines output of `chl-parser`'s `dump_tokens` example and
// TABLE is `editors/highlight-classes.json`. Paths inside DUMP resolve against
// the working directory. Every byte of every span must carry the class's
// expected scope; see editors/README.md, "Editor highlight check".

import { readFileSync } from "node:fs";
import { ROOT_SCOPE, loadGrammar, vsctm } from "./grammar.mjs";

const [dumpPath, tablePath] = process.argv.slice(2);
if (!dumpPath || !tablePath) {
  console.error("usage: check-grammar.mjs DUMP TABLE");
  process.exit(2);
}

const table = JSON.parse(readFileSync(tablePath, "utf8"));
const spansByFile = new Map();
for (const line of readFileSync(dumpPath, "utf8").split("\n")) {
  if (line === "") continue;
  const span = JSON.parse(line);
  if (!spansByFile.has(span.file)) spansByFile.set(span.file, []);
  spansByFile.get(span.file).push(span);
}

const grammar = await loadGrammar();

// The scope stack of every byte of `source`, outermost first. A newline byte
// has none, because TextMate tokenizes line by line and never sees it; the
// check fails a span that contains one. vscode-textmate indexes a line in
// UTF-16 code units, which this converts to byte offsets.
function scopesByByte(source) {
  const scopes = new Array(Buffer.byteLength(source, "utf8")).fill(null);
  let ruleStack = vsctm.INITIAL;
  let lineStart = 0;
  for (const line of source.split("\n")) {
    const result = grammar.tokenizeLine(line, ruleStack);
    for (const token of result.tokens) {
      const start = lineStart + Buffer.byteLength(line.slice(0, token.startIndex), "utf8");
      const end = lineStart + Buffer.byteLength(line.slice(0, token.endIndex), "utf8");
      scopes.fill(token.scopes, start, end);
    }
    ruleStack = result.ruleStack;
    lineStart += Buffer.byteLength(line, "utf8") + 1;
  }
  return scopes;
}

// The innermost scope that is not `punctuation.definition.*`. That scope marks
// a delimiter of the enclosing construct (a string's quote, a comment's `#`,
// a tag's backtick), and a theme colors the delimiter as the construct. A
// `punctuation.definition.*` scope with no construct around it, only the root,
// is the relevant scope itself.
function relevantScope(stack) {
  const innermost = stack[stack.length - 1] ?? ROOT_SCOPE;
  for (let i = stack.length - 1; i >= 0; i--) {
    if (!stack[i].startsWith("punctuation.definition.")) {
      return stack[i] === ROOT_SCOPE ? innermost : stack[i];
    }
  }
  return innermost;
}

// `expected` is a dotted scope prefix, matched on segment boundaries; `null`
// means no scope beyond the root.
function matches(scope, expected) {
  if (expected === null) return scope === ROOT_SCOPE;
  return scope === expected || scope.startsWith(`${expected}.`);
}

const mismatches = [];
let checked = 0;
for (const [file, spans] of spansByFile) {
  const bytes = readFileSync(file);
  const scopes = scopesByByte(bytes.toString("utf8"));
  for (const span of spans) {
    if (!(span.class in table)) {
      mismatches.push(`${file}:${span.line}:${span.col}: class \`${span.class}\` is not in ${tablePath}`);
      continue;
    }
    const expected = table[span.class].textmate;
    const got = new Set();
    for (let b = span.start; b < span.end; b++) {
      if (bytes[b] === 0x0a) {
        got.add("a newline");
        continue;
      }
      const scope = relevantScope(scopes[b] ?? []);
      if (!matches(scope, expected)) got.add(scope);
    }
    checked++;
    if (got.size > 0) {
      const text = JSON.stringify(bytes.subarray(span.start, span.end).toString("utf8"));
      mismatches.push(
        `${file}:${span.line}:${span.col}: ${text} is ${span.class}; ` +
          `TextMate gave ${[...got].join(", ")}, expected ${expected ?? ROOT_SCOPE}`,
      );
    }
  }
}

for (const m of mismatches) console.error(m);
const summary = `${checked} spans in ${spansByFile.size} files`;
if (checked === 0) {
  console.error(`check-grammar: checked ${summary}; ${dumpPath} holds no spans`);
  process.exit(1);
}
if (mismatches.length > 0) {
  console.error(`check-grammar: ${mismatches.length} mismatches over ${summary}`);
  process.exit(1);
}
console.log(`check-grammar: TextMate grammar agrees with the lexer over ${summary}`);

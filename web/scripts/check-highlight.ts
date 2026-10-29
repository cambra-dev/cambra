// Checks the source pane's highlighting against the lexer's highlight spans.
//
//   web/node_modules/.bin/vite-node web/scripts/check-highlight.ts DUMP
//
// DUMP is the JSON-lines output of `chl-parser`'s `dump_tokens` example. Paths
// inside it resolve against the working directory. Every byte of a span must
// get the span's class from `classifyLine`, or no class when the class has no
// TextMate prefix in `editors/highlight-classes.json`. `./ci.sh editors` runs
// this beside the VS Code and Neovim checkers (`editors/README.md`, "Editor
// highlight check").

import { readFileSync } from "node:fs";

import { INITIAL } from "vscode-textmate";

import classTable from "../../editors/highlight-classes.json";
import { type ColouredClass, type HighlightClass, classifyLine } from "../src/cambraSyntax";

const [dumpPath] = process.argv.slice(2);
if (!dumpPath) {
  console.error("usage: check-highlight.ts DUMP");
  process.exit(2);
}

interface Span {
  file: string;
  line: number;
  col: number;
  start: number;
  end: number;
  class: string;
}

const spansByFile = new Map<string, Span[]>();
for (const line of readFileSync(dumpPath, "utf8").split("\n")) {
  if (line === "") continue;
  const span = JSON.parse(line) as Span;
  const spans = spansByFile.get(span.file) ?? [];
  spans.push(span);
  spansByFile.set(span.file, spans);
}

// The class of every byte of `source`, as the pane colours it. A newline byte
// has none, because the pane classifies line by line; a span holding one fails.
function classesByByte(source: string): (ColouredClass | null | undefined)[] {
  const classes = new Array<ColouredClass | null | undefined>(Buffer.byteLength(source, "utf8"));
  let stack = INITIAL;
  let lineStart = 0;
  for (const line of source.split("\n")) {
    const result = classifyLine(line, stack);
    let from = 0;
    for (const run of result.runs) {
      const start = lineStart + Buffer.byteLength(line.slice(0, from), "utf8");
      const end = lineStart + Buffer.byteLength(line.slice(0, run.end), "utf8");
      classes.fill(run.cls, start, end);
      from = run.end;
    }
    stack = result.stack;
    lineStart += Buffer.byteLength(line, "utf8") + 1;
  }
  return classes;
}

const mismatches: string[] = [];
let checked = 0;
for (const [file, spans] of spansByFile) {
  const bytes = readFileSync(file);
  const classes = classesByByte(bytes.toString("utf8"));
  for (const span of spans) {
    if (!(span.class in classTable)) {
      const where = `${file}:${span.line}:${span.col}`;
      mismatches.push(`${where}: class \`${span.class}\` is not in highlight-classes.json`);
      continue;
    }
    const cls = span.class as HighlightClass;
    const expected = classTable[cls].textmate === null ? null : cls;
    const got = new Set<string>();
    for (let b = span.start; b < span.end; b++) {
      const actual = bytes[b] === 0x0a ? undefined : classes[b];
      if (actual === undefined) got.add("a newline");
      else if (actual !== expected) got.add(actual ?? "no class");
    }
    checked++;
    if (got.size > 0) {
      const text = JSON.stringify(bytes.subarray(span.start, span.end).toString("utf8"));
      mismatches.push(
        `${file}:${span.line}:${span.col}: ${text} is ${span.class}; ` +
          `the source pane gave ${[...got].join(", ")}, expected ${expected ?? "no class"}`,
      );
    }
  }
}

for (const m of mismatches) console.error(m);
const summary = `${checked} spans in ${spansByFile.size} files`;
if (checked === 0) {
  console.error(`check-highlight: checked ${summary}; ${dumpPath} holds no spans`);
  process.exit(1);
}
if (mismatches.length > 0) {
  console.error(`check-highlight: ${mismatches.length} mismatches over ${summary}`);
  process.exit(1);
}
console.log(`check-highlight: the source pane agrees with the lexer over ${summary}`);

// Syntax highlighting for the source pane, from the VS Code grammar.
//
// The pane runs `editors/vscode/syntaxes/cambra.tmLanguage.json` under
// `vscode-textmate`, the tokenizer VS Code runs, and gives each token the class
// whose TextMate prefix in `editors/highlight-classes.json` matches its scope.
// No keyword, builtin or operator is restated here.
// `web/scripts/check-highlight.ts`, run by `./ci.sh editors`, checks the
// classes this module assigns against the lexer's highlight spans, as the VS
// Code and Neovim checkers check theirs (`editors/README.md`, "Editor highlight
// check").
//
// VS Code runs the grammar's regexes under Oniguruma, compiled to WebAssembly.
// This module runs them as JavaScript `RegExp`s instead (`jsOnigLib`), which
// keeps the wasm out of the bundle.

import {
  type Language,
  StreamLanguage,
  type StringStream,
  forceParsing,
  syntaxHighlighting,
} from "@codemirror/language";
import type { Extension } from "@codemirror/state";
import type { EditorView } from "@codemirror/view";
import { Tag, tagHighlighter } from "@lezer/highlight";
import {
  INITIAL,
  Registry,
  parseRawGrammar,
  type IGrammar,
  type IOnigCaptureIndex,
  type IOnigLib,
  type IOnigMatch,
  type OnigScanner,
  type OnigString,
  type StateStack,
} from "vscode-textmate";

import rawGrammar from "../../editors/vscode/syntaxes/cambra.tmLanguage.json";
import classTable from "../../editors/highlight-classes.json";

export const ROOT_SCOPE = "source.cambra";

/** A lexer highlight class: a key of `editors/highlight-classes.json`. */
export type HighlightClass = keyof typeof classTable;

/** The classes with a TextMate scope prefix. The rest are left uncoloured. */
export type ColouredClass = {
  [K in HighlightClass]: (typeof classTable)[K]["textmate"] extends string ? K : never;
}[HighlightClass];

/** Each coloured class with its scope prefix, longest prefix first. */
const PREFIXES: readonly (readonly [ColouredClass, string])[] = (
  Object.entries(classTable) as [HighlightClass, { textmate: string | null }][]
)
  .flatMap(([cls, row]) =>
    row.textmate === null ? [] : [[cls as ColouredClass, row.textmate] as const],
  )
  .sort((a, b) => b[1].length - a[1].length);

/**
 * Oniguruma spellings that a `RegExp` without the `u` flag accepts and reads
 * with another meaning: `\A` as `A`, `\p{L}` as `p{L}`, `[[:alpha:]]` as a
 * class holding `[`, `:` and letters. Onig-only syntax a `RegExp` rejects, such
 * as possessive quantifiers and atomic groups, already throws when compiled.
 */
function refuseOnigOnly(source: string): void {
  let inClass = false;
  for (let i = 0; i < source.length; i++) {
    const c = source[i];
    if (c === "\\") {
      const next = source[i + 1] ?? "";
      if ("AGzZhHKRXOpP".includes(next)) {
        throw new Error(`grammar regex ${JSON.stringify(source)}: \\${next} is Oniguruma-only`);
      }
      i++;
    } else if (inClass) {
      if (c === "]") inClass = false;
      else if (c === "[" && source[i + 1] === ":") {
        throw new Error(`grammar regex ${JSON.stringify(source)}: POSIX bracket is Oniguruma-only`);
      }
    } else if (c === "[") {
      inClass = true;
      // A `]` directly after `[` or `[^` is a member, not the end.
      if (source[i + 1] === "^") i++;
      if (source[i + 1] === "]") i++;
    }
  }
}

/**
 * Compiles one grammar regex as a `RegExp`.
 *
 * `m`, because Oniguruma's `^` and `$` match at line boundaries and
 * vscode-textmate appends a `\n` to every line it scans. `d`, for capture
 * offsets. `g`, so `lastIndex` sets where a search starts.
 *
 * Without the `u` flag, `\b` and `\w` are ASCII, where Oniguruma's are Unicode.
 * The two differ only where a non-ASCII letter touches a word, which the lexer
 * reports as an error outside strings and comments.
 */
export function compileOnigRegex(source: string): RegExp {
  refuseOnigOnly(source);
  return new RegExp(source, "dgm");
}

type CachedSearch = { content: string; from: number; match: RegExpExecArray | null };

/**
 * An Oniguruma scanner over `RegExp`s: the next match of any of its patterns at
 * or after a position, the earliest start winning and the first pattern among
 * equal starts, as `OnigScanner.findNextMatchSync` does.
 */
class JsOnigScanner implements OnigScanner {
  private readonly regexes: RegExp[];
  // Per pattern, its last search: a match at or after a later start position
  // over the same text is the same match, as Oniguruma's scanner cache assumes.
  private readonly cache: (CachedSearch | null)[];

  constructor(sources: string[]) {
    this.regexes = sources.map(compileOnigRegex);
    this.cache = sources.map(() => null);
  }

  findNextMatchSync(string: string | OnigString, startPosition: number): IOnigMatch | null {
    const content = typeof string === "string" ? string : string.content;
    let best: { index: number; match: RegExpExecArray } | null = null;
    for (let i = 0; i < this.regexes.length; i++) {
      const match = this.search(i, content, startPosition);
      if (match && (best === null || match.index < best.match.index)) best = { index: i, match };
    }
    if (best === null) return null;
    const { index, match } = best;
    const captureIndices: IOnigCaptureIndex[] = match.indices!.map((range) =>
      // An unmatched group has length 0, which vscode-textmate skips.
      range === undefined
        ? { start: match.index, end: match.index, length: 0 }
        : { start: range[0], end: range[1], length: range[1] - range[0] },
    );
    return { index, captureIndices };
  }

  private search(i: number, content: string, from: number): RegExpExecArray | null {
    const hit = this.cache[i];
    const reusable =
      hit !== null &&
      hit.content === content &&
      hit.from <= from &&
      (hit.match === null || hit.match.index >= from);
    if (reusable) return hit.match;
    const re = this.regexes[i];
    re.lastIndex = from;
    const match = re.exec(content);
    this.cache[i] = { content, from, match };
    return match;
  }
}

export const jsOnigLib: IOnigLib = {
  createOnigScanner: (sources) => new JsOnigScanner(sources),
  createOnigString: (content) => ({ content }),
};

async function loadGrammar(): Promise<IGrammar> {
  const registry = new Registry({
    onigLib: Promise.resolve(jsOnigLib),
    loadGrammar: async (scopeName) =>
      scopeName === ROOT_SCOPE
        ? parseRawGrammar(JSON.stringify(rawGrammar), "cambra.tmLanguage.json")
        : null,
  });
  const grammar = await registry.loadGrammar(ROOT_SCOPE);
  if (!grammar) throw new Error(`vscode-textmate found no grammar for ${ROOT_SCOPE}`);
  return grammar;
}

// Loaded at module evaluation, so the source pane builds its editor with the
// language already in it. Loading resolves through promises alone, with no
// I/O; regexes compile when a line first needs them.
export const grammar: IGrammar = await loadGrammar();

/**
 * The innermost scope that is not `punctuation.definition.*`, which marks a
 * delimiter of the enclosing construct, such as a string's quote. The rule
 * `editors/vscode/test/check-grammar.mjs` applies (`editors/README.md`, "Editor
 * highlight check").
 */
export function relevantScope(stack: readonly string[]): string {
  const innermost = stack[stack.length - 1] ?? ROOT_SCOPE;
  for (let i = stack.length - 1; i >= 0; i--) {
    if (!stack[i].startsWith("punctuation.definition.")) {
      return stack[i] === ROOT_SCOPE ? innermost : stack[i];
    }
  }
  return innermost;
}

/**
 * The class whose TextMate prefix is the longest one the scope starts with on
 * a segment boundary, or null for none. Longest, because one class's prefix can
 * extend another's: `keyword.other.mutation` is `mutation`, not
 * `keyword-other`.
 */
export function classOfScope(scope: string): ColouredClass | null {
  for (const [cls, prefix] of PREFIXES) {
    if (scope === prefix || scope.startsWith(`${prefix}.`)) return cls;
  }
  return null;
}

/** A run of a line in one class, ending at UTF-16 offset `end`. */
export interface ClassRun {
  end: number;
  cls: ColouredClass | null;
}

/** One line's class runs, and the grammar state the next line starts from. */
export function classifyLine(
  line: string,
  stack: StateStack,
): { runs: ClassRun[]; stack: StateStack } {
  const result = grammar.tokenizeLine(line, stack);
  const runs = result.tokens.map((t) => ({
    end: Math.min(t.endIndex, line.length),
    cls: classOfScope(relevantScope(t.scopes)),
  }));
  return { runs, stack: result.ruleStack };
}

// ---------------------------------------------------------------------------
// CodeMirror

interface LineState {
  stack: StateStack;
  // The current line's runs and the next one to emit; null before its first token.
  runs: ClassRun[] | null;
  next: number;
}

// Token names carry a prefix: StreamLanguage resolves a few bare names, `type`
// and `builtin` among them, to its own legacy tags before it consults
// `tokenTable`.
const tokenName = (cls: ColouredClass): string => `cambra-${cls}`;

const CLASS_TAGS = new Map<ColouredClass, Tag>(PREFIXES.map(([cls]) => [cls, Tag.define()]));

const streamLanguage: Language = StreamLanguage.define<LineState>({
  name: "cambra",
  startState: () => ({ stack: INITIAL, runs: null, next: 0 }),
  copyState: (s) => ({ ...s }),
  token(stream: StringStream, state: LineState): string | null {
    if (stream.sol() || state.runs === null) {
      const { runs, stack } = classifyLine(stream.string, state.stack);
      state.runs = runs;
      state.next = 0;
      state.stack = stack;
    }
    const run = state.runs[state.next];
    if (run === undefined) {
      stream.skipToEnd();
      return null;
    }
    state.next += 1;
    stream.pos = Math.min(stream.string.length, Math.max(run.end, stream.pos + 1));
    if (stream.eol()) state.runs = null;
    return run.cls === null ? null : tokenName(run.cls);
  },
  // An empty line still steps the grammar, which can hold a construct open.
  blankLine(state: LineState) {
    state.stack = classifyLine("", state.stack).stack;
    state.runs = null;
  },
  languageData: { commentTokens: { line: "#" } },
  tokenTable: Object.fromEntries([...CLASS_TAGS].map(([cls, tag]) => [tokenName(cls), tag])),
});

/**
 * The CSS classes a token of `cls` carries: `cm-cambra-<class>`, and
 * `cm-cambra-<Group>` for the class's Vim group in `highlight-classes.json`.
 * `style.css` colours the groups, so the pane draws the families Neovim draws,
 * and a new class with an existing group needs no new rule.
 */
export function cssClasses(cls: ColouredClass): string {
  const group: string | null = classTable[cls].vim;
  return group === null ? `cm-cambra-${cls}` : `cm-cambra-${cls} cm-cambra-${group}`;
}

/** The source pane's language and its highlighter. */
export const cambraSyntax: Extension = [
  streamLanguage,
  syntaxHighlighting(
    tagHighlighter([...CLASS_TAGS].map(([cls, tag]) => ({ tag, class: cssClasses(cls) }))),
  ),
];

/**
 * Highlights the whole document now. Without it the parse worker colours the
 * document after the first paint, and the pane shows the colour arriving.
 */
export function highlightNow(view: EditorView): void {
  forceParsing(view, view.state.doc.length, 200);
}

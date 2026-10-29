// @vitest-environment jsdom
//
// The source pane's syntax highlighting. Agreement with the lexer over the
// `.cambra` corpus is `web/scripts/check-highlight.ts`, under `./ci.sh editors`;
// these tests cover what that check cannot reach without the Rust toolchain: the
// regex engine on its own, the scope-to-class rule, the editor wiring, and the
// palette.

import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { EditorState } from "@codemirror/state";
import { EditorView } from "@codemirror/view";
import { afterEach, describe, expect, it } from "vitest";

import rawGrammar from "../../editors/vscode/syntaxes/cambra.tmLanguage.json";
import classTable from "../../editors/highlight-classes.json";
import {
  ROOT_SCOPE,
  classOfScope,
  compileOnigRegex,
  cambraSyntax,
  highlightNow,
  jsOnigLib,
  relevantScope,
} from "./cambraSyntax";

/** Every `match`, `begin` and `end` regex in the grammar. */
function grammarRegexes(node: unknown, out: string[] = []): string[] {
  if (Array.isArray(node)) {
    for (const x of node) grammarRegexes(x, out);
  } else if (node !== null && typeof node === "object") {
    for (const [key, value] of Object.entries(node)) {
      if ((key === "match" || key === "begin" || key === "end") && typeof value === "string") {
        out.push(value);
      } else {
        grammarRegexes(value, out);
      }
    }
  }
  return out;
}

describe("the regex engine", () => {
  it("compiles every regex in the VS Code grammar", () => {
    const sources = grammarRegexes(rawGrammar);
    expect(sources.length).toBeGreaterThan(20);
    for (const source of sources) expect(() => compileOnigRegex(source), source).not.toThrow();
  });

  it("refuses Oniguruma spellings a RegExp reads with another meaning", () => {
    for (const source of ["\\Afoo", "a\\G", "\\p{L}", "x\\z", "[[:alpha:]]"]) {
      expect(() => compileOnigRegex(source), source).toThrow(/Oniguruma-only/);
    }
    // An escaped backslash before `A`, and `[` as a class member, are plain.
    for (const source of ["\\\\A", "[\\]A]", "[]:]", "[^]:]"]) {
      expect(() => compileOnigRegex(source), source).not.toThrow();
    }
  });

  it("matches `$` before the newline vscode-textmate appends to a line", () => {
    const scanner = jsOnigLib.createOnigScanner(["$"]);
    expect(scanner.findNextMatchSync("ab\n", 0, 0)?.captureIndices[0].start).toBe(2);
  });

  it("takes the earliest match, and the first pattern among equal starts", () => {
    const scanner = jsOnigLib.createOnigScanner(["b", "a", "ab"]);
    const string = jsOnigLib.createOnigString("xab\n");
    expect(scanner.findNextMatchSync(string, 0, 0)).toEqual({
      index: 1,
      captureIndices: [{ start: 1, end: 2, length: 1 }],
    });
    // From past the `a`, the cached search for `a` no longer applies.
    expect(scanner.findNextMatchSync(string, 2, 0)?.index).toBe(0);
    expect(scanner.findNextMatchSync(string, 3, 0)).toBeNull();
  });

  it("reports an unmatched group with length 0", () => {
    const scanner = jsOnigLib.createOnigScanner(["(x)|(y)"]);
    const { captureIndices } = scanner.findNextMatchSync("y", 0, 0)!;
    expect(captureIndices[1].length).toBe(0);
    expect(captureIndices[2]).toEqual({ start: 0, end: 1, length: 1 });
  });
});

describe("scope to class", () => {
  it("takes the longest prefix, so a class extending another's prefix wins", () => {
    expect(classOfScope("keyword.other.cambra")).toBe("keyword-other");
    expect(classOfScope("keyword.other.mutation.cambra")).toBe("mutation");
    expect(classOfScope("entity.name.function.cambra")).toBe("function-name");
    expect(classOfScope("entity.name.function.decorator.cambra")).toBe("decorator");
  });

  it("matches a prefix on segment boundaries only", () => {
    expect(classOfScope("punctuationx.cambra")).toBeNull();
    expect(classOfScope(ROOT_SCOPE)).toBeNull();
  });

  it("names a class for every class with a TextMate prefix", () => {
    for (const [cls, row] of Object.entries(classTable)) {
      if (row.textmate !== null) expect(classOfScope(`${row.textmate}.cambra`), cls).toBe(cls);
    }
  });

  it("looks through a delimiter to the construct around it", () => {
    const quote = "punctuation.definition.string.begin.cambra";
    expect(relevantScope([ROOT_SCOPE, "string.quoted.double.cambra", quote])).toBe(
      "string.quoted.double.cambra",
    );
    // A delimiter with no construct around it is the relevant scope itself.
    const decorator = "punctuation.definition.decorator.cambra";
    expect(relevantScope([ROOT_SCOPE, decorator])).toBe(decorator);
    expect(relevantScope([])).toBe(ROOT_SCOPE);
  });
});

describe("the source pane's editor", () => {
  let view: EditorView | null = null;
  afterEach(() => {
    view?.destroy();
    view = null;
  });

  function mount(doc: string): EditorView {
    const parent = document.body.appendChild(document.createElement("div"));
    const state = EditorState.create({ doc, extensions: [cambraSyntax] });
    view = new EditorView({ state, parent });
    highlightNow(view);
    return view;
  }

  /** The text of every element carrying `cm-cambra-<cls>`. */
  function coloured(v: EditorView, cls: string): string[] {
    return [...v.contentDOM.querySelectorAll(`.cm-cambra-${cls}`)].map((e) => e.textContent ?? "");
  }

  it("colours each class, with its Vim group's class beside it", () => {
    const v = mount(
      [
        "def f(x: Int):",
        '    return x + "a\\n"  # TODO',
        "n := 0",
        "out << `some(True)",
      ].join("\n"),
    );
    expect(coloured(v, "keyword-other")).toEqual(["def"]);
    expect(coloured(v, "function-name")).toEqual(["f"]);
    expect(coloured(v, "type")).toEqual(["Int"]);
    expect(coloured(v, "keyword-control")).toEqual(["return"]);
    expect(coloured(v, "Statement")).toEqual(["return"]);
    expect(coloured(v, "string")).toEqual(['"a', '"']);
    expect(coloured(v, "escape")).toEqual(["\\n"]);
    expect(coloured(v, "comment")).toEqual(["# "]);
    expect(coloured(v, "todo")).toEqual(["TODO"]);
    expect(coloured(v, "mutation")).toEqual([":="]);
    expect(coloured(v, "feed")).toEqual(["<<"]);
    expect(coloured(v, "variant-tag")).toEqual(["`some"]);
    expect(coloured(v, "boolean")).toEqual(["True"]);
    // An identifier carries no class.
    expect(v.contentDOM.querySelectorAll('[class*="cm-cambra-identifier"]')).toHaveLength(0);
  });

  it("re-colours text as it is edited", () => {
    const v = mount("x = 1");
    expect(coloured(v, "keyword-control")).toEqual([]);
    v.dispatch({ changes: { from: 0, insert: "if " } });
    highlightNow(v);
    expect(coloured(v, "keyword-control")).toEqual(["if"]);
  });
});

describe("the palette", () => {
  it("has a rule for every Vim group a coloured class names", () => {
    const css = readFileSync(resolve(__dirname, "style.css"), "utf8");
    const groups = new Set(
      Object.values(classTable).flatMap((row) =>
        row.textmate !== null && row.vim !== null ? [row.vim] : [],
      ),
    );
    expect(groups.size).toBeGreaterThan(5);
    for (const group of groups) expect(css, group).toMatch(new RegExp(`\\.cm-cambra-${group}\\b`));
  });
});

// The source pane's tokenizer, and the thing that keeps it honest.
//
// `cambraLang.ts` restates the language's keyword set in TypeScript, which is a
// duplicate of `src/chl_parser/lexer.rs` and would rot silently: a keyword added
// to the language would simply stop being highlighted, with nothing failing. So
// the first test here reads `lexer.rs` and asserts the two agree. It is the same
// bargain `fixtures.manifest` makes for the snapshot corpus — duplicate the
// fact, then pin it.

// The lexer is read off disk rather than imported: Vite's `?raw` refuses a path
// outside the project root, and widening `server.fs.allow` to reach the Rust
// tree would loosen the dev server for every request to buy one test a file.
// `@types/node` is a types-only devDependency and costs the bundle nothing.

import { readFileSync } from "node:fs";

import { StringStream } from "@codemirror/language";
import { describe, expect, it } from "vitest";

import { BOOLEANS, KEYWORDS, OPERATORS, token } from "./cambraLang";

const LEXER = new URL("../../src/chl_parser/lexer.rs", import.meta.url);

/**
 * Every word-shaped `#[token("...")]` in the lexer.
 *
 * Word-shaped on purpose: the lexer also declares punctuation and delimiters
 * that way, and those are not the drift this guards. A keyword is the thing a
 * reader expects to see coloured.
 */
function lexerKeywords(): Set<string> {
  const source = readFileSync(LEXER, "utf8");
  const found = new Set<string>();
  for (const m of source.matchAll(/#\[token\("([A-Za-z_][A-Za-z0-9_]*)"/g)) {
    found.add(m[1]);
  }
  return found;
}

/** Run the tokenizer over one line, as `[text, tag]` pairs, skipping whitespace. */
function lex(line: string): [string, string | null][] {
  const stream = new StringStream(line, 2, 2);
  const out: [string, string | null][] = [];
  let guard = 0;
  while (!stream.eol()) {
    if (guard++ > 500) throw new Error("tokenizer made no progress");
    const before = stream.pos;
    const tag = token(stream);
    if (stream.pos === before) throw new Error(`no progress at ${before}`);
    const text = line.slice(before, stream.pos);
    stream.start = stream.pos;
    if (text.trim() === "") continue;
    out.push([text, tag]);
  }
  return out;
}

describe("the keyword set tracks lexer.rs", () => {
  it("finds the lexer, so this test cannot pass by reading nothing", () => {
    expect(lexerKeywords().size).toBeGreaterThan(10);
  });

  it("declares exactly the words lexer.rs does", () => {
    const ours = new Set([...KEYWORDS, ...BOOLEANS]);
    expect([...lexerKeywords()].sort()).toEqual([...ours].sort());
  });

  it("keeps the two sets disjoint, so a word gets one tag", () => {
    expect([...KEYWORDS].filter((k) => BOOLEANS.has(k))).toEqual([]);
  });
});

describe("tokenizer", () => {
  it("takes a comment to end of line", () => {
    expect(lex("x = 1  # prices are scaled by 10^8")).toEqual([
      ["x", null],
      ["=", "channelOp"],
      ["1", "number"],
      ["# prices are scaled by 10^8", "comment"],
    ]);
  });

  it("reads both quote styles, and escapes inside them", () => {
    expect(lex(`"BTC-USD"`)).toEqual([[`"BTC-USD"`, "string"]]);
    expect(lex(`'ETH-USD'`)).toEqual([[`'ETH-USD'`, "string"]]);
    expect(lex(`"a\\"b"`)).toEqual([[`"a\\"b"`, "string"]]);
  });

  it("ends an unterminated string at the line, not at the file", () => {
    // The pane renders programs that failed to compile, so one stray quote
    // should cost one line of colour rather than the rest of the document.
    expect(lex(`"oops`)).toEqual([[`"oops`, "string"]]);
  });

  it("separates keywords from identifiers that merely contain them", () => {
    expect(lex("for u in price_updates()")).toEqual([
      ["for", "keyword"],
      ["u", null],
      ["in", "keyword"],
      ["price_updates", null],
      ["(", null],
      [")", null],
    ]);
    // `information` starts with `in`; `formatted` starts with `for`.
    expect(lex("information formatted")).toEqual([
      ["information", null],
      ["formatted", null],
    ]);
  });

  it("tags True and False as literals rather than control flow", () => {
    expect(lex("True False")).toEqual([
      ["True", "bool"],
      ["False", "bool"],
    ]);
  });

  it("gives the sink write and the store commit their own tag", () => {
    expect(lex("btc_line << (qty=btc_qty)")).toEqual([
      ["btc_line", null],
      ["<<", "channelOp"],
      ["(", null],
      ["qty", null],
      ["=", "channelOp"],
      ["btc_qty", null],
      [")", null],
    ]);
    expect(lex("btc_px := u.price")).toEqual([
      ["btc_px", null],
      [":=", "channelOp"],
      ["u", null],
      [".", null],
      ["price", null],
    ]);
  });

  it("keeps the operator table sorted longest-first", () => {
    // The tokenizer takes the first entry that matches, so a short operator
    // sitting above a longer one starting with it would shadow it — `=` above
    // `==` would lex a comparison as two assignments.
    const lengths = OPERATORS.map(([op]) => op.length);
    expect(lengths).toEqual([...lengths].sort((a, b) => b - a));
  });

  it("does not let a bare `=` shadow the operators that start with one", () => {
    expect(lex("a == b")[1]).toEqual(["==", "operator"]);
    expect(lex("a => b")[1]).toEqual(["=>", "operator"]);
    expect(lex("a = b")[1]).toEqual(["=", "channelOp"]);
  });

  it("prefers the longer operator where two overlap", () => {
    // `<<=` must not lex as `<<` then `=`, and `<=` must not lex as `<` then `=`.
    expect(lex("a <<= b")[1]).toEqual(["<<=", "channelOp"]);
    expect(lex("a <= b")[1]).toEqual(["<=", "operator"]);
    expect(lex("a <: b")[1]).toEqual(["<:", "operator"]);
  });

  it("leaves a type annotation's parts addressable", () => {
    expect(lex("btc_px: Mut(Int, Txn) := 0")).toEqual([
      ["btc_px", null],
      [":", null],
      ["Mut", null],
      ["(", null],
      ["Int", null],
      [",", null],
      ["Txn", null],
      [")", null],
      [":=", "channelOp"],
      ["0", "number"],
    ]);
  });

  it("makes progress on anything, including characters it does not claim", () => {
    expect(() => lex("@ ~ ` $ ?")).not.toThrow();
  });
});

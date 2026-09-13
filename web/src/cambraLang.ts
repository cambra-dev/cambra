// Syntax highlighting for the source pane.
//
// A `StreamLanguage` rather than a Lezer grammar, because the pane's whole
// requirement is a tokenizer. It renders one immutable file, read-only: no
// folding, no indentation, no completion, no incremental reparse, nothing that
// wants a tree. It also costs no dependency — `@codemirror/language` and
// `@lezer/highlight` are already here under the `codemirror` meta-package.
//
// Reusing a Python mode was the alternative, and the surface really is close.
// It is wrong in knowable ways: Python highlights nineteen words Cambra does not
// have (`class`, `import`, `lambda`, `None`, `while`, `try`, ...), so a program
// using one as an identifier gets coloured as a keyword; it misses `where`,
// which Cambra does have; and it reads `<<` as a bit shift rather than as the
// write to a sink, which is the operator a reader most needs to find.
//
// The token set below is `src/chl_parser/lexer.rs` restated. `cambraLang.test.ts`
// reads that file and fails when the two disagree, so a keyword added to the
// language cannot quietly stop being highlighted here.

import {
  HighlightStyle,
  StreamLanguage,
  type StringStream,
  syntaxHighlighting,
} from "@codemirror/language";
import { Tag, tags } from "@lezer/highlight";

/**
 * The language's keywords, as `lexer.rs` declares them.
 *
 * `True` and `False` are lexed as keywords there but read as literals, so they
 * are tagged as such; the pinning test asserts against the union, which is what
 * `lexer.rs` actually holds.
 */
export const KEYWORDS: ReadonlySet<string> = new Set([
  "where",
  "and",
  "or",
  "not",
  "if",
  "elif",
  "else",
  "for",
  "in",
  "def",
  "return",
  "yield",
  "pass",
  "with",
  "match",
  "case",
]);

/** Keyword-lexed literals. Part of `lexer.rs`'s keyword set; not control flow. */
export const BOOLEANS: ReadonlySet<string> = new Set(["True", "False"]);

/**
 * Every operator, longest first, with the tag it takes.
 *
 * One ordered table rather than a "channel ops" list checked before a general
 * one: the ordering constraints cross the two groups. `==` and `=>` have to be
 * tried before `=`, and `<<=` before `<<`, so splitting them into separate
 * loops put a correctness requirement somewhere it did not show. Sorted by
 * length here, and `cambraLang.test.ts` asserts that it stays sorted.
 *
 * `channelOp` covers the three ways a program moves a value into something:
 * `<<` writes a row to a sink, `:=` commits to a store, and `=` binds a name.
 * They are tagged together so that scanning for "where does a value land" is
 * one colour rather than three.
 */
export const OPERATORS: readonly (readonly [string, string])[] = [
  ["<<=", "channelOp"],
  ["//=", "operator"],
  ["==", "operator"],
  ["!=", "operator"],
  ["<=", "operator"],
  [">=", "operator"],
  ["=>", "operator"],
  ["->", "operator"],
  ["<<", "channelOp"],
  [":=", "channelOp"],
  ["<:", "operator"],
  ["++", "operator"],
  ["+=", "operator"],
  ["-=", "operator"],
  ["*=", "operator"],
  ["^+", "operator"],
  ["^*", "operator"],
  ["//", "operator"],
  ["=", "channelOp"],
  ["+", "operator"],
  ["-", "operator"],
  ["*", "operator"],
  ["&", "operator"],
  ["|", "operator"],
  ["^", "operator"],
  ["<", "operator"],
  [">", "operator"],
];

/**
 * A write to a sink, a commit to a store, or a binding.
 *
 * Its own tag rather than `tags.operator`: the highlight style gives it ink and
 * weight where ordinary operators get neither, and a tag of our own cannot
 * collide with a meaning some other grammar assigns.
 */
export const channelOp = Tag.define();

const IDENT_START = /[A-Za-z_]/;
const IDENT_REST = /[A-Za-z0-9_]/;
const DIGIT = /[0-9]/;

/**
 * One token, or null for whitespace and anything unclaimed.
 *
 * Exported so the tests can drive it over a `StringStream` directly. Going
 * through a mounted editor would assert CodeMirror's highlighting plumbing
 * rather than this token table.
 */
export function token(stream: StringStream): string | null {
  if (stream.eatSpace()) return null;

  // `#` to end of line. `lexer.rs` skips these before the parser sees them.
  if (stream.peek() === "#") {
    stream.skipToEnd();
    return "comment";
  }

  // Both quote styles, with backslash escapes. An unterminated string ends at
  // the newline rather than swallowing the rest of the file: the pane shows
  // programs that failed to compile, and one bad quote should cost one line.
  const quote = stream.peek();
  if (quote === '"' || quote === "'") {
    stream.next();
    while (!stream.eol()) {
      const ch = stream.next();
      if (ch === "\\") {
        stream.next();
        continue;
      }
      if (ch === quote) break;
    }
    return "string";
  }

  const head = stream.peek();
  if (head !== undefined && DIGIT.test(head)) {
    stream.eatWhile(DIGIT);
    return "number";
  }

  if (head !== undefined && IDENT_START.test(head)) {
    stream.eatWhile(IDENT_REST);
    const word = stream.current();
    if (BOOLEANS.has(word)) return "bool";
    if (KEYWORDS.has(word)) return "keyword";
    return null;
  }

  for (const [op, tag] of OPERATORS) {
    if (stream.match(op)) return tag;
  }

  stream.next();
  return null;
}

export const cambraStream = StreamLanguage.define({
  name: "cambra",
  token,
  languageData: {
    commentTokens: { line: "#" },
  },
  tokenTable: {
    channelOp,
  },
});

/**
 * The scheme, which works around the pane's other colours rather than ducking
 * them.
 *
 * The pane spends blue on `--sel-here` and `--edge`, amber on `--sel-elsewhere`
 * and `--node-id`, and red on `--err`. Those carry provenance and diagnostics,
 * and syntax must never be mistaken for either — so it takes the hues that are
 * free. Purple for keywords, green for every literal, magenta for the channel
 * operators. None of the three appears anywhere else in the app.
 *
 * Literals share one colour on purpose: a string, a number and `True` are the
 * same kind of thing to a reader scanning for them. Identifiers and ordinary
 * operators keep default ink — a program is mostly identifiers, and colouring
 * those is what turns highlighting into noise.
 *
 * `channelOp` is the loudest, and is the only one that also takes weight: `<<`
 * and `:=` are the two places data crosses a boundary rather than being
 * computed, which is the thing worth spotting from the back of a room.
 */
export const cambraHighlight = HighlightStyle.define([
  { tag: tags.comment, color: "var(--syn-comment)", fontStyle: "italic" },
  { tag: tags.keyword, color: "var(--syn-keyword)", fontWeight: "600" },
  { tag: tags.string, color: "var(--syn-literal)" },
  { tag: tags.number, color: "var(--syn-literal)" },
  { tag: tags.bool, color: "var(--syn-literal)" },
  { tag: channelOp, color: "var(--syn-channel)", fontWeight: "700" },
]);

/** The source pane's language support: tokenizer plus the restrained scheme. */
export const cambraLanguage = [
  cambraStream,
  syntaxHighlighting(cambraHighlight),
];

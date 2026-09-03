import { describe, expect, it } from "vitest";

import { OffsetMap, wordRangeAt } from "./offsets";

describe("OffsetMap", () => {
  // "café\n×2": c a f are ASCII (1 byte), é is 2 bytes (U+00E9), \n is 1,
  // × is 2 bytes (U+00D7), 2 is 1. UTF-16 indices are all single units here.
  const text = "café\n×2";
  const map = new OffsetMap(text);

  it("reports byte and char lengths", () => {
    // c(1)+a(1)+f(1)+é(2)+\n(1)+×(2)+2(1) = 9 bytes; 7 UTF-16 units.
    expect(map.byteLength).toBe(9);
    expect(map.charLength).toBe(7);
  });

  it("maps char offsets to byte offsets across multi-byte chars", () => {
    expect(map.charToByte(0)).toBe(0); // before 'c'
    expect(map.charToByte(3)).toBe(3); // before 'é'
    expect(map.charToByte(4)).toBe(5); // after 'é' (é = 2 bytes), before '\n'
    expect(map.charToByte(5)).toBe(6); // before '×'
    expect(map.charToByte(6)).toBe(8); // after '×' (2 bytes), before '2'
    expect(map.charToByte(7)).toBe(9); // end of doc
  });

  it("maps byte offsets back to char offsets", () => {
    expect(map.byteToChar(0)).toBe(0);
    expect(map.byteToChar(3)).toBe(3); // start of 'é'
    expect(map.byteToChar(5)).toBe(4); // after 'é'
    expect(map.byteToChar(6)).toBe(5); // start of '×'
    expect(map.byteToChar(8)).toBe(6); // start of '2'
    expect(map.byteToChar(9)).toBe(7); // end
  });

  it("round-trips char -> byte -> char at every char boundary", () => {
    for (let c = 0; c <= map.charLength; c++) {
      expect(map.byteToChar(map.charToByte(c))).toBe(c);
    }
  });

  it("round-trips byte -> char -> byte at every code-point byte boundary", () => {
    // Boundaries that start a code point: 0,1,2,3,5,6,8,9.
    for (const b of [0, 1, 2, 3, 5, 6, 8, 9]) {
      expect(map.charToByte(map.byteToChar(b))).toBe(b);
    }
  });

  it("snaps a byte offset inside a multi-byte sequence to its start", () => {
    // Byte 4 is the 2nd byte of 'é' (bytes 3..5); snaps to char 4 (after é),
    // since byteToChar finds the first index whose byte value >= target.
    expect(map.byteToChar(4)).toBe(4);
  });

  it("clamps out-of-range inputs", () => {
    expect(map.charToByte(-5)).toBe(0);
    expect(map.charToByte(999)).toBe(9);
    expect(map.byteToChar(-5)).toBe(0);
    expect(map.byteToChar(999)).toBe(7);
  });

  it("is identity for pure ASCII", () => {
    const ascii = new OffsetMap("hello world");
    for (let i = 0; i <= 11; i++) {
      expect(ascii.charToByte(i)).toBe(i);
      expect(ascii.byteToChar(i)).toBe(i);
    }
  });

  it("handles an astral code point (surrogate pair)", () => {
    // "a😀b": 'a'(1 byte, 1 unit), 😀 U+1F600 (4 bytes, 2 units), 'b'(1,1).
    const astral = new OffsetMap("a😀b");
    expect(astral.byteLength).toBe(6);
    expect(astral.charLength).toBe(4);
    expect(astral.charToByte(0)).toBe(0); // 'a'
    expect(astral.charToByte(1)).toBe(1); // start of 😀
    expect(astral.charToByte(3)).toBe(5); // 'b' (after 4-byte emoji)
    expect(astral.charToByte(4)).toBe(6); // end
    expect(astral.byteToChar(5)).toBe(3); // 'b'
  });
});

describe("wordRangeAt", () => {
  it("takes the whole token the offset lands in", () => {
    const t = "        if pool > r:";
    expect(wordRangeAt(t, 8)).toEqual({ from: 8, to: 10 }); // on the `i`
    expect(wordRangeAt(t, 9)).toEqual({ from: 8, to: 10 }); // on the `f`
    expect(wordRangeAt(t, 13)).toEqual({ from: 11, to: 15 }); // inside `pool`
  });

  it("takes the single character when it is not part of a token", () => {
    const t = "a + b";
    expect(wordRangeAt(t, 1)).toEqual({ from: 1, to: 2 }); // the space
    expect(wordRangeAt(t, 2)).toEqual({ from: 2, to: 3 }); // the `+`
  });

  it("counts digits and underscores as token characters", () => {
    expect(wordRangeAt("__arg_0 = 12", 3)).toEqual({ from: 0, to: 7 });
    expect(wordRangeAt("__arg_0 = 12", 11)).toEqual({ from: 10, to: 12 });
  });

  it("clamps at both ends of the document", () => {
    expect(wordRangeAt("xy", -5)).toEqual({ from: 0, to: 2 });
    expect(wordRangeAt("xy", 2)).toEqual({ from: 2, to: 2 });
    expect(wordRangeAt("", 0)).toEqual({ from: 0, to: 0 });
  });
});

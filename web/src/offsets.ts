// The byte<->char bridge (CORRECTNESS-CRITICAL).
//
// Cambra `Span`s carry UTF-8 *byte* offsets into the source text. CodeMirror 6
// positions are document offsets measured in UTF-16 code units (the JS string
// indexing unit). For ASCII the two coincide, but the substrate's contract is
// bytes, so every crossing between a Cambra span and a CM position MUST route
// through this module — never index a CM doc with a raw Cambra byte offset.
//
// We precompute, once per source, the cumulative UTF-8 byte length at each
// UTF-16 code-unit boundary. `byteAt[i]` is the byte offset of the char that
// starts at UTF-16 index `i` (so `byteAt[doc.length]` is the total byte length).
// Lookups are then a binary search rather than a re-encode per query.

const enc = new TextEncoder();

export class OffsetMap {
  // byteAt[i] = cumulative UTF-8 byte offset at UTF-16 code-unit index i.
  // Length is text.length + 1; strictly non-decreasing.
  private readonly byteAt: number[];

  constructor(text: string) {
    const byteAt = new Array<number>(text.length + 1);
    let byte = 0;
    // Iterate by code *point* (so a surrogate pair is one step), recording the
    // running byte total at each of the 1-or-2 UTF-16 units it spans.
    let i = 0;
    for (const ch of text) {
      byteAt[i] = byte;
      const units = ch.length; // 1 for BMP, 2 for an astral code point
      const chBytes = enc.encode(ch).length;
      // Interior unit of a surrogate pair maps to the same byte offset as its
      // start; a char-offset never lands strictly inside a surrogate pair in
      // practice, but keep the table total well-defined.
      for (let u = 1; u < units; u++) byteAt[i + u] = byte;
      byte += chBytes;
      i += units;
    }
    byteAt[i] = byte; // sentinel at end-of-document
    this.byteAt = byteAt;
  }

  /** Total UTF-8 byte length of the source. */
  get byteLength(): number {
    return this.byteAt[this.byteAt.length - 1];
  }

  /** Total UTF-16 code-unit length (i.e. the CM document length). */
  get charLength(): number {
    return this.byteAt.length - 1;
  }

  /** Char offset (UTF-16 index) -> UTF-8 byte offset. Clamps to range. */
  charToByte(charOffset: number): number {
    const i = clamp(charOffset, 0, this.byteAt.length - 1);
    return this.byteAt[i];
  }

  /**
   * UTF-8 byte offset -> char offset (UTF-16 index). Clamps to range.
   *
   * `byteAt` is non-decreasing, so we binary-search for the first index whose
   * byte value is >= `byteOffset`. A byte offset that lands strictly inside a
   * multi-byte sequence (should not happen for real spans) snaps to the start
   * of that code point.
   */
  byteToChar(byteOffset: number): number {
    const target = clamp(byteOffset, 0, this.byteLength);
    const a = this.byteAt;
    let lo = 0;
    let hi = a.length - 1;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (a[mid] < target) lo = mid + 1;
      else hi = mid;
    }
    return lo;
  }
}

function clamp(x: number, lo: number, hi: number): number {
  return x < lo ? lo : x > hi ? hi : x;
}

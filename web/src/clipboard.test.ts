// @vitest-environment jsdom
//
// The clipboard shim's three outcomes. jsdom implements no clipboard, so
// `navigator.clipboard` is installed per test — which is also the "absent API"
// case the shim has to survive on a non-secure origin.

import { afterEach, describe, expect, it, vi } from "vitest";

import { copyToClipboard } from "./clipboard";

function installClipboard(writeText: (text: string) => Promise<void>): void {
  Object.defineProperty(navigator, "clipboard", { value: { writeText }, configurable: true });
}

afterEach(() => {
  Reflect.deleteProperty(navigator, "clipboard");
});

describe("copyToClipboard", () => {
  it("returns false when navigator.clipboard is absent", async () => {
    expect(navigator.clipboard).toBeUndefined();
    await expect(copyToClipboard("hello")).resolves.toBe(false);
  });

  it("writes the exact text and returns true", async () => {
    const writeText = vi.fn().mockResolvedValue(undefined);
    installClipboard(writeText);

    await expect(copyToClipboard("a\n  b\n")).resolves.toBe(true);
    expect(writeText).toHaveBeenCalledTimes(1);
    expect(writeText).toHaveBeenCalledWith("a\n  b\n");
  });

  it("returns false rather than throwing when the write is refused", async () => {
    // What a denied permission or an unfocused document produces.
    installClipboard(vi.fn().mockRejectedValue(new DOMException("Denied", "NotAllowedError")));

    await expect(copyToClipboard("hello")).resolves.toBe(false);
  });
});

// Pure unit test for `resolvedTypeTooltip` (Bug 2): the B5 hole→resolved-type
// tooltip string. The string logic is extracted from the DOM so it can be
// covered directly; the jsdom view-integration test (treeView.dom.test.ts)
// exercises the rendering path.

import { describe, expect, it } from "vitest";

import { resolvedTypeTooltip } from "./treeView";

describe("resolvedTypeTooltip", () => {
  it("renders a single resolved type", () => {
    expect(resolvedTypeTooltip("_", ["Int"])).toBe("`_` resolves to `Int`");
  });

  it("joins a mono fan-out type set with ` | `", () => {
    expect(resolvedTypeTooltip("_", ["Int", "String"])).toBe(
      "`_` resolves to `Int | String`",
    );
  });

  it("returns null when there are no resolved types", () => {
    expect(resolvedTypeTooltip("_", [])).toBeNull();
  });

  it("returns null when the local hole type is null", () => {
    expect(resolvedTypeTooltip(null, ["Int"])).toBeNull();
  });

  it("uses the actual local hole type in the message", () => {
    expect(resolvedTypeTooltip("(_ ⇒ _)", ["(Int ⇒ Int)"])).toBe(
      "`(_ ⇒ _)` resolves to `(Int ⇒ Int)`",
    );
  });
});

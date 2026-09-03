// The fixture loader's *error* path. `fixture()` exists to turn an opaque
// WireError into the re-bless procedure, so the enrichment is the behaviour
// worth pinning — a silent regression here costs the next reader the whole
// "why does this test fail?" detour the helper was added to prevent.

import { describe, expect, it } from "vitest";

import { fixture } from "./helpers";
import { SCHEMA_VERSION } from "../wireValidate";

import listMinJson from "./list_min.snapshot.json";

describe("fixture()", () => {
  it("returns the validated snapshot for a good payload", () => {
    expect(fixture(listMinJson).meta.schema).toBe(SCHEMA_VERSION);
  });

  it("keeps the underlying wire error and appends the re-bless procedure", () => {
    // Computed, not a literal: a literal stale version silently stops being
    // stale the moment SCHEMA_VERSION reaches it.
    const stale = {
      ...listMinJson,
      meta: { ...listMinJson.meta, schema: SCHEMA_VERSION - 1 },
    };
    expect(() => fixture(stale)).toThrow(/meta\.schema/);
    expect(() => fixture(stale)).toThrow(/regen-fixtures\.sh/);
  });
});

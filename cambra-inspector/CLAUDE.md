# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this directory — the inspector's `web/` frontend and its golden-fixture corpus. The Rust half lives in the `cambra` crate at `src/inspector_model/` and `src/inspector_server/`.

## The golden fixtures

`web/src/__fixtures__/*.snapshot.json` are full `/api/snapshot` payloads for the
corpus in `scripts/fixtures.manifest` — shared by the regen script, the
`ci_fixtures` byte gate, and `tests/inspector_goldens.rs`. Re-bless via:

```bash
cambra-inspector/scripts/regen-fixtures.sh   # from the repo root
```

**Re-bless discipline:** classify every diff into a named, explained class
before committing — id renumbering vs label rename vs structural change —
and state the classes in the commit message. A diff you cannot explain is a
bug, not a re-bless: stop and investigate. `NodeId` is a process-global mint
counter, so anything shifting upstream mint *counts* renumbers every later id
and rewrites the whole corpus; that diff is expected and still has to be named
as that.

**What a re-bless pins, beyond the shape.** Each node's `type` is `Display for
Type`'s rendering — `src/ccl/ty.rs`'s `Serialize` hands `collect_str` that
string — so the corpus pins the type notation on every node in every pane. A
literal's singleton spelling is part of that. Changing any of the notation is a
deliberate corpus-wide re-bless.

## Frontend

- **Never run `npm run dev`** — it starts a Vite server that does not exit.
  `typecheck` / `test` / `build` (from `web/`) are all one-shot.
  `cambra --inspect-only` also blocks forever; for scripted inspection use
  `--dump-snapshot`.
- `web/dist/index.html` is **committed and embedded** at compile time. After
  changing anything under `web/src/`, rerun `npm run build` and commit the
  regenerated bundle — the `ci_web` gate compares it against a fresh build.

## Wire-shape changes

The Rust validator (`src/inspector_server/wire_check.rs`) and the TypeScript
validator (`web/src/wireValidate.ts`) assert the same contract and are always
updated together. A schema change means: update both validators, regenerate fixtures
(classified), rebuild the bundle.

`SCHEMA_VERSION` stays at 1 through all of it. Nothing durable consumes the
payload — this frontend is rebuilt from this repo — so a breaking change costs
no version until a consumer exists that an old version could reach. What a bump
means once one does: `src/inspector_model/design.md`, "The schema version".

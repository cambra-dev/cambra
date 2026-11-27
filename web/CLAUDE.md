# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this directory — the inspector's `web/` frontend and its tests. The Rust half lives in the `cambra` crate at `src/inspector_model/` and `src/inspector_server/`.

## The tests' payloads

The tests read the `/api/snapshot` payload of every gallery program
(`tests/programs/`), dumped fresh before they run: vitest's global setup
(`src/__fixtures__/dumps.ts`) runs `write_gallery_snapshots` in
`tests/it/inspector_wire.rs` through `cargo test`. `CAMBRA_SNAPSHOT_PROFILE`
names the cargo profile to dump with; unset, it is the default test profile.
A test reads a payload with `dumped("<program>")` from `src/__fixtures__/helpers.ts`.

A test keys on what a payload means, such as pane ids, node labels and types, and
never on a `NodeId`: ids come from a process-global counter and carry no meaning
across compiler changes. Each node's `type` is `Display for Type`'s rendering
(`src/ccl/ty.rs`), so a test that asserts a type asserts that notation.

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
updated together. A schema change means: update both validators and `src/types.ts`,
then rebuild the bundle.

`SCHEMA_VERSION` stays at 1 through all of it. Nothing durable consumes the
payload — this frontend is rebuilt from this repo — so a breaking change costs
no version until a consumer exists that an old version could reach. What a bump
means once one does: `src/inspector_model/design.md`, "The schema version".

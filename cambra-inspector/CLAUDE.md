# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this directory (the `cambra-inspector` crate and its `web/` frontend).

## Golden fixtures & the two ratchets

Two independent pinned-expectation suites exist, often moved by the same
provenance-affecting compiler change. If your change moves one, check the other.

1. **Wire fixtures** — `web/src/__fixtures__/*.snapshot.json`: full
   `/api/snapshot` payloads for the corpus in `scripts/fixtures.manifest`
   (shared by the regen script, the `ci_fixtures` byte gate, and
   `tests/goldens.rs`). Re-bless via:

   ```bash
   cambra-inspector/scripts/regen-fixtures.sh   # from the repo root
   ```

2. **Census ratchet** — `census_ratchet` in `src/ccl/context.rs` (core crate):
   pins per-category source-attribution counts per pane for its own corpus.
   Its re-bless procedure lives in its doc comment.

**Re-bless discipline (both ratchets):** classify every diff into a named,
explained class before committing — for fixtures, e.g. id renumbering vs label
rename vs structural change, stated in the commit message; for census rows, a
comment on the changed row naming the responsible pass and the shift. A diff
you cannot explain is a bug, not a re-bless — stop and investigate.

## Frontend

- **Never run `npm run dev`** — it starts a Vite server that does not exit.
  `typecheck` / `test` / `build` (from `web/`) are all one-shot. The
  `cambra-inspector` server binary also blocks forever; for scripted
  inspection use `--dump-snapshot`.
- `web/dist/index.html` is **committed and embedded** at compile time. After
  changing anything under `web/src/`, rerun `npm run build` and commit the
  regenerated bundle — the `ci_web` gate compares it against a fresh build.

## Wire-shape changes

The Rust validator (`src/lib.rs` test_support) and the TypeScript validator
(`web/src/wireValidate.ts`) assert the same contract and are always updated
together. A schema change means: bump `SCHEMA_VERSION`, update both
validators, regenerate fixtures (classified), rebuild the bundle.

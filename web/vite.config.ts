import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

import { defineConfig, type Plugin } from "vite";
import { viteSingleFile } from "vite-plugin-singlefile";

const NOTICE = fileURLToPath(new URL("../NOTICE", import.meta.url));

/**
 * The bundle states the licence of what it embeds.
 *
 * `dist/index.html` is committed and embedded in the binary, so it is an
 * object-code distribution of elkjs, and EPL-2.0 §3.2 requires that
 * distribution to name the licence and say where the source is. The
 * repository's `NOTICE` is the one copy of that text; this puts it in the one
 * file that travels without the repository around it. An HTML comment rather
 * than a JS banner, because the notice has to survive minification and be
 * readable in the file a reader opens.
 */
function notice(): Plugin {
  return {
    name: "cambra:notice",
    transformIndexHtml: {
      order: "post",
      handler: (html: string) => `<!--\n${readFileSync(NOTICE, "utf8").trim()}\n-->\n${html}`,
    },
  };
}

// Single-file build: everything (JS + CSS) is inlined into one
// `dist/index.html` with zero external requests, so the server can embed it
// via `include_str!` and `cargo build` needs no Node toolchain (R7).
export default defineConfig({
  plugins: [notice(), viteSingleFile()],
  build: {
    target: "es2022",
    cssCodeSplit: false,
    assetsInlineLimit: 100_000_000,
    chunkSizeWarningLimit: 100_000_000,
    reportCompressedSize: false,
  },
});

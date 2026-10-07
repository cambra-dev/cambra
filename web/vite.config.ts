import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

import { defineConfig, type Plugin } from "vite";
import { viteSingleFile } from "vite-plugin-singlefile";

const NOTICE = fileURLToPath(new URL("../NOTICE", import.meta.url));
// The licence elkjs ships, so the text in the bundle is the installed version's.
const EPL = fileURLToPath(new URL("./node_modules/elkjs/LICENSE.md", import.meta.url));

/**
 * The bundle states the licence of what it embeds.
 *
 * `dist/index.html` is committed and embedded in the binary, so it is an
 * object-code distribution of elkjs. EPL-2.0 §3.1(a) requires that
 * distribution to state that the Source Code is available under the EPL and
 * how to obtain it, and §3.3 forbids dropping the notices elkjs carries, which
 * minification strips. The repository's `NOTICE` holds both; this puts it, with
 * the licence text, in the one file that travels without the repository around
 * it. An HTML comment rather than a JS banner, because the notice has to
 * survive minification and be readable in the file a reader opens.
 */
function notice(): Plugin {
  return {
    name: "cambra:notice",
    transformIndexHtml: {
      order: "post",
      handler: (html: string) => {
        const text = `${readFileSync(NOTICE, "utf8").trim()}\n\n${readFileSync(EPL, "utf8").trim()}`;
        // An HTML comment ends at the first `-->`, after which the rest of the
        // notice would parse as page content.
        if (text.includes("-->")) throw new Error("NOTICE or the EPL text contains `-->`");
        return `<!--\n${text}\n-->\n${html}`;
      },
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

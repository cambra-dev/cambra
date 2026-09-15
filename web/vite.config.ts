import { defineConfig } from "vite";
import { viteSingleFile } from "vite-plugin-singlefile";

// Single-file build: everything (JS + CSS) is inlined into one
// `dist/index.html` with zero external requests, so the server can embed it
// via `include_str!` and `cargo build` needs no Node toolchain (R7).
export default defineConfig({
  plugins: [viteSingleFile()],
  build: {
    target: "es2022",
    cssCodeSplit: false,
    assetsInlineLimit: 100_000_000,
    chunkSizeWarningLimit: 100_000_000,
    reportCompressedSize: false,
  },
});

// The embedding contract, against the built WebAssembly module.
//
// The same scenario `tests/embed.rs` runs natively — compile, push, tick, read,
// frame — so a divergence here is the wasm wrapper's, not the program's. Run it
// through `scripts/build-wasm.sh`, which produces the `pkg/` this imports.
//
// Exits non-zero on the first failed expectation, and prints the measurements
// the demo's budget depends on: compile time, per-row time, and module size.

import { readFileSync, statSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const repo = join(here, "..");
const { init_panic_hook, Program } = await import(join(here, "pkg", "cambra.js"));

let failures = 0;
function check(what, ok, detail = "") {
  if (ok) {
    console.log(`  ok   ${what}${detail ? ` — ${detail}` : ""}`);
  } else {
    console.error(`  FAIL ${what}${detail ? ` — ${detail}` : ""}`);
    failures += 1;
  }
}

const dir = join(repo, "tests", "programs", "asset_cart");
const source = readFileSync(join(dir, "v0.cambra"), "utf8");
const channels = JSON.parse(readFileSync(join(dir, "channels.json"), "utf8")).channels;

init_panic_hook();

const compileStart = Date.now();
const program = Program.compile("v0.cambra", source, channels);
const compileMs = Date.now() - compileStart;
console.log(`compile: ${compileMs} ms`);

const snapshot = JSON.parse(program.snapshot());
check("the snapshot is a program payload", snapshot.meta.payloadKind === "program");
check("every compiler pane is present", snapshot.panes.length === 7, `${snapshot.panes.length} panes`);

const SCALE = 100_000_000;

/** Tick until the sinks answer. A reader fires a tick or more after its write. */
function settle() {
  for (let i = 0; i < 8; i += 1) {
    const result = program.tick();
    if (result.outputs.length > 0) return result;
  }
  return { outputs: [], produced: false, done: false };
}

function push(source, rows) {
  program.push(source, rows);
  return settle();
}

check("a cart change alone serves no view", push("cart_changes", [{ ticker: "BTC-USD", qty: 2 }]).outputs.length === 0);
push("price_updates", [{ ticker: "BTC-USD", price: 81_692 * SCALE }]);
push("price_updates", [{ ticker: "DOGE-USD", price: 100 }]);

const served = push("view_requests", [true]);
const sinks = served.outputs.map((o) => o.sink);
check("a view request serves every line", JSON.stringify(sinks) === '["btc_line","eth_line","sol_line"]', sinks.join(","));

const btc = served.outputs.find((o) => o.sink === "btc_line")?.rows[0];
check("the cart is priced", btc?.qty === 2 && btc?.price === 81_692 * SCALE && btc?.total === 2 * 81_692 * SCALE, JSON.stringify(btc));

const frame = JSON.parse(program.frame(false));
check("the frame records operators", frame.nodes.length > 0, `${frame.nodes.length} nodes`);
const windows = frame.sources.map((s) => s.name).sort();
check("every source the program reads reports a window", JSON.stringify(windows) === '["cart_changes","price_updates","view_requests"]', windows.join(","));
check("a source the program never reads is absent", !windows.includes("stdin"));

let rejected = false;
try {
  program.push("price_updates", [{ ticker: "BTC-USD" }]);
} catch (e) {
  rejected = String(e).includes("missing field 'price'");
}
check("a row missing a declared field is rejected", rejected);

// Throughput against the recorded feed's 2.33 rows/s — a row has ~430 ms.
const feed = ["BTC-USD", "ETH-USD", "SOL-USD", "DOGE-USD", "XRP-USD"];
const ROWS = 40;
const throughputStart = Date.now();
for (let i = 0; i < ROWS; i += 1) {
  program.push("price_updates", [{ ticker: feed[i % feed.length], price: (100 + i) * SCALE }]);
  program.tick();
}
const perRowMs = (Date.now() - throughputStart) / ROWS;
console.log(`per price row: ${perRowMs.toFixed(1)} ms`);
check("the program keeps up with the feed", perRowMs < 430, `${perRowMs.toFixed(1)} ms against a 430 ms budget`);

const bytes = statSync(join(here, "pkg", "cambra_bg.wasm")).size;
console.log(`module: ${(bytes / 1024 / 1024).toFixed(2)} MB`);
check("the module stays under 8 MB", bytes < 8 * 1024 * 1024, `${(bytes / 1024 / 1024).toFixed(2)} MB`);

if (failures > 0) {
  console.error(`\n${failures} check(s) failed`);
  process.exit(1);
}
console.log("\nwasm contract: all checks passed");

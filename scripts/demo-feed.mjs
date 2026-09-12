#!/usr/bin/env node
// DEMO SCAFFOLDING — NOT FOR MAIN.
//
// A stand-in for the language-level socket channel. `demo_code_syntax.md`
// specifies the real shape as `wasm_socket_subscribe(url, channel, products)`,
// a channel the host connects and decodes — native builds with `tungstenite`,
// the page with the browser's own WebSocket. Until that builtin lands there is
// no way to feed `price_updates()` from a live market under `cambra --inspect`,
// because the binary's only ingress is the JSON-lines dev driver on stdin
// (`src/host_driver.rs`). This bridges the two so the inspector can be watched
// against real prices. Delete it when the builtin lands; do not build on it,
// and do not put it on a presentation path — `vault/projects/storefront-demo/
// demo-project.md` rules the native CLI out as one.
//
//   node scripts/demo-feed.mjs | cargo run -- --inspect tests/programs/asset_cart/v0.cambra
//
//   --replay [path]  replay the recorded slice instead of connecting
//   --speed N        replay rate multiplier (default 1)
//   --qty SPEC       seed quantities, e.g. BTC-USD=2,ETH-USD=3 (default), or ""
//
// Rows are `{ticker, price}` with price in dollars × 10^8, matching
// `tests/programs/asset_cart/channels.json`.

import { createReadStream } from "node:fs";
import { createGunzip } from "node:zlib";
import { createInterface } from "node:readline";

/** Dollars × 10^8 — the scale every price crosses a channel in. */
const SCALE = 100_000_000;

/** The 20-product basket the recorded slice was captured over. */
const PRODUCTS = [
  "BTC-USD", "ETH-USD", "SOL-USD", "XRP-USD", "DOGE-USD", "ADA-USD", "AVAX-USD",
  "LINK-USD", "DOT-USD", "LTC-USD", "BCH-USD", "UNI-USD", "AAVE-USD", "ATOM-USD",
  "NEAR-USD", "APT-USD", "ARB-USD", "OP-USD", "SUI-USD", "HBAR-USD",
];

/** The tickers `v0.cambra` keeps a slot and a sink for. */
const TRACKED = new Set(["BTC-USD", "ETH-USD", "SOL-USD"]);

// The thinned capture, which lives in the vault repo beside this one rather
// than in it: it is demo data, and 83 KB of it. `--replay <path>` takes the raw
// capture under `demo-data/` too — replay reads both shapes.
const DEFAULT_SLICE =
  "../../vault/projects/storefront-demo/data/coinbase-2026-09-03-30min.ndjson.gz";

/**
 * A decimal price string as an integer of 10^-8 dollars, exactly.
 *
 * String arithmetic rather than `parseFloat(s) * SCALE`, which is not exact:
 * `parseFloat("0.07948") * 1e8` is 7947999.999999999. The same conversion as
 * the deck's `scalePrice`, and the reason both refuse a price with more than
 * eight decimal places rather than rounding one.
 */
function scalePrice(decimal) {
  const negative = decimal.startsWith("-");
  const body = negative ? decimal.slice(1) : decimal;
  const [whole, fraction = ""] = body.split(".");
  const digits = String(SCALE).length - 1;
  if (fraction.length > digits) {
    throw new Error(`price ${decimal} carries more than ${digits} decimal places`);
  }
  const scaled = Number(`${whole}${fraction.padEnd(digits, "0")}`);
  if (!Number.isSafeInteger(scaled)) {
    throw new Error(`price ${decimal} does not scale to a safe integer`);
  }
  return negative ? -scaled : scaled;
}

/** One host event, as the dev driver reads it. */
function emit(source, rows) {
  process.stdout.write(`${JSON.stringify({ source, rows })}\n`);
}

/**
 * Feed one quote onward.
 *
 * A view request follows a price only for a ticker the cart holds a line for:
 * the program serves every line on every request, so requesting one per row of
 * the other seventeen products would redraw the whole cart for a row it
 * ignores. This is what `CartDemo.vue` does in the page.
 */
function onTick(ticker, price) {
  emit("price_updates", [{ ticker, price }]);
  if (TRACKED.has(ticker)) emit("view_requests", [true]);
}

function seedQuantities(spec) {
  if (spec === "") return;
  const rows = spec.split(",").map((pair) => {
    const [ticker, qty] = pair.split("=");
    return { ticker, qty: Number(qty) };
  });
  for (const row of rows) emit("cart_changes", [row]);
}

/**
 * One recorded line as a quote, or `null` for a line carrying none.
 *
 * Two shapes, because there are two captures: `postprocess.py`'s thinned slice
 * is `{t, p, px, …}`, and `capture.mjs`'s raw one wraps the exchange's own
 * message as `{t, m}`, where only `type: "ticker"` carries a price.
 */
function quoteOf(row) {
  if (row.m !== undefined) {
    const m = row.m;
    return m.type === "ticker" && m.product_id && m.price
      ? { ticker: m.product_id, price: m.price }
      : null;
  }
  return row.p && row.px ? { ticker: row.p, price: row.px } : null;
}

async function replay(path, speed) {
  const stream = createReadStream(path);
  stream.on("error", (e) => {
    process.stderr.write(
      `demo-feed: cannot read ${path}: ${e.message}\n` +
        "demo-feed: pass one with --replay <path>, or drop --replay to go live\n",
    );
    process.exit(1);
  });
  const lines = createInterface({
    input: stream.pipe(createGunzip()),
    crlfDelay: Infinity,
  });
  const started = Date.now();
  // Taken from the first line rather than assumed zero: the thinned slice
  // stamps an offset from the capture's start, the raw one a wall clock.
  let origin;
  for await (const line of lines) {
    if (line === "") continue;
    const row = JSON.parse(line);
    origin ??= row.t ?? 0;
    const quote = quoteOf(row);
    if (quote === null) continue;
    const due = started + ((row.t ?? 0) - origin) / speed;
    const wait = due - Date.now();
    if (wait > 0) await new Promise((resolve) => setTimeout(resolve, wait));
    onTick(quote.ticker, scalePrice(quote.price));
  }
}

function live() {
  const socket = new WebSocket("wss://ws-feed.exchange.coinbase.com");
  socket.onopen = () =>
    socket.send(
      JSON.stringify({
        type: "subscribe",
        channels: [{ name: "ticker_batch", product_ids: PRODUCTS }],
      }),
    );
  // Only `ticker`; a subscription ack and a heartbeat carry no price.
  socket.onmessage = (event) => {
    const message = JSON.parse(event.data);
    if (message.type !== "ticker" || !message.product_id || !message.price) return;
    onTick(message.product_id, scalePrice(message.price));
  };
  socket.onerror = (e) => process.stderr.write(`demo-feed: socket: ${e.message ?? e}\n`);
  socket.onclose = (e) => {
    process.stderr.write(`demo-feed: closed ${e.code} ${e.reason}\n`);
    process.exit(0);
  };
}

const argv = process.argv.slice(2);
const flag = (name, fallback) => {
  const at = argv.indexOf(name);
  if (at === -1) return fallback;
  const value = argv[at + 1];
  return value === undefined || value.startsWith("--") ? "" : value;
};

seedQuantities(flag("--qty", "BTC-USD=2,ETH-USD=3"));

if (argv.includes("--replay")) {
  const path = flag("--replay", "") || new URL(DEFAULT_SLICE, import.meta.url).pathname;
  await replay(path, Number(flag("--speed", "1")) || 1);
} else {
  live();
}

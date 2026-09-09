Both agents are back. Two findings changed the design:

- **`for req, resp in ...` does not exist.** The real form is `reqs, resps = http_serve(port, method, path)` with `resps << body`, special-cased to a top-level tuple destructure. I gave `wasm_serve` the same shape minus the port.
- **`asset_cart/mod.rs`'s claim that "a reply from a loop that also writes never fires" is unsubstantiated** — no test pins it, and `http_counter/program.cambra` passes doing exactly that. Spec §8.4 plus `spine_write_commits_beside_false_guard` give the working shape: bare `if` guards the state writes, the reply sits on the block's spine so `commit = p ∨ true` fires it either way, and a spine re-read gives read-your-writes on the success path.

---

## v1 — hardcoded, single unit

```python
# TODO star star / exp operator
one_btc = 10**8
one_dollar = 10**8        # microcents; matches the feed's existing 10^8 scale

# TODO alias types, refinement predicates
AccountId = Int
Microcents = Int
Balance = {Microcents where  _ > 0}
Ticker = String

accts: Mut(Map(AccountId, Balance), Txn) = (
  (1, 500 * one_dollar)
)

# TODO tuple keys in maps
# NOTE: `, Txn` added — checkout credits this inside a transaction, and an
# induction `Mut` may not be written inside a `with begin():` block.
holdings: Mut(Map({AccountId, Ticker}, Int), Txn) = map(
  [((1, "BTC"), 2 * one_btc)]
)

# --- cart ------------------------------------------------------------------

# A pending quantity per (account, ticker), in the asset's base units — the
# same units `holdings` carries. A checkout drains it; a PATCH sets one line.
# TODO tuple keys in maps
cart: Mut(Map({AccountId, Ticker}, Int), Txn) := box(map([]))

# The last price the feed quoted, in Microcents per *whole* unit. Written by
# the `ticker_updates` loop at the foot of this file, read by checkout inside
# the transaction that spends the cash, so a quote and a debit share a snapshot.
prices: Mut(Map(Ticker, Microcents), Txn) := box(map([]))

# --- endpoints -------------------------------------------------------------

# `wasm_serve(method, path)` is `http_serve`'s shape without the port: the
# embedding page is the listener, so there is nothing to bind. Each call binds
# a host-channel pair registered under (method, path), and rows cross as
# declared record types rather than strings — which is why nothing below parses
# a body. Row types, declared by the host:
#   PATCH /cart      {account: Int, ticker: String, qty: Int}
#                 -> {ok: Bool, ticker: String, qty: Int}
#   PUT   /checkout  {account: Int}
#                 -> {ok: Bool, due: Microcents, cash: Microcents}
#   GET   /cart      {account: Int}
#                 -> {cash: Microcents, lines: [...], positions: [...]}
cart_changes,  cart_change_acks = wasm_serve("PATCH", "/cart")
checkout_reqs, checkout_acks    = wasm_serve("PUT",   "/checkout")
view_requests, view_replies     = wasm_serve("GET",   "/cart")

for c in cart_changes:
    with begin():
        # The deny idiom: a bare `if` with no `else`. A quantity that is not a
        # sane count of base units contributes no write, and this path does not
        # commit.
        if c.qty >= 0:
            cart[(c.account, c.ticker)] := c.qty
        # On the spine beside the guard, so the ack commits either way
        # (`commit = p or true`) and the page always hears back. It has to sit
        # inside the block: a sibling feed after the block may not read a
        # `Mut(_, Txn)`.
        cart_change_acks << (ok=(c.qty >= 0), ticker=c.ticker, qty=c.qty)

for r in checkout_reqs:
    with begin():
        cash = accts[r.account]
        # Every pending line, priced at the latest quote. `one_btc` is the
        # divisor for every asset — the fixed-scale assumption v2 unwinds.
        # TODO entry iteration (`for k -> v in m`) is [Planned], unparsed
        # TODO a comprehension over a transactional map is [Decided], unparsed
        # TODO a bare `m[k]` needs `FullMap`; today it is `m[k]?` plus `match`
        due = sum([q * prices[t] // one_btc
                   for (a, t) -> q in cart if a == r.account])
        # One guard over three keyed writes: the debit, the credit and the
        # drain commit together or not at all. This is the atomicity claim.
        if cash >= due:
            accts[r.account] := cash - due
            # TODO a `for` inside `with begin():` is not accepted today — a
            # TODO block takes writes, bindings, `if`, `match` and feeds only
            for (a, t) -> q in cart if a == r.account:
                holdings[(a, t)] := holdings[(a, t)] + q
                cart[(a, t)] := 0
        # Read-your-writes: the debited balance on the committing path, the
        # untouched one on the denied path.
        remaining = accts[r.account]
        checkout_acks << (ok=(cash >= due), due=due, cash=remaining)

for v in view_requests:
    with begin():
        # A read-only block, so the reply stays inside it: that is what pins
        # every line, every position and the cash to one commit snapshot.
        # TODO the record-of-list sink row is P3; today this is one sink per
        # TODO ticker, which is why `cart.cambra` has btc_line/eth_line/sol_line
        view_replies << (
            cash = accts[v.account],
            lines = [(ticker=t, qty=q, price=prices[t],
                      total=q * prices[t] // one_btc)
                     for (a, t) -> q in cart if a == v.account],
            positions = [(ticker=t, qty=q)
                         for (a, t) -> q in holdings if a == v.account],
        )

# --- feed ------------------------------------------------------------------

# The host's websocket, in the same shape as a host source: it connects, sends
# the subscription, decodes each message and pushes one typed row per quote —
# so no JSON parsing or string splitting happens in Cambra, which the design
# notes reject on principle. Native builds do this with `tungstenite`; the page
# uses the browser's own WebSocket, and the recorded slice replays into the
# same channel offline. Arguments are compile-time constants, as `http_serve`'s
# are. Rows carry the bare ticker ("BTC"), not the product id.
#   -> {ticker: String, price: Microcents}
ticker_updates = wasm_socket_subscribe(
    "wss://ws-feed.exchange.coinbase.com",
    "ticker_batch",
    ["BTC-USD", "ETH-USD", "SOL-USD"],
)

for u in ticker_updates:
    with begin():
        prices[u.ticker] := u.price
```

## v2 — the `_rescaled` upgrade

```python
# A map, not a record: `one_map[h.ticker]` looks a key up that is only known at
# runtime, and a record's fields are fixed at compile time. `{...}` is type
# syntax, so it could not have been a brace literal either. Keys are the ticker
# strings the feed and `holdings` already use, plus "CASH" for the balance.
# TODO map literals `[k -> v, ...]` are [Decided] but unparsed; `map([...])` is
# TODO the constructor that parses today
# TODO annotate `FullMap(Ticker, Int)` to make the unchecked lookups below
# TODO total — a bare `m[k]` on a `Map` is rejected, `FullMap` is what admits it
one_map = map([
    ("BTC",  10**8),      # satoshi
    ("CASH", 10**8),      # microcents, matching v1's one_dollar
    ("ETH",  10**18),     # wei -- TODO: a holding over ~9.2 ETH overflows Int64
    ("SOL",  10**9),      # lamport
])

# TODO alias types
AccountId = Int
Microcents = Int
Ticker = String
ScaledQuantity = {qty: Int, scale: Int}

# TODO LoadFrom
@LoadFrom(accts)
accts_ro: {id: Int, cash: Microcents}

accts_rescaled: Mut(Map(AccountId, Microcents), Txn) = (
  (cash, one_map[CASH])
  for cash in accts_ro
)

# Keyed off (id, ticker)
@LoadFrom(holdings)
holdings_ro: Map({AccountId, Ticker}, Int)

# TODO tuple keys in maps
holdings_rescaled: Mut(Map({AccountId, Ticker}, ScaledQuantity) := [
  (h.amount, one_map[h.ticker]) # TODO unchecked lookup
  for h in holdings_ro
]

# --- cart ------------------------------------------------------------------

# The cart carries its own scale for the same reason `holdings_rescaled` does:
# pricing a line now divides by the asset's scale, not by one fixed constant.
# TODO tuple keys in maps
# TODO a record in a `Map` value position is unproven — `map`'s codomain has
# TODO only ever been driven as a scalar column
cart_rescaled: Mut(Map({AccountId, Ticker}, ScaledQuantity), Txn) := box(map([]))

# Prices stay in Microcents per whole unit — the quote side did not rescale,
# only the quantity side did.
prices: Mut(Map(Ticker, Microcents), Txn) := box(map([]))

# --- endpoints -------------------------------------------------------------

# Identical routes and identical row types to v1, so nothing outside the
# program moves: the page's PATCH still carries a plain integer count of base
# units, and the program stamps the scale on it from `one_map`.
cart_changes,  cart_change_acks = wasm_serve("PATCH", "/cart")
checkout_reqs, checkout_acks    = wasm_serve("PUT",   "/checkout")
view_requests, view_replies     = wasm_serve("GET",   "/cart")

for c in cart_changes:
    with begin():
        if c.qty >= 0:
            # The runtime lookup this whole migration exists for.
            cart_rescaled[(c.account, c.ticker)] := (
                qty = c.qty,
                scale = one_map[c.ticker],
            )
        cart_change_acks << (ok=(c.qty >= 0), ticker=c.ticker, qty=c.qty)

for r in checkout_reqs:
    with begin():
        cash = accts_rescaled[r.account]
        # The one line that differs from v1: the divisor came off the line
        # instead of being `one_btc` for everything.
        # TODO entry iteration, map comprehension, bare `m[k]` — as v1
        due = sum([line.qty * prices[t] // line.scale
                   for (a, t) -> line in cart_rescaled if a == r.account])
        if cash >= due:
            accts_rescaled[r.account] := cash - due
            # TODO a `for` inside `with begin():` is not accepted today
            for (a, t) -> line in cart_rescaled if a == r.account:
                holdings_rescaled[(a, t)] := (
                    qty = holdings_rescaled[(a, t)].qty + line.qty,
                    scale = line.scale,
                )
                cart_rescaled[(a, t)] := (qty = 0, scale = line.scale)
        remaining = accts_rescaled[r.account]
        checkout_acks << (ok=(cash >= due), due=due, cash=remaining)

for v in view_requests:
    with begin():
        # TODO the record-of-list sink row is P3
        # TODO the denomination note wants these display-ready rather than
        # TODO (value, scale) pairs, which needs `str()` and a padding primitive
        view_replies << (
            cash = accts_rescaled[v.account],
            lines = [(ticker=t, qty=line.qty, scale=line.scale,
                      price=prices[t],
                      total=line.qty * prices[t] // line.scale)
                     for (a, t) -> line in cart_rescaled if a == v.account],
            positions = [(ticker=t, qty=h.qty, scale=h.scale)
                         for (a, t) -> h in holdings_rescaled if a == v.account],
        )

# --- feed ------------------------------------------------------------------

ticker_updates = wasm_socket_subscribe(
    "wss://ws-feed.exchange.coinbase.com",
    "ticker_batch",
    ["BTC-USD", "ETH-USD", "SOL-USD"],
)

for u in ticker_updates:
    with begin():
        prices[u.ticker] := u.price
```

---

### What the wasm spoofs need (not edited — `cambra-site/` is off limits)

- `public/wasm/channels.json` — the three `source` entries become three route-shaped request/response pairs keyed by `(method, path)`, and `price_updates` becomes the socket source. The three `*_line` sinks collapse into `view_replies`.
- `demo/transport.ts` — `push(source, rows)` gains a request/response form so a PATCH/PUT/GET can be paired with its reply; `TRACKED`/`LINE_SINKS` go away.
- `demo/feed.ts` — `LiveFeed` stops calling `push("price_updates", …)` and instead backs `wasm_socket_subscribe`; `ReplayFeed` remains the offline stand-in on the same channel. Both should emit the bare ticker (`"BTC"`), since that is the key `holdings` and `one_map` use.
- `components/CartDemo.vue` — `setQuantity` → PATCH, a new checkout control → PUT, `refresh` → GET, and one `view_replies` subscription in place of three per-ticker sinks.

### Outside `TODO(now)`, but these will not work as written

I left them alone except where my code required the change:

1. `accts` and `holdings` use `=`; a `Mut` declaration needs `:=`. A plain `=` inside a block is rejected with "`=` binds immutably — a plain `=` here is a no-op shadow".
2. `holdings` had no `Txn` domain — I added it, because checkout credits it inside a transaction and an induction `Mut` cannot be written there.
3. Both seeds are single-entry. `map([(k, v)])` with one entry is a known panic (`post-lambda-elim produced an invalid tree`, pinned `should_panic`); seed two entries. Empty `map([])`, which the cart and prices use, is unverified rather than known-broken.
4. `holdings_rescaled` is missing a closing paren on its annotation, and its comprehension uses `[...]` where the value is a pair.
5. `accts_rescaled` is annotated `Map(AccountId, Microcents)` but its body builds `(cash, one_map[CASH])` — a pair. I wrote checkout against the annotation (a plain Int in microcents). `for cash in accts_ro` also binds a whole `{id, cash}` record, not the cash field, and nothing produces the key.

One semantics point I could not pin down from the tests: a feed on the block's **spine** beside a failing guard. `spine_write_commits_beside_false_guard` proves a spine *write* commits (`commit = p ∨ true`), and §8.4 says an in-block feed rides the commit — so the ack should fire on the denied path. No test covers a spine feed specifically, and `txn_multi_read` has a live bug in the fed-out read path. Worth a probe before the beat depends on it.

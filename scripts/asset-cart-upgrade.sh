#!/usr/bin/env bash
# DEMO SCAFFOLDING — NOT FOR MAIN.
#
# Validate the asset cart's upgrade against the real binary: run
# `v1_single_line.cambra` under a control port, build a cart in it, replace it with
# `v2_migrating_single_line.cambra`, and check that the state crossed the swap and the new
# arithmetic took effect.
#
#   scripts/asset-cart-upgrade.sh [--post FILE] [--debug] [--control PORT] [--keep]
#
# `asset_cart_single_line_migrates_its_state_to_per_asset_scales` makes the same claims in
# process. This drives the binary instead, so it also covers the paths that test cannot
# reach: the stdin host driver, the control port, and `/reload` over the wire.
#
# `--post` swaps the version to reload; `v2_single_line.cambra` is the other target and
# passes the same checks. `--debug` uses a debug build, which compiles the program an order
# of magnitude slower — the script waits for the control port either way. `--keep` leaves
# the transcript in place and prints its path.
set -uo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${repo}" || exit 1

pre="tests/programs/asset_cart/v1_single_line.cambra"
post="tests/programs/asset_cart/v2_migrating_single_line.cambra"
profile="release"
control=0
keep=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --post) post="$2"; shift 2 ;;
    --pre) pre="$2"; shift 2 ;;
    --control) control="$2"; shift 2 ;;
    --debug) profile="debug"; shift ;;
    --keep) keep=1; shift ;;
    -h|--help) sed -n '2,19p' "${BASH_SOURCE[0]}" | sed 's|^# \?||'; exit 0 ;;
    *) echo "asset-cart-upgrade: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

say() { printf '\n\033[1m== %s\033[0m\n' "$*"; }
fail() { printf '\033[31mFAIL\033[0m %s\n' "$*" >&2; exit 1; }

# A port nothing holds. Asking the kernel for one and closing it races with anything else
# doing the same, which is why the program is given the number rather than binding zero.
if [[ "${control}" == "0" ]]; then
  control="$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')"
fi

say "building (${profile})"
if [[ "${profile}" == "release" ]]; then
  cargo build --release --bin cambra || fail "the build failed"
  binary="target/release/cambra"
else
  cargo build --bin cambra || fail "the build failed"
  binary="target/debug/cambra"
fi

work="$(mktemp -d)"
fifo="${work}/feed"
transcript="${work}/transcript.jsonl"
mkfifo "${fifo}"

cleanup() {
  exec 3>&- 2>/dev/null
  kill "${program:-}" 2>/dev/null
  wait "${program:-}" 2>/dev/null
  if [[ "${keep}" == "1" ]]; then
    echo "transcript: ${transcript}"
  else
    rm -rf "${work}"
  fi
}
trap cleanup EXIT INT TERM

say "phase 1 — ${pre} on control port ${control}"
"${binary}" --control="${control}" "${pre}" <"${fifo}" >"${transcript}" 2>"${work}/stderr" &
program=$!
# Holding the write end open is what keeps the run alive: the driver treats end of stdin as
# end of the run and exits about 200 ms later.
exec 3>"${fifo}"

# The control port binds after the first compile, so its answering is the signal that the
# program is up. A fixed sleep is wrong in either build profile.
for _ in $(seq 120); do
  if exec 4<>/dev/tcp/127.0.0.1/"${control}" 2>/dev/null; then
    exec 4>&-
    break
  fi
  kill -0 "${program}" 2>/dev/null || { cat "${work}/stderr" >&2; fail "the program exited before the control port bound"; }
  sleep 1
done
exec 4<>/dev/tcp/127.0.0.1/"${control}" 2>/dev/null || fail "the control port never answered"
exec 4>&-
echo "  up"

# One host event per line, and one line per tick — so a quote commits before the request
# that reads it.
feed() { printf '%s\n' "$1" >&3; sleep 0.4; }

say "phase 2 — a quote and a cart line per account"
feed '{"source":"price_updates","rows":[{"ticker":"BTC","price":100000000000}]}'
feed '{"source":"price_updates","rows":[{"ticker":"ETH","price":200000000000}]}'
feed '{"source":"PATCH /cart","rows":[{"account":1,"ticker":"BTC","qty":100000}]}'
feed '{"source":"PATCH /cart","rows":[{"account":2,"ticker":"ETH","qty":100000}]}'
feed '{"source":"GET /cart","rows":[{"account":1}]}'
feed '{"source":"GET /cart","rows":[{"account":2}]}'

# Both replies open with a summary and then render the whole differing tree, which runs to
# hundreds of lines of IR. The summary is what a check wants; `--keep` holds the transcript
# for the rest.
summary() { grep -E '^(reloaded:|phase |[0-9]+ shared)' | head -n 4; }

say "phase 3 — /diff, then /reload onto ${post}"
curl -s --data-binary "@${post}" "http://127.0.0.1:${control}/diff" | summary
reply="$(curl -s -w '\n%{http_code}' --data-binary "@${post}" "http://127.0.0.1:${control}/reload")"
code="$(tail -n1 <<<"${reply}")"
sed '$d' <<<"${reply}" | summary
[[ "${code}" == "200" ]] || fail "the reload was refused (HTTP ${code}); the running program is untouched"

say "phase 4 — the same views, then a checkout against the migrated state"
feed '{"source":"GET /cart","rows":[{"account":1}]}'
feed '{"source":"GET /cart","rows":[{"account":2}]}'
feed '{"source":"PUT /checkout","rows":[{"account":2}]}'
feed '{"source":"GET /cart","rows":[{"account":2}]}'
sleep 1

say "phase 5 — what crossed the swap"
python3 - "${transcript}" <<'PY'
import json, sys

rows = {}
for line in open(sys.argv[1]):
    line = line.strip()
    if not line:
        continue
    try:
        entry = json.loads(line)
    except json.JSONDecodeError:
        continue
    rows.setdefault(entry["sink"], []).extend(entry["rows"])

views = rows.get("GET /cart", [])
acks = rows.get("PUT /checkout", [])
problems = []

def want(condition, message):
    if not condition:
        problems.append(message)

want(len(views) == 5, f"expected 5 view replies (2 before, 2 after, 1 settled), got {len(views)}")
want(len(acks) == 1, f"expected 1 checkout ack, got {len(acks)}")

if len(views) == 5 and len(acks) == 1:
    btc_before, eth_before, btc_after, eth_after, settled = views
    ack = acks[0]

    # BTC's divisor is satoshis in both versions, so nothing about its line may move. This
    # is the claim that the state crossed the swap.
    want(btc_after == btc_before,
         f"BTC's line moved across the swap:\n    before {btc_before}\n    after  {btc_after}")

    # ETH's becomes gwei, so its total falls by the ratio of the two scales and nothing
    # else about it does. This is the claim that the new code took effect.
    for name in ("cash", "ticker", "qty", "price", "held"):
        want(eth_after[name] == eth_before[name],
             f"the swap changed ETH's {name}: {eth_before[name]} -> {eth_after[name]}")
    want(eth_after["total"] == eth_before["total"] // 10,
         f"ETH's total should be a tenth after the swap: "
         f"{eth_before['total']} -> {eth_after['total']}")

    # The migrated collections are written, not merely read.
    due = eth_after["total"]
    want(ack == {"ok": True, "due": due, "cash": eth_after["cash"] - due},
         f"the checkout should price the migrated line at {due}, got {ack}")
    want(settled["qty"] == 0, f"the line should be cleared, got qty {settled['qty']}")
    want(settled["held"] == eth_after["held"] + eth_after["qty"],
         f"the holding should gain the line's quantity: "
         f"{eth_after['held']} + {eth_after['qty']} != {settled['held']}")
    want(settled["cash"] == eth_after["cash"] - due,
         f"the debit should stand, got cash {settled['cash']}")

    print(f"  before  BTC {btc_before}")
    print(f"  after   BTC {btc_after}")
    print(f"  before  ETH {eth_before}")
    print(f"  after   ETH {eth_after}")
    print(f"  checkout    {ack}")
    print(f"  settled ETH {settled}")

if problems:
    print()
    for problem in problems:
        print(f"  FAIL {problem}")
    sys.exit(1)
print("\n  the state crossed the swap and the new arithmetic took effect")
PY
status=$?

if [[ "${status}" != "0" ]]; then
  echo
  echo "The transcript is ${transcript} — re-run with --keep to hold it."
  keep=1
  fail "the upgrade did not hold"
fi

say "ok"

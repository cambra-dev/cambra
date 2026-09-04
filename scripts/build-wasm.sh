#!/usr/bin/env bash
# Build the WebAssembly module and run the embedding contract against it.
#
# Two tools this repo does not depend on: the `wasm32-unknown-unknown` target
# (named in rust-toolchain.toml, so `rustup` installs it with the toolchain) and
# `wasm-bindgen-cli`, whose version must match the `wasm-bindgen` crate exactly.
# `ci.sh wasm` type-checks the library without either; this produces the module.
#
#   scripts/build-wasm.sh [--target web|nodejs]
#
# `nodejs` (the default) is what `scripts/wasm-contract.mjs` imports. `web` is
# what a page loads.
set -euo pipefail

target="nodejs"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --target)
      target="$2"
      shift 2
      ;;
    *)
      echo "usage: $0 [--target web|nodejs]" >&2
      exit 1
      ;;
  esac
done

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${root}"

if ! command -v wasm-bindgen > /dev/null 2>&1; then
  # The CLI's version must match the crate's exactly, so name the one the lock
  # resolved rather than telling the reader to guess.
  crate_version="$(awk '/^name = "wasm-bindgen"$/{found=1} found&&/^version/{gsub(/[version = "]/,""); print; exit}' Cargo.lock)" || crate_version="the locked version"
  echo "wasm-bindgen not found; install the matching CLI:" >&2
  echo "  cargo install wasm-bindgen-cli --version ${crate_version}" >&2
  exit 1
fi

echo "building the module (wasm-release: size-optimized, stripped)"
cargo build --profile wasm-release --target wasm32-unknown-unknown --lib

out="${root}/scripts/pkg"
rm -rf "${out}"
wasm-bindgen --target "${target}" --out-dir "${out}" \
  "target/wasm32-unknown-unknown/wasm-release/cambra.wasm"

module_size="$(du -h "${out}/cambra_bg.wasm")" || module_size="unknown"
echo "module: ${module_size%%$'\t'*}"

if [[ "${target}" == "nodejs" ]]; then
  echo
  node "${root}/scripts/wasm-contract.mjs"
fi

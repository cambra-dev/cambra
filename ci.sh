#!/usr/bin/env bash
set -euo pipefail

ci_fmt()    { cargo fmt --check; }
# --all-targets lints test code too and warms the cache for cargo test
ci_clippy() { cargo clippy --all-targets -- -D warnings; }
ci_test()   { cargo test; }

ci_all() {
    local failed=0
    ci_fmt    || failed=1
    ci_clippy || failed=1
    ci_test   || failed=1
    exit $failed
}

cmd="${1:-all}"
"ci_${cmd}"

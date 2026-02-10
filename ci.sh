#!/usr/bin/env bash
# Use `set -x` so it's easy to pull out the failing commands.
set -euxo pipefail

ci_fmt() { cargo fmt --check; }
# --all-targets lints test code too and warms the cache for cargo test
ci_clippy() { cargo clippy --all-targets -- -D warnings; }
ci_test() { cargo test; }
ci_shellcheck() { find . -name '*.sh' -not -path './.git/*' -exec shellcheck -a -o all {} +; }

ci_all() {
  local failed=0
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_shellcheck || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_fmt || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_clippy || failed=1
  # shellcheck disable=SC2310
  # intentional: || captures failure without exiting
  ci_test || failed=1
  exit "${failed}"
}

cmd="${1:-all}"
"ci_${cmd}"

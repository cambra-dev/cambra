# formal/

The Lean 4 model of the CCL type system. Plan, milestones, and adjudicated
decisions: [design.md](design.md).

```bash
cd formal
lake build          # library (theorems + #guard spec examples) + the oracle
```

The toolchain is pinned by `lean-toolchain`; `elan` fetches it on first build.

`lake build` also produces `.lake/build/bin/subverdict`, the M1 differential
oracle. The Rust half is an ordinary unit test that skips (loudly) when the
binary is absent:

```bash
cargo test differential_ground_subtype
CAMBRA_DIFF_N=20000 CAMBRA_DIFF_SEED=7 cargo test differential_ground_subtype -- --nocapture
```

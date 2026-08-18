//! Storefront — the north-star operational application, and the intended
//! launch demo.  One program spanning the layers a conventional stack splits
//! across systems: transactional order intake (`/order`, `/restock` mutating
//! a shared refined store), a stream of committed order lines (the `orders`
//! feed), and time-indexed analytics served over HTTP (`/stats`).  The
//! domain rules live in the types instead of tests: the `Qty` refinement
//! (`{Int where _ >= 0}`) makes overselling ill-typed, `ItemPricing`'s record
//! refinement rejects below-cost catalog entries at the literal, `SKU`
//! (keys actually in the catalog) makes `inventory`'s `FullMap` lookups
//! statically hit, and `quote`'s `static assert` makes selling below cost
//! ill-typed — in every version.
//!
//! `v0.cambra` and `v1.cambra` are the two sides of the version-upgrade
//! dimension: V1
//! changes only `quote` (and adds the `is_promo_spent` view) — a
//! budgeted flash sale, half off list until cumulative discount spend
//! exhausts the budget.  `is_promo_spent` is a time-pinned aggregate over the
//! order feed read inside the ordering transaction — a named view the
//! runtime can materialize and maintain incrementally — so pricing depends
//! on transactional history and concurrent orders cannot double-spend the
//! budget; the cost floor stays
//! because the inherited postcondition rejects the naive discount on the
//! low-margin "poster".  The diff between the files is the upgrade;
//! inventory and the order feed persist across the branch point.
//!
//! ### What the orchestration will look like once unblocked
//!
//! One test drives the whole story end to end:
//!
//! 1. Compile and boot V0 on a free port.
//! 2. Drive a mixed workload from client threads: concurrent `/order`
//!    requests (including oversell attempts on one hot SKU and invalid
//!    qty < 0 requests), interleaved `/restock`s, and `/stats` reads.
//! 3. Assert the responses: `http.ok` orders priced by V0's `quote`,
//!    `http.conflict` (409) for oversell attempts — the invariant visibly
//!    holding under load — a boundary rejection for invalid qty (the HTTP
//!    library derives request validation from the handlers' inferred
//!    constraints), and `/stats` snapshots
//!    that are consistent with the orders committed before each read.
//! 4. Upgrade to V1 at a branch point t_new while V0's state persists.
//! 5. Replay the workload; assert post-t_new orders are priced by V1's
//!    budgeted `quote` — half off while the promotion budget lasts, list
//!    price once it is spent — and that both invariants held across the
//!    upgrade.
//!
//! Steps 4–5 need the versioning surface (`Versioned` dispatch, the
//! branch point `t_new`, branch/merge), which is still open design.
//!
//! ### Current limitations (what this test depends on)
//!
//! **Blocked today**: the `` ` `` prefix on the `` `some ``/`` `none `` variant
//! tags is not lexed (the `\` lambda — the filter predicates — already
//! lexes).  Behind the tag, the `match` expression on the catalog lookup is
//! still not a keyword and derails the layout pass (an inconsistent-
//! indentation lex error).  The full dependency list, each isolated by a
//! smaller gallery program where one exists:
//!
//! - `static assert` lifted to a codomain refinement — `discount_contract`
//!   pins the boundary-assert ancestor of this shape.
//! - Refined transactional store + guarded decrement — `nonneg_inventory`.
//! - Transaction-time views over feeds — `ledger_balance`.
//! - Type-alias statements (`Dollars`/`Qty`/`ItemPricing`/`SKU`), record
//!   refinements (`{… where _.price >= _.cost}`), a value-dependent key type
//!   (`_ in catalog.keys()`), and `FullMap` total lookups — new with the
//!   redesigned example; no isolating gallery program yet.
//! - HTTP-library request validation derived from inferred handler
//!   constraints — open with the rest of the HTTP library design.
//! - Transactions, `Mut(..., Txn)`, `match`/`Option`, structured requests,
//!   `restrict`/`count` — `txn_kv` (the storefront spells restriction
//!   `filter`); v1's `is_promo_spent` additionally uses
//!   `summon(Transaction)` and a time-pinned aggregate inside a
//!   `requires Transaction` UDF, which no smaller program pins.  Its
//!   incremental materialization is the efficiency milestone: the naive
//!   plan rescans order history per quote.
//! - Status-code response constructors (`http.ok`/`http.bad_request`/
//!   `http.not_found`/`http.conflict` over a response record, behind
//!   `import http` — the module surface is decided) — sketched in
//!   the spec's HTTP Direction note; open with the rest of the HTTP library
//!   design (including wire serialization for bare non-String responses —
//!   /stats answers with the revenue map itself), and no isolating program
//!   yet.
//! - `groupby` through operator conversion (`curry`) — `groupby_rollup`;
//!   /stats additionally needs `k -> g` entry-pair iteration of the keyed
//!   result and a map comprehension (`[k -> v for …]`).
//! - Record terms `(f=v)` — `reachability`.
//! - `Feed(...)` annotations — `fanout`.
//! - Version dispatch across a branch point — no isolating program yet
//!   (deferred with the still-open versioning surface).
//!
//! This pins the variant-tag lex failure on both files — the `` ` `` prefix on
//! `` `some ``/`` `none `` (`docs/chl-spec.md`, "6.5 Variants") is not lexed,
//! and it precedes the `match`-block indentation
//! failure behind it.  When the tag lexes, the test goes red and the next
//! blocker gets pinned.

use super::common::expect_compile_error;

#[test]
fn storefront_currently_blocked_at_lexing() {
    expect_compile_error(include_str!("v0.cambra"), "invalid token");
    expect_compile_error(include_str!("v1.cambra"), "invalid token");
}

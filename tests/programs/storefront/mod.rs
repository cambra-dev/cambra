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
//! Steps 4–5 upgrade at a branch point, which is one of two things. Replacing
//! V0 with V1 outright is implemented — the running program's state carries
//! across the swap (`src/ccl/design/hot-reload.md`, "How a reload works"), which
//! is what step 4 asks for and what `hot_reload` demonstrates. Serving both
//! sides of `t_new` at once still needs the versioning surface (`Versioned`
//! dispatch, branch/merge), which is open design.
//!
//! ### Current limitations (what this test depends on)
//!
//! **Blocked today** at the front end, on the membership `in` of `SKU`'s
//! predicate (see the pinned blocker below).  The full dependency list, each
//! isolated by a smaller gallery program where one exists:
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
//! - `k -> g` entry-pair iteration of a keyed `groupby` result and a map
//!   comprehension (`[k -> v for …]`), which /stats needs on top of the
//!   rollup `groupby_rollup` covers.
//! - Record terms `(f=v)` — `reachability`.
//! - `Feed(...)` annotations — `fanout`.
//! - Replacing one version with another — `hot_reload`.
//! - Serving two versions at once across a branch point — no isolating program
//!   yet (deferred with the still-open versioning surface).
//!
//! The variant tags, the refinement braces and the `->` entry pairs of the
//! `catalog` and `inventory` literals all parse now (`docs/chl-spec.md`,
//! "3.15 Variant constructors", "6.4 Refinement syntax" and "2.4 Atoms"), so both
//! files pin the same blocker behind them: `SKU`'s predicate
//! `_ in catalog.keys()` parses only as far as `in`, which is no expression
//! operator.  The parser recovers past each statement, so the same run also
//! reports the other unshipped surfaces listed above — `import`, `static assert`,
//! `requires`, `with begin():` in value position, and the bare annotation
//! `orders: Feed(…)`.
//!
//! `/stats`'s map comprehension over `groupby` parses in both files.  What it
//! still needs is entry iteration: `for key -> g in groupby(…)` binds a pair only
//! once a keyed collection iterates entries (`src/ccl/design/collections.md`,
//! "Telling `Set` and `Map` apart [Open]").

use super::common::expect_compile_error;

#[test]
fn storefront_currently_blocked_in_the_front_end() {
    expect_compile_error(include_str!("v0.cambra"), "_ in catalog.keys()");
    expect_compile_error(include_str!("v1.cambra"), "_ in catalog.keys()");
}

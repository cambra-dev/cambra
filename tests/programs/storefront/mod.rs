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
//! `v0.cambra`, `v1.cambra`, and `v2.cambra` are a version chain, and each
//! diff is an upgrade.  V1
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
//! V2 adds the two capabilities a conventional stack buys separate systems
//! for — durable execution and an ETL-to-warehouse path — and adds two
//! primitives to carry them.  An **outbound call** is the dual of `http.serve`:
//! requests out, results in, paired by a key the program supplies, with the
//! contract that the runtime dispatches at most one call per key and records
//! its result durably before any consumer observes it.  A **deadline** is a
//! source over transactional state: `clock.due(m)` yields a key once its
//! deadline passes, so scheduling is a write and cancelling is a delete.
//!
//! Everything else a workflow engine supplies falls out of those two.  The
//! checkout saga is a per-key state machine over `checkouts`, advanced by one
//! `for` loop per event source; compensation is an ordinary transaction the
//! machine reaches; retry with backoff is a failed result writing a new
//! deadline and re-dispatching under a new attempt key, which needs no loop and
//! so does not wait on `while` lowering.  What durable execution adds over
//! plain durable state is the guarantee that a half-finished process resumes,
//! and that decomposes into the durability of `checkouts` plus the at-most-once
//! call contract, with nothing left over.  `external_call`, `checkout_saga`,
//! and `abandoned_cart` pin those pieces one at a time.
//!
//! The ETL path splits in two, and only one half is a saving.  The mart
//! (`/analytics/daily-revenue`) is a rollup over the same `orders` feed the
//! operational endpoints write, so a conventional pipeline's outbox, topic,
//! consumer, and loader have no counterpart here.  The archive does cross a
//! boundary — retention and cold storage are not met by an in-program view —
//! and `store.parquet` is surface Cambra does not have.  `warehouse_export`
//! pins both halves; `docs/REPORT.md` measures them.
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
//! - `k -> g` entry-pair iteration of a keyed `groupby` result and a map
//!   comprehension (`[k -> v for …]`), which /stats needs on top of the
//!   rollup `groupby_rollup` covers.
//! - Record terms `(f=v)` — `reachability`.
//! - `Feed(...)` annotations — `fanout`.
//! - Version dispatch across a branch point — no isolating program yet
//!   (deferred with the still-open versioning surface).
//!
//! The variant tags and the refinement braces parse now (`docs/chl-spec.md`,
//! "3.15 Variant constructors" and "6.4 Refinement syntax"), so what each file
//! pins is the blocker behind them:
//!
//! - **v0 — map-literal entries are unparsed.**  The first blocker is the `->`
//!   entry pair in the `catalog` literal.  The parser recovers past each
//!   statement, so the same run also reports the other unshipped surfaces listed
//!   above (`static assert`, `requires`, `<<`) and one the refinements exposed:
//!   `SKU`'s predicate `_ in catalog.keys()` parses only as far as `in`, which is
//!   no expression operator.
//! - **v1 and v2 — a layout failure, which lexing hits first.**  `quote` writes a
//!   multi-line `if`/`else` **expression** whose `else:` sits at a shallower
//!   indent than the then-branch body it follows.  The off-side rule dedents to a
//!   level that was never opened and the lexer reports inconsistent indentation.
//!   What is missing is a continuation rule for a bracket-less multi-line
//!   expression: `docs/chl-spec.md`, "1.4 Implicit line continuation" covers only
//!   bracketed forms.  Behind it, v0's map-literal entries and everything else
//!   listed above.  V2 inherits `quote` unchanged, so it is blocked at the same
//!   line; a lex error aborts the run, which is why its own surfaces never
//!   reach a diagnostic and the satellites carry their pins instead.
//!
//! What V2 adds to the dependency list above, none of it reachable today:
//!
//! - The outbound call `http.call(name, method, path)` and its at-most-once
//!   contract — `external_call`.
//! - `clock.due(deadlines)` over a `Mut(Map(K, Time), Txn)` variable, and
//!   map-entry deletion, which has no decided spelling (`del m[k]` here) —
//!   `abandoned_cart`.
//! - `clock.day` and arithmetic on `Time`, which today is a position in the
//!   commit order with no algebra, and the partitioned object-storage sink
//!   `store.parquet` — `warehouse_export`.
//! - A `FullMap` whose key set grows with the program (`checkouts`), which
//!   `docs/chl-spec.md`, "6.3 Direction: collections as functions [Tentative]"
//!   leaves `[Open]` as the construction-site obligation — `checkout_saga`.

use super::common::expect_compile_error;

#[test]
fn storefront_currently_blocked_in_the_front_end() {
    expect_compile_error(include_str!("v0.cambra"), "found '->'");
    expect_compile_error(include_str!("v1.cambra"), "inconsistent indentation");
    expect_compile_error(include_str!("v2.cambra"), "inconsistent indentation");
}

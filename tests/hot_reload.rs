//! Replacing a running program with a new version of its source, against a
//! program that is actually running.
//!
//! # The programs
//!
//! The gallery entry is one program and the version that replaces it:
//! `program.cambra` is a guestbook where `POST /sign` accumulates into a mutable
//! variable and `GET /peek` holds no state, and `reloaded.cambra` is the same
//! program with the accumulating loop edited. That pair is what a reader should
//! look at to see what a reload does.
//!
//! Everything else the cases drive is scaffolding. [`fixtures`] holds the ones
//! that are a program a case names — a base per shape, plus the variants that
//! differ from one by the single edit their case is about. A program a case
//! builds rather than names stays in the case, and there are three reasons to
//! build one: it varies by more than an edit, so a function takes the varying
//! part (`fold_to_main`, `filtered_fold_to_main`, `fold_behind_a_route`,
//! `nested_fold`, `boundary_pair`, `two_instantiations`, `anonymous_sites`); it
//! needs a second port, which `source` does not substitute
//! (`a_port_whose_last_route_goes_is_released`,
//! `a_version_naming_an_unbindable_port_is_refused`); or it is `stdin`-sourced
//! and has no `{PORT}` to substitute at all. The bases:
//!
//! | Base | Shape |
//! | --- | --- |
//! | `guestbook` | The gallery program. One stateful loop, so one `Transact` store with one key; `/peek`'s loop holds nothing. |
//! | `bump-over-source` | The smallest one: `POST /bump` accumulates into `n`. Varied by its declared init, for the rule that a carried value wins over one. |
//! | `record-accumulator` | A record-valued accumulator, varied by the type of one field — a retype no single program can express. |
//! | `bump-over-a-fixed-list` | A fold over `["y", "z"]` read by `POST /bump`. Varied by the body and by the collection, which are the two edits a fold tells apart. |
//! | `two-loops` | `POST /a` and `POST /b` each accumulate into their own variable. Independent, so a store each — one is kept while the other is rebuilt. |
//! | `two-accumulators` | One loop carrying two variables (`left` and `right`), for the cases about telling them apart. |
//! | `one-stateful-loop` | `POST /p` accumulates, `POST /q` does not — the pair a variable can move between. |
//! | `latest-write` | A transactional variable (`Mut(String, Txn)`) that `POST /set` overwrites and `GET /get` reads. |
//! | `running-log` | A transactional variable that `POST /set` appends to, so every commit leaves a mark a replay would show. |
//! | `one-transactional-loop` | `POST /a` commits into a transactional variable, `POST /b` holds nothing — the pair a transactional writer can be added to. |
//! | `two-transactions` | Two transactional variables written and read from disjoint endpoint pairs, so they fall in different causal groups and each gets its own commit store. |
//!
//! The `stdin` cases drive the binary as a subprocess
//! ([`launch_under_control`]), because a `main` output fed by `stdin` belongs to
//! the binary's own loop rather than to a sink a test can pump. Those are also the
//! only cases that reach the control port over HTTP; every other case calls
//! `LiveProgram` directly.
//!
//! Some cases pull a program's value itself instead
//! (`drive_main_to_terminal`). A fold over a fixed collection needs no
//! source, so pulling it is what makes the position a reload lands on nameable:
//! one pull decides one position, where a socket lands wherever the notification
//! round it arrives in reaches.
//!
//! # What a reload may do
//!
//! | Change | Expected |
//! | --- | --- |
//! | Logic outside a store's recurrence | Accepted; the store is kept and its variables are untouched |
//! | Logic inside one | Accepted; the store is rebuilt and each variable resumes from the value it held, so what was recorded stands and the new rule governs from here |
//! | An edit to one of two independent loops | Accepted; the other's store is kept |
//! | A loop gains an accumulator under a new name | Accepted and reported; the others resume, and the new one starts at its init and folds from where the loop has got to, since one loop drives one position sequence |
//! | A route serving statelessly gains a transactional writer | Accepted and reported; the writer commits from the next request, replaying none the route already answered |
//! | A loop is added over a collection an existing loop folded | Accepted; the collection is built again for it and folded whole, and the existing loop keeps its own iteration and folds nothing twice |
//! | A loop is added over an input this version cannot build again | Accepted; it folds from where that input starts, and the report names it and how much it will not see |
//! | A variable is added whose name another already has | Accepted; the bindings enclosing each declaration tell them apart, so the existing one resumes and the added one starts at its init |
//! | A variable moves to another loop | Accepted; it seeds with the value it held and decides the positions its new loop's iteration still has |
//! | A variable moves to or from a transaction | Accepted either direction; the value carries, and a fold caught partway resumes at the cut so no element is folded twice |
//! | The same, onto a different collection | Accepted; the value carries and the new collection is folded whole, since the sequence its positions were counted in is gone |
//! | A loop reads another source — a port change, say | Accepted; same as above, and the port it left is released |
//! | Two loops, or two transaction writers, swap which source they read | Accepted; each keeps its value and continues where its new source has got to |
//! | A variable moves to a loop over a fixed collection | Accepted; same as above — the value seeds and the collection folds on top of it |
//! | The body of a loop over a fixed collection is edited | Accepted; the fold resumes at the position it had reached, so the new rule governs the elements left |
//! | The same, with the fold caught partway | Accepted; every element is folded once, and the cut falls at the position the retired version had reached |
//! | The collection itself is edited | Accepted; the edited collection is a different computation, so its iteration is rebuilt and the collection folded whole |
//! | The same, over a collection a filter narrows | Accepted; the cut falls on a position the filter kept, which is a position of the collection it filters |
//! | An endpoint is added | Accepted; the route serves as soon as the swap completes |
//! | An endpoint is removed | Accepted; the route is retired and the address answers 404, unless it was the port's last route, in which case the port is released |
//! | An endpoint is removed with a request already in flight to it | Accepted; that request is answered 404 too, rather than waiting for a reply no version will compute |
//! | Repeats and reverts | Accepted; each takes effect |
//! | A reload after one that kept a stateful binding whole | Accepted; the variable under the kept binding is still carried and still guarded |
//!
//! # What it may not
//!
//! | Change | Expected |
//! | --- | --- |
//! | A variable is no longer declared | Refused, naming it |
//! | A variable's type changes | Refused, naming both types |
//! | Two anonymous call sites of one stateful function are reordered, or a third inserted ahead | Refused, naming both declarations and saying to bind each call site to a name |
//! | The source does not compile | Refused |
//!
//! In every refusal the running program keeps serving. Diffing is covered
//! separately and must leave it untouched whichever phase it compares at, and
//! whatever the version it is compared against would have changed.
//!
//! # Two properties worth stating
//!
//! How much a reload reuses does not depend on how many reloads came before it:
//! a binding is named by what it computes, not by whether the compilation before
//! this one happened to build it.
//!
//! A rebuilt store resumes rather than restarting, and resumes at the position
//! its source has reached rather than replaying it. Most cases here drive two or
//! three requests before reloading, which is not enough to exercise a resuming
//! store's indexing — `a_store_resumes_however_far_its_source_has_advanced`
//! drives six for that reason.
//!
//! Neither property weakens with the number of reloads. Every `{PORT}` fixture
//! here binds its store at the top of the binding chain, where each compilation
//! registers it again; the two cases over `nested_fold` put a store under another
//! binding instead, which is the placement where keeping that binding is what
//! has to hand the store on.

// A test binary's crate root resolves child modules relative to `tests/`, not to
// a directory named after this file, so each `mod` names its path. `common` is
// the gallery's HTTP and scheduler glue, compiled into this binary too.
#[path = "hot_reload/cases.rs"]
mod cases;
#[path = "hot_reload/harness.rs"]
mod harness;
#[path = "support/serving.rs"]
mod serving;

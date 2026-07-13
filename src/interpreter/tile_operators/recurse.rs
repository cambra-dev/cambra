use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use bit_set::BitSet;

use super::*;
use crate::interpreter::{ColumnValue, Consumer, Extent, Scheduler, Value, WakeupQueue};

// ---------------------------------------------------------------------------
// Recurse  (mutation-loop driver, single output port)
// ---------------------------------------------------------------------------

/// Loop driver for mutation accumulation.  Takes three inputs (init,
/// domain, recursive_input) and is itself a `TileOperator` whose
/// emitted tile is the *previous-accumulator* stream — `init` at
/// position 0, `recursive_input[i-1]` at position `i` for `i > 0`.
///
/// Op-conversion wraps `Recurse` in a `FanOut`; one branch is read by
/// the loop body as `acc_var`, and another branch is the loop's
/// external prev-acc stream.  The loop body itself is always a
/// `Record({step, to_<defer>*})` and is wrapped in `FanOut(Memo(...))`: one
/// branch is projected to `.step` and feeds back into `recursive_input`
/// (closing the cycle), the other is the external output (exposed
/// directly as the running Record stream).  The body fan-out's
/// re-entrancy support (the cyclic mode of [`FanOut::new_cyclic`]) lets
/// the cyclic subscribe and pull paths close back through it without
/// `RefCell` aliasing.
///
/// **Inputs:**
/// 1. **init** — any tiling.  `Scalar(T)` for single-accumulator
///    loops, `Record({f_i: Scalar(T_i)})` for multi-accumulator loops
///    (the per-variable inits combined via `ScalarFanIn` by
///    op-conversion).  The codomain tiling of this `Recurse` mirrors
///    `init.tiling()` exactly.
/// 2. **domain** — a `SealedFunction(D, Scalar(D_elem))` (typically an
///    [`IterateExtent`]) whose codomain values enumerate the iteration
///    positions in canonical order.
/// 3. **recursive_input** — a `SealedFunction(D, init.tiling)`
///    carrying the new accumulator value at each position.  Wired in
///    after construction via the closure returned by
///    [`Recurse::recursive_input_setter`], since the body has to be
///    compiled around our output port before it's available.
///
/// **Output**: the *prev-acc* stream `SealedFunction(D, init.tiling)`
/// — `init` at position 0, `recursive_input[i-1]` at position
/// `i > 0`.  `acc_var` reads inside the loop body resolve to this
/// stream; surrounding lowering composes against this stream and
/// inlines any pending mutations to recover the right per-iteration
/// accumulator view (see `lower_mutation_loop` in [`crate::ccl::lower`]).
///
/// The body's external `Fun(D, Record({step, to_<defer>*}))` output is
/// exposed directly; downstream lowering picks each accumulator off
/// via `Proj("step") [▷ Proj(i)] ▷ Last` and each per-iteration channel
/// via `Proj("to_<defer>")`.
///
/// **Wiring order** (see `interpreter::operator_conversion`'s `Loop` arm):
/// ```text
/// 1. Construct Recurse with init and domain inputs.
/// 2. Grab `recursive_input_setter` BEFORE moving Recurse into a Box —
///    this is the only way to wire recursive_input later, since the
///    body needs Recurse already wrapped as a TileOperator.
/// 3. Wrap Recurse in `FanOut`; use one of its branches as acc_var.
/// 4. Compile loop_body in a scope where `acc_var` resolves to that
///    FanOut branch — its output is the new-accumulator Record stream.
/// 5. Wrap the body in `FanOut(Memo(...))`; call the setter from step 2
///    with the `.step` projection of one branch (closing the cycle).
///    Use another branch as the external output (exposed directly).
/// ```
///
/// **Cycle convergence.**  `RecurseProducer::get_impl` drives the cycle
/// by pulling `recursive_input` once per call.  Because `Recurse` is
/// wrapped in a `FanOut`, only one `RecurseProducer` is ever
/// constructed; the body's `acc_var` reads close back through that
/// fan-out, not through a fresh call into `get_impl`, so there's no
/// in-process re-entrance into the producer.  The body fan-out's own
/// re-entrancy support makes the re-entrant pull on `recursive_input`
/// itself safe: the outer call has the inner producer taken out, so
/// the inner pull sees `producer = None` and serves from the
/// fan-out's `cached_tile` (which is the body's prior emission —
/// exactly what `recurse_step` needs to record into `known` to
/// advance the cycle).
pub struct Recurse {
    /// Init operator, set at construction and subscribed on `subscribe`.
    init_op: Box<dyn TileOperator>,
    /// Domain operator, set at construction and subscribed on `subscribe`.
    domain_op: Box<dyn TileOperator>,
    /// Recursive input — the body fan-out's branch back into us.  Wired
    /// in by the closure returned from [`Recurse::recursive_input_setter`]
    /// after the loop body has been compiled.  Behind `Rc<RefCell<...>>`
    /// so the setter can mutate it after `self` has been moved into a
    /// `Box<dyn TileOperator>` — the body lives downstream of us in
    /// the op graph and can only be wired in once we've been boxed for
    /// use as a `TileOperator`.
    recursive_input_op: Rc<RefCell<Option<Box<dyn TileOperator>>>>,
    output_tiling: Tiling,
    domain_extent: Extent,
    /// The tiling of the accumulator (mirrors `init.tiling()`).  Drives
    /// the codomain shape of emitted tiles: a [`Tiling::Scalar`] codomain
    /// emits `Tile::Scalar`, a [`Tiling::Record`] codomain emits
    /// `Tile::Record` with per-field scalar sub-tiles built by
    /// [`build_codomain_tile_from_values`].  See [`Recurse::new`].
    codomain_tiling: Tiling,
}

impl Recurse {
    /// Construct a new `Recurse` with `init` and `domain` inputs wired.
    /// The recursive input is wired in later via the closure returned
    /// from [`Recurse::recursive_input_setter`], once the loop body
    /// has been compiled around our output port.
    ///
    /// The codomain tiling of this `Recurse` mirrors `init.tiling()`
    /// exactly, so a `Tiling::Scalar(T)` init produces a `SealedFunction(D,
    /// Scalar(T))` output (single-accumulator scalar Joins) while a
    /// `Tiling::Record({f_i: Scalar(T_i)})` init produces `SealedFunction(D,
    /// Record({f_i: Scalar(T_i)}))` — the shape used by multi-accumulator
    /// mutation loops where op-conversion combines the per-variable inits
    /// into a single `ScalarFanIn` so one `Recurse` drives every cycle.
    pub fn new(init: Box<dyn TileOperator>, domain: Box<dyn TileOperator>) -> Self {
        let domain_extent = match domain.tiling() {
            Tiling::SealedFunction { domain, .. } => domain.clone(),
            other => panic!("Recurse domain must have SealedFunction tiling, got {other}"),
        };
        let codomain_tiling = init.tiling().clone();
        // `Recurse`'s codomain mirrors `init.tiling()`, and downstream
        // [`build_codomain_tile_from_values`] only knows how to construct
        // `Tile::Scalar` and `Tile::Record` codomains from value vectors —
        // anything else (SealedFunction, CurriedFunction, Aggregation)
        // panics deep inside the producer.  Catch the misuse here, where
        // the failure points at the `Recurse::new` caller (op-conversion's
        // `Loop` arm or a future caller) rather than at a per-tile
        // construction failure many iterations later.
        debug_assert!(
            codomain_tiling.is_scalar(),
            "Recurse init must have a scalar or scalar-record tiling, got {codomain_tiling}",
        );
        let output_tiling = Tiling::SealedFunction {
            domain: domain_extent.clone(),
            codomain: Box::new(codomain_tiling.clone()),
        };
        Self {
            init_op: init,
            domain_op: domain,
            recursive_input_op: Rc::new(RefCell::new(None)),
            output_tiling,
            domain_extent,
            codomain_tiling,
        }
    }

    /// Return a closure that wires the recursive input — typically the
    /// compiled loop body's `FanOut` branch, after the body has been
    /// built around `Recurse`.
    ///
    /// Returned as a setter rather than a `&self` method so that
    /// op-conversion can hold onto the setter after `Recurse` itself
    /// has been moved into a `Box<dyn TileOperator>` (and from there
    /// into the `FanOut` that splits the prev-acc stream to its
    /// consumers).  The body can't be compiled until `Recurse` is a
    /// `TileOperator` (it reads `acc_var` = our output port), so this
    /// construction-time ordering is the natural one.
    pub fn recursive_input_setter(&self) -> impl FnOnce(Box<dyn TileOperator>) + use<> {
        let slot = self.recursive_input_op.clone();
        move |op| {
            *slot.borrow_mut() = Some(op);
        }
    }
}

impl TileOperator for Recurse {
    fn tiling(&self) -> &Tiling {
        &self.output_tiling
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Kick the body chain immediately: the value at position 0 (the
        // `init` value) is always available, so this port has data to
        // serve as soon as it is subscribed.  This is what lets the
        // surrounding drain loop make progress on its first iteration —
        // without this notify, the body's subscription would idle until
        // something else notified it. `consumer` is retained (below, as a
        // shareable `Rc`) so each subsequent partial pull can re-arm this signal
        // through the wakeup queue as it converges.
        let consumer: Rc<RefCell<dyn Consumer>> = {
            let mut consumer = consumer;
            Rc::new(RefCell::new(move || consumer.notify()))
        };
        consumer.borrow_mut().notify();
        let wakeups = scheduler.wakeup_queue();
        let init_guard = self.init_op.tiling().universal_guard();
        let init_producer = self
            .init_op
            .subscribe(init_guard, Box::new(|| {}), scheduler);
        let domain_guard = self.domain_op.tiling().universal_guard();
        let domain_producer = self
            .domain_op
            .subscribe(domain_guard, Box::new(|| {}), scheduler);
        let mut recursive_input_op = self
            .recursive_input_op
            .borrow_mut()
            .take()
            .expect("Recurse: recursive_input not wired (call recursive_input_setter)");
        let recursive_input_guard = recursive_input_op.tiling().universal_guard();
        let recursive_input_producer =
            recursive_input_op.subscribe(recursive_input_guard, Box::new(|| {}), scheduler);
        Box::new(RecurseProducer {
            base: ProducerBase::new(RecurseProducer::alloc_id(), &self.output_tiling),
            consumer,
            wakeups,
            init_producer,
            domain_producer,
            recursive_input_producer,
            init_value: None,
            domain_values: Vec::new(),
            known: HashMap::new(),
            recorded_positions: HashSet::new(),
            domain_extent: self.domain_extent.clone(),
            codomain_tiling: self.codomain_tiling.clone(),
            released_cycle_positions: Predicate::False,
            recursive_input_released: Predicate::False,
        })
    }
}

struct RecurseProducer {
    base: ProducerBase,
    /// The downstream consumer, retained so the cycle can request its own
    /// re-pull. The recurrence advances one position per `get`, so between the
    /// first pull and convergence there is more to compute but no *external*
    /// notification will arrive (the domain source has already fired). After a
    /// pull that made progress but has not yet converged, `get_impl` asks the
    /// [`WakeupQueue`] to re-notify this consumer, so a demand-driven driver
    /// re-pulls until terminal instead of stalling on a wake-up that never comes.
    /// Held as a shared `Rc` because the wakeup queue delivers it later, and
    /// because a synchronous `notify()` from inside `get` would re-enter the
    /// cyclic operator graph mid-borrow (see [`WakeupQueue`]).
    consumer: Rc<RefCell<dyn Consumer>>,
    /// The scheduler's deferred-wakeup queue — where a progress-but-not-converged
    /// pull re-arms `consumer` for the next `check_for_notifications`.
    wakeups: WakeupQueue,
    init_producer: Box<dyn TileProducer>,
    domain_producer: Box<dyn TileProducer>,
    recursive_input_producer: Box<dyn TileProducer>,
    /// Cached `init` value — fetched once on the first iteration step
    /// (`init` may itself be a previous loop's scalar Join, which
    /// can take several pulls to resolve under the single-step model).
    /// For multi-accumulator loops this is a [`Value::Record`] packing
    /// every accumulator's initial value; for scalar loops it is a
    /// primitive value.  Mirrors the body's per-iteration emission shape.
    init_value: Option<Value>,
    /// Cached `domain` codomain values, in canonical order.  Maintained
    /// *cumulatively*: old positions stay even after the body has
    /// released them, so the index-based prev-acc lookup below
    /// (`init` at index 0, `known[domain_values[i-1]]` at index `i`)
    /// stays stable as the source frontier advances.
    domain_values: Vec<Value>,
    /// Recorded `recursive_input` values, indexed by domain value.
    /// Each `recurse_step` records observed (domain, codomain) pairs
    /// here so the next prev-acc tile emission can serve them.  Each
    /// value matches `codomain_tiling`'s shape (scalar primitive or
    /// `Value::Record` for multi-accumulator loops).
    known: HashMap<Value, Value>,
    /// Set of domain values whose `recursive_input` value has been
    /// observed at some point.  Grows monotonically — never shrinks,
    /// even when [`Self::release_impl`] drops the corresponding entry
    /// from `known` after downstream consumers release their successor
    /// positions.  The `fully_drained` check (in [`Self::get_impl`])
    /// uses this to detect convergence; using `known.contains_key` for
    /// that purpose would break once incremental release starts
    /// freeing entries before terminal.
    recorded_positions: HashSet<Value>,
    domain_extent: Extent,
    /// Tiling of the codomain.  Drives the per-pull tile construction
    /// in [`Self::get_impl`] via [`build_codomain_tile_from_values`].
    codomain_tiling: Tiling,
    /// Cumulative predicate over cycle output positions that downstream
    /// consumers have released.  Each release call unions the new
    /// guard into this set; [`Self::release_impl`] uses it both as the
    /// release predicate to forward to `domain_producer` (cycle and
    /// source share a domain) and — shifted by one position — as the
    /// predicate to forward to `recursive_input_producer` and to drop
    /// from `known`.  Streaming sources rely on this to free upstream
    /// state as positions are consumed, rather than holding everything
    /// until source convergence.
    released_cycle_positions: Predicate,
    /// Cumulative predicate already forwarded to
    /// `recursive_input_producer` (the *shifted* form of
    /// `released_cycle_positions`).  Tracked so each `release_impl`
    /// call only forwards the *new* shifted positions rather than the
    /// whole cumulative set every time.  `release` is idempotent so
    /// double-release would be safe, just wasteful for long-running
    /// streams.
    recursive_input_released: Predicate,
}

impl RecurseProducer {
    /// Pull `init_producer` (once it converges to a single scalar) and
    /// cache the result.  Returns `None` if `init` is still un-resolved
    /// — happens when `init` is itself a previous loop's scalar Join
    /// (a sequential `for` chain) which can take several pulls to
    /// converge.  Callers handle `None` by bailing out with a
    /// non-terminal empty tile; the outer consumer's pull loop will
    /// retry.
    fn ensure_init_value(&mut self) -> Option<Value> {
        if let Some(v) = &self.init_value {
            return Some(v.clone());
        }
        let tile = self
            .init_producer
            .get(self.init_producer.tiling().universal_guard());
        let resolved = scalar_tile_to_column_value(tile).as_single();
        if let Some(v) = &resolved {
            self.init_value = Some(v.clone());
        }
        resolved
    }

    /// Pull `domain_producer` and append any newly-seen positions to
    /// `domain_values` (cumulatively — old positions stay even after
    /// the body has released them, so index-based prev-acc lookup
    /// stays stable).  Returns whether the domain is now terminal.
    fn refresh_domain_values(&mut self) -> bool {
        let tile = self
            .domain_producer
            .get(self.domain_producer.tiling().universal_guard());
        let domain_terminal = tile.is_terminal();
        let Tile::SealedFunction { codomain, .. } = tile else {
            panic!("Recurse: domain must produce a SealedFunction tile");
        };
        let cv = scalar_tile_to_column_value(*codomain);
        // Append any positions we haven't already seen.  Domain emits in
        // canonical order and positions never disappear from our
        // cumulative list, so an O(N) "is this already present" check
        // is fine — a HashSet would just trade one allocation for another.
        for i in 0..cv.len() {
            let v = cv.index_at(i);
            if !self.domain_values.contains(&v) {
                self.domain_values.push(v);
            }
        }
        domain_terminal
    }

    /// Pull `recursive_input_producer` once and record any newly-observed
    /// positions into `known`.  This is a *re-entrant* pull through the
    /// body fan-out: the outer caller (a `FanOut` branch on this
    /// `Recurse`) has the inner producer taken out, so this pull serves
    /// from the body fan-out's cached tile (the body's prior emission)
    /// rather than re-driving body.
    ///
    /// **Release happens out-of-band in [`Self::release_impl`].**
    /// `recurse_step` only records.  When a downstream consumer
    /// releases cycle positions, `release_impl` forwards a
    /// shifted-by-one release into `recursive_input_producer` (so the
    /// body fan-out's recursive-input branch can advance its
    /// per-branch release predicate, eventually freeing the body's
    /// cached tile and the source).  The universal release on
    /// `fully_drained` (in `get_impl`) catches anything left at
    /// convergence.
    fn recurse_step(&mut self) {
        let universal = self.recursive_input_producer.tiling().universal_guard();
        let mut tile = self.recursive_input_producer.get(universal);
        tile.compact();
        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("Recurse: recursive_input must produce SealedFunction tiles");
        };
        let cv = scalar_tile_to_column_value(*codomain);
        for i in 0..domain.len() {
            let dval = domain.index_at(i);
            if self.recorded_positions.contains(&dval) {
                continue;
            }
            self.recorded_positions.insert(dval.clone());
            self.known.insert(dval, cv.index_at(i));
        }
    }
}

impl TileProducer for RecurseProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // `init` may be a previous loop's scalar Join — under the
        // single-step model, that producer may need several pulls to
        // converge.  Bail out early with a non-terminal empty tile if
        // so; the outer consumer's loop will keep calling `get` until
        // everything is terminal.
        let Some(init_value) = self.ensure_init_value() else {
            // `Tiling::empty_tile` produces the structurally-valid empty
            // SealedFunction with `Predicate::False` we want as the
            // "not ready yet" signal. `init` is a value (a literal or a prior
            // loop's scalar result), never an external stream, so it *will*
            // resolve — notify so the driver re-pulls and drives it there,
            // rather than waiting for a wake-up that only the (already-fired)
            // domain source could send.
            self.wakeups.request(self.consumer.clone());
            return self.tiling().empty_tile();
        };
        let domain_terminal = self.refresh_domain_values();
        // Progress = this pull recorded a new position of the recurrence. When
        // it did but we have not yet converged, more remains to compute with no
        // external trigger pending, so we notify below to request a re-pull.
        let recorded_before = self.recorded_positions.len();
        self.recurse_step();
        let made_progress = self.recorded_positions.len() > recorded_before;

        // Emit the full prev_acc tile (every domain position we've seen
        // with a known prev-acc value).  We don't filter by what
        // consumers have released — the surrounding `FanOut` does
        // per-branch release filtering on the way out, so each branch
        // sees only what its own consumer still cares about.
        let mut domain_out: Vec<Value> = Vec::new();
        let mut codomain_out: Vec<Value> = Vec::new();
        for (i, dval) in self.domain_values.iter().enumerate() {
            let value = if i == 0 {
                init_value.clone()
            } else {
                let prev_dval = &self.domain_values[i - 1];
                match self.known.get(prev_dval) {
                    Some(v) => v.clone(),
                    None => continue, // Not yet computed — skip until it's filled in.
                }
            };
            domain_out.push(dval.clone());
            codomain_out.push(value);
        }
        let domain = ColumnValue::from_values(domain_out, &self.domain_extent);
        let codomain_tile = build_codomain_tile_from_values(codomain_out, &self.codomain_tiling);
        // The shifted prev_acc stream is fully drained iff the source's
        // `domain` operator declared its tile terminal *and* every
        // announced position has a `known` entry (i.e. `recursive_input`
        // delivered a value for it).  At that point we can advertise
        // `Predicate::True` so downstream operators (FanIn, ExtractLast,
        // etc.) see the tile as terminal.  Otherwise we fall back to the
        // explicit position list — which signals "these positions are
        // present, more may arrive".
        // Convergence: every announced position has had its
        // `recursive_input` value recorded.  We track this against
        // `recorded_positions` rather than `known` because
        // `release_impl` may have already evicted entries from `known`
        // whose successor cycle positions were released by downstream
        // — those positions were still seen, just no longer needed
        // for emission.
        let fully_drained = domain_terminal
            && self
                .domain_values
                .iter()
                .all(|v| self.recorded_positions.contains(v));
        let domain_predicate = if fully_drained {
            Predicate::True
        } else if domain.is_empty() {
            Predicate::False
        } else {
            Predicate::from_column_value(&domain)
        };
        // On convergence, universally release both internal subscriptions
        // so the source sees a `Predicate::True` release from this
        // `Recurse` group.  A `DataSource`'s released-predicate is the
        // intersection across every subscriber; if `domain_producer`
        // (our own `IterateExtent` over the source) and
        // `recursive_input_producer` (the body fan-out's branch back to
        // us) don't both reach universal, the source's intersection
        // stays narrower than `True`.  We do it here — not in
        // `release_impl` — because the public consumer (e.g. `ExtractLast`
        // wrapping the body fan-out's other branch) doesn't necessarily
        // release us when the cycle finishes.  Release is idempotent, so
        // doing it on every post-convergence pull is fine.
        if fully_drained {
            self.domain_producer
                .release(self.domain_producer.tiling().universal_guard());
            self.recursive_input_producer
                .release(self.recursive_input_producer.tiling().universal_guard());
        }
        // If we aren't done and there is more data already available, queue up a notification
        // to be fired outside of the `get` callstack.
        if !fully_drained && (domain_terminal || made_progress) {
            self.wakeups.request(self.consumer.clone());
        }
        Tile::SealedFunction {
            domain_predicate,
            domain,
            codomain: Box::new(codomain_tile),
            deleted: BitSet::new(),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Universal release: forward universally to both upstream subs.
        // (Idempotent with the `fully_drained` path in `get_impl`, which
        // also fires universal releases on convergence.)
        if obsolete_guard.is_universal() {
            self.released_cycle_positions = Predicate::True;
            self.recursive_input_released = Predicate::True;
            self.domain_producer
                .release(self.domain_producer.tiling().universal_guard());
            self.recursive_input_producer
                .release(self.recursive_input_producer.tiling().universal_guard());
            self.known.clear();
            return;
        }

        // Per-position release: a downstream consumer has signalled
        // that some cycle positions are no longer needed.  Three things
        // to do:
        //
        //   1. Forward the release to `domain_producer` directly —
        //      we and the source share a domain, so the cycle release
        //      and the source release are the same predicate.
        //
        //   2. Forward a *shifted* release to `recursive_input_producer`:
        //      cycle position `i` was emitted using
        //      `known[domain_values[i-1]]`, so releasing cycle
        //      position `i` makes `recursive_input` at
        //      `domain_values[i-1]` obsolete (for `i > 0`; the very
        //      first position uses `init_value`, not a recursive_input
        //      value).
        //
        //   3. Drop the corresponding entries from `known`, since
        //      those values are no longer needed for prev-acc lookup
        //      of any unreleased cycle position.
        let new_pred = match &obsolete_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => p.clone(),
            other => panic!("Recurse: unsupported release guard {other:?}"),
        };
        self.released_cycle_positions = self.released_cycle_positions.union(&new_pred);
        self.domain_producer
            .release(TileGuard::Function(FunctionGuard::Domain(new_pred)));

        // Compute the shifted predicate over `domain_values`:
        // predecessors of positions newly released as cycle outputs
        // and not yet released as recursive_input positions.  Done by
        // walking `domain_values` rather than by a generic predicate
        // shift because the "shift" depends on the source's actual
        // emission order, which lives in this Vec.
        let mut new_shifted: Vec<Value> = Vec::new();
        for i in 1..self.domain_values.len() {
            let dval = &self.domain_values[i];
            if !self.released_cycle_positions.contains(dval) {
                continue;
            }
            let pred_dval = &self.domain_values[i - 1];
            if self.recursive_input_released.contains(pred_dval) {
                continue;
            }
            new_shifted.push(pred_dval.clone());
        }
        if !new_shifted.is_empty() {
            let cv = ColumnValue::from_values(new_shifted.clone(), &self.domain_extent);
            let shifted_pred = Predicate::from_column_value(&cv);
            self.recursive_input_released = self.recursive_input_released.union(&shifted_pred);
            self.recursive_input_producer
                .release(TileGuard::Function(FunctionGuard::Domain(shifted_pred)));
            for v in new_shifted {
                self.known.remove(&v);
            }
        }
    }
}

/// Build a codomain [`Tile`] from a stream of accumulator values laid out
/// in domain-position order, mirroring `tiling`'s shape.
///
/// - For [`Tiling::Scalar`], emit `Tile::Scalar(ColumnValue::from_values(…))` —
///   the existing scalar-Recurse path.
/// - For [`Tiling::Record`], split each [`Value::Record`] into per-field
///   value columns and recurse, producing `Tile::Record({field: Tile::Scalar(…)})`
///   that matches what [`FanIn`] emits for the body of a multi-accumulator
///   mutation loop (so `recursive_input` feeds back tile-shape-compatibly
///   with our output).
///
/// Panics on tilings we don't currently produce as a `Recurse` codomain.
fn build_codomain_tile_from_values(values: Vec<Value>, tiling: &Tiling) -> Tile {
    match tiling {
        Tiling::Scalar(extent) => Tile::Scalar(ColumnValue::from_values(values, extent)),
        Tiling::Record(fields) => {
            let mut field_tiles: HashMap<String, Tile> = HashMap::with_capacity(fields.len());
            for (field_name, field_tiling) in fields {
                let field_values: Vec<Value> = values
                    .iter()
                    .map(|v| match v {
                        Value::Record(r) => r
                            .get(field_name)
                            .cloned()
                            .expect("Record value missing expected field"),
                        other => panic!(
                            "build_codomain_tile_from_values: expected Value::Record, got {other:?}"
                        ),
                    })
                    .collect();
                field_tiles.insert(
                    field_name.clone(),
                    build_codomain_tile_from_values(field_values, field_tiling),
                );
            }
            Tile::Record(field_tiles)
        }
        other => panic!("Recurse: unsupported codomain tiling {other}"),
    }
}

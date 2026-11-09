use std::borrow::Cow;

use bit_set::BitSet;

use super::*;
use crate::interpreter::operator_graph::value;
use crate::{
    ccl::FieldKey,
    interpreter::{
        ColumnValue, Consumer, Scheduler, Value, shared_consumer, tiling::FunctionGuard,
        tuple_field,
    },
};

// ---------------------------------------------------------------------------
// CheckedLookup / CheckedLookupProducer
// ---------------------------------------------------------------------------

/// The checked lookup `c[k]` — decide whether `k` is a key of `c`, and answer
/// `` `some(c(k)) `` or `` `none ``.
///
/// **Membership is decided here, not read off an empty tile.** A collection is a total
/// function on its own domain, so applying it at a key outside that domain is not an
/// operation the type system offers; what `c[k]` returns is a tagged sum, and producing
/// one means deciding the predicate. An empty tile cannot stand in for that decision,
/// because it means "no rows known here" — which covers a key genuinely absent *and* a
/// producer that has not converged. Reading `` `none `` off it would make the answer a
/// function of how far the source had run rather than of the collection's value, so a
/// lookup on a live source would answer `` `none `` and later `` `some ``.
///
/// Terminality is therefore the **readiness** condition rather than the answer: until the
/// domain is decided this operator emits nothing, exactly as any operator awaiting its
/// input does.
pub struct CheckedLookup {
    /// Identity and the answer's tiling, one `` {`none | `some{𝑉}} `` per key.
    base: OperatorBase,
    /// Where the collection and the keys come from — see [`LookupSource`].
    source: LookupSource,
}

/// The two ways a lookup's operands reach this operator.
///
/// Which one it is follows from where the lookup sits, not from the collection: `lookup?` is
/// applied to a `(collection, key)` pair, and op-conversion either still has that pair as a
/// term or has already assembled it into a stream of rows.
enum LookupSource {
    /// Both operands still terms, so each compiles as its own source: the collection is read
    /// once and every key answered against it.
    Split {
        collection: Box<dyn TileOperator>,
        keys: Box<dyn TileOperator>,
    },
    /// One stream of `(collection, key)` rows, the point-free form of a lookup inside an
    /// iteration. Field 0 carries either a nested function tile — one collection shared by
    /// every row — or a scalar column of materialized map values, one per row.
    Paired(Box<dyn TileOperator>),
}

impl CheckedLookup {
    /// Look keys up in `collection`, with both operands as their own sources. The answer
    /// takes the keys' shape: a scalar for `m[1]`, a stream wherever the keys are one.
    pub fn split(
        collection: Box<dyn TileOperator>,
        keys: Box<dyn TileOperator>,
        option_extent: Extent,
    ) -> Self {
        let tiling = answer_tiling(keys.tiling(), option_extent);
        Self {
            base: OperatorBase::new(tiling),
            source: LookupSource::Split { collection, keys },
        }
    }

    /// Look each row's key up in that row's collection, over an assembled stream of
    /// `(collection, key)` pairs. The answer's domain is the stream's own.
    pub fn paired(pairs: Box<dyn TileOperator>, option_extent: Extent) -> Result<Self, String> {
        let Tiling::DataFunction { domain, codomain } = pairs.tiling() else {
            return Err(format!(
                "`lookup?` over an assembled pair needs a stream of rows, got {}",
                pairs.tiling()
            ));
        };
        let Tiling::Record(fields) = codomain.as_ref() else {
            return Err(format!(
                "`lookup?`'s input rows must be `(collection, key)` pairs, got {codomain}"
            ));
        };
        // Field 0 is the collection. A nested function tiling is either one collection shared
        // by every row or a collection per row, one run beneath each row; the tiling does not
        // tell them apart, and the producer does, by the level's run count. A scalar is a
        // materialized map value per row. Anything else is a collection whose values are
        // themselves collections, which has no answer shape.
        let collection = fields
            .get(&tuple_field(0))
            .ok_or_else(|| "`lookup?`'s input rows have no collection field".to_string())?;
        match collection {
            Tiling::DataFunction { codomain, .. } if !codomain.holds_a_level() => {}
            Tiling::Scalar(Extent::Function { .. }) => {}
            other => {
                return Err(format!(
                    "`c[k]` over a collection whose values are themselves collections is not \
                     supported yet: the answer would carry a collection as its `some` \
                     payload, and its tiling is {other}"
                ));
            }
        }
        // Field 1 is the key. A key is one value, spread over a column per field where it is
        // a product, so the runtime pivots it to one column and searches with that.
        match fields.get(&tuple_field(1)) {
            Some(t) if is_key_tiling(t) => {}
            other => {
                return Err(format!(
                    "`lookup?`'s input rows carry one key each, so field 1 tiles as a scalar \
                     or as a record of them; got {}",
                    other.map_or_else(|| "no field".to_string(), Tiling::to_string)
                ));
            }
        }
        let tiling = Tiling::DataFunction {
            domain: domain.clone(),
            codomain: Box::new(Tiling::Scalar(option_extent)),
        };
        Ok(Self {
            base: OperatorBase::new(tiling),
            source: LookupSource::Paired(pairs),
        })
    }
}

/// The answer's tiling for a given key tiling: one option per key, in the keys' own shape.
///
/// A key is one value however many columns carry it, so a **product** key — a tuple or
/// record, which tiles as a record of columns — takes the scalar shape
/// ([`is_key_tiling`], which is what decides it here too).
fn answer_tiling(keys: &Tiling, option_extent: Extent) -> Tiling {
    if is_key_tiling(keys) {
        return Tiling::Scalar(option_extent);
    }
    match keys {
        // One key per row at one level, and a **collection of keys per row** deeper — what
        // a correlated comprehension's key binder is, one group of keys per outer row. The
        // answer keeps the shape either way: one answer per key, where its key sits.
        keys @ Tiling::DataFunction { .. } => {
            change_tiling_result(keys, |_| Tiling::Scalar(option_extent))
        }
        other => panic!("CheckedLookup keys must be a scalar or a stream, got {other}"),
    }
}

/// Whether `tiling` carries **one key**: a scalar column, or a record of them.
///
/// A product key is spread over a column per field, while a collection's domain holds it as
/// one `Records` column — two presentations of one value, which
/// [`scalar_tile_to_column_value`] converts between. Recursive, because a record whose
/// fields are not themselves keys is not a key, and the converter faults on one.
fn is_key_tiling(tiling: &Tiling) -> bool {
    match tiling {
        Tiling::Scalar(_) => true,
        Tiling::Record(fields) => fields.values().all(is_key_tiling),
        _ => false,
    }
}

impl TileOperator for CheckedLookup {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        match &self.source {
            LookupSource::Split { collection, keys } => {
                visit(value("collection", &**collection));
                visit(value("keys", &**keys));
            }
            LookupSource::Paired(pairs) => visit(value("pairs", &**pairs)),
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (source, gate) = match &mut self.source {
            // Two inputs, so both wake the same consumer. The collection is what decides an
            // absence, so when it settles after the keys it is the input that completes the
            // answer — subscribed with a consumer of its own it would settle with nobody
            // scheduled to read it (see `shared_consumer`).
            LookupSource::Split { collection, keys } => {
                let (shared, gate) = shared_consumer(consumer);
                let keys = subscribe_forwarding(&mut **keys, &shared, scheduler);
                let collection = subscribe_forwarding(&mut **collection, &shared, scheduler);
                (ProducerSource::Split { collection, keys }, Some(gate))
            }
            // One input, carrying both operands, so there is nothing to share.
            LookupSource::Paired(pairs) => (
                ProducerSource::Paired(pairs.subscribe(
                    pairs.tiling().universal_guard(),
                    consumer,
                    scheduler,
                )),
                None,
            ),
        };
        Box::new(CheckedLookupProducer {
            base: ProducerBase::new(
                CheckedLookupProducer::alloc_id(),
                &self.base.tiling,
                &self.base,
                scheduler,
            )
            .sharing(gate),
            source,
            released: false,
        })
    }
}

struct CheckedLookupProducer {
    base: ProducerBase,
    source: ProducerSource,
    released: bool,
}

/// [`LookupSource`] after subscription.
enum ProducerSource {
    Split {
        collection: Box<dyn TileProducer>,
        keys: Box<dyn TileProducer>,
    },
    Paired(Box<dyn TileProducer>),
}

/// `` `some(v) `` — the tag a present key answers with.
fn some_of(v: Value) -> Value {
    Value::Union {
        tag: FieldKey::Name(crate::ccl::V_SOME),
        inner: Box::new(v),
    }
}

/// `` `none `` — the tag a decided absence answers with.
fn none() -> Value {
    Value::Union {
        tag: FieldKey::Name(crate::ccl::V_NONE),
        inner: Box::new(Value::Unit),
    }
}

/// The answer for one key against a **materialized** map value.
///
/// A map value is a binding list, so it carries its own keys: it is complete wherever it is
/// present, and absence needs no terminality wait. This is how a mutable collection's
/// mutable variable holds its collection, at one store key.
fn answer_in_value(key: &Value, m: &Value) -> Value {
    match m {
        Value::Function(bindings) => bindings
            .iter()
            .find(|b| &b.input == key)
            .map_or_else(none, |b| some_of(b.output.clone())),
        other => panic!("CheckedLookup: collection is not a map value: {other:?}"),
    }
}

/// The answer for one key against a collection tile, or `None` while it is still deciding.
///
/// A **streamed** collection carries its keys in the domain column, so an absent key is only
/// an answer once that domain is decided. A **materialized** one is a single map value and
/// answers immediately ([`answer_in_value`]).
fn answer_for(key: &Value, coll: &Tile) -> Option<Value> {
    match coll {
        Tile::DataFunction { domain, .. } => {
            answer_in_run(key, coll, 0..domain.len(), || coll.is_terminal())
        }
        Tile::Scalar(col) if !col.is_empty() => Some(answer_in_value(key, &col.index_at(0))),
        // A materialized collection that has not arrived yet.
        Tile::Scalar(_) => None,
        other => panic!("CheckedLookup: collection is not a collection: {other:?}"),
    }
}

/// `key`'s answer in the run `run` of the streamed collection `coll`: `some` of the value
/// there, `none` where the run lacks it and `decided` says the run is complete, and nothing
/// while it is still open.
fn answer_in_run(
    key: &Value,
    coll: &Tile,
    run: std::ops::Range<usize>,
    decided: impl FnOnce() -> bool,
) -> Option<Value> {
    let Tile::DataFunction {
        domain, codomain, ..
    } = coll
    else {
        unreachable!("a streamed collection is a function tile: {coll:?}")
    };
    assert!(
        !codomain.holds_a_level(),
        "a streamed collection maps keys to values, so its keys are one level"
    );
    match run.into_iter().find(|&i| &domain.index_at(i) == key) {
        Some(i) => {
            // `None` here would read as "still deciding" for a shape that will never change,
            // and the lookup would spin instead of answering. Op-conversion's
            // `reject_unanswerable_lookup_collection` is what makes this unreachable.
            let Tile::Scalar(values) = codomain.as_ref() else {
                panic!(
                    "CheckedLookup: an answer's `some` payload is one column value, so the \
                     collection's codomain tiles as a scalar; got {codomain:?}"
                )
            };
            Some(some_of(values.index_at(i)))
        }
        None if decided() => Some(none()),
        None => None,
    }
}

/// A stream of keys answered against `coll`, one option per key where the key sits: the
/// keys' own levels, with the answer in place of each key.
///
/// **What the collection has decided goes out now.** A key it has not decided yet is
/// withheld from its group rather than holding the group back ([`Tile::withhold`]): the
/// groups re-offset, the levels above keep their rows, and no level calls the key's path
/// complete, since a row missing a key will gain it. A consumer releases what it has taken by path (`Tile::to_guard`), so a row
/// delivered in part is released in part and the rest arrives beneath it later.
fn answer_key_stream(keys: &Tile, coll: &Tile, out_extent: &Extent) -> Tile {
    let depth = keys
        .innermost_depth()
        .unwrap_or_else(|| unreachable!("a key stream is a collection: {keys:?}"));
    // A product key arrives as a record of columns and pivots to the one column a domain is
    // searched with; a scalar one is already that, and borrows, so the common shape is not
    // charged a copy per pull.
    let key_col = match keys.deepest_values() {
        Tile::Scalar(col) => Cow::Borrowed(col),
        record => Cow::Owned(scalar_tile_to_column_value(record.clone())),
    };
    let answers: Vec<Option<Value>> = (0..key_col.len())
        .map(|i| answer_for(&key_col.index_at(i), coll))
        .collect();
    let mut out = keys.clone();
    let decided = (0..answers.len())
        .map(|i| answers[i].is_some())
        .collect::<Vec<bool>>();
    if !decided.iter().all(|&d| d) {
        let paths = keys.paths_at(CurryLevel::new(depth));
        let withheld: Vec<&[Value]> = paths
            .iter()
            .zip(&answers)
            .filter(|(_, answer)| answer.is_none())
            .map(|(path, _)| path.as_slice())
            .collect();
        out.withhold(CurryLevel::new(depth), &decided, &withheld);
    }
    *out.deepest_values_mut() = Tile::Scalar(ColumnValue::from_values(
        answers.into_iter().flatten().collect(),
        out_extent,
    ));
    out
}

/// `key`'s answer in run `row` of `level`, the collection of the row at `position`, which is
/// decided once `complete` calls `[position, key]` decided ([`answer_in_run`]).
fn answer_in_row(
    position: &Value,
    key: &Value,
    level: &Tile,
    row: usize,
    complete: &Predicate,
) -> Option<Value> {
    let (start, end) = level.row_run(row);
    answer_in_run(key, level, start..end, || {
        complete.contains_path(&[position.clone(), key.clone()])
    })
}

/// How the rows of an assembled `(collection, key)` stream supply their collection.
enum RowCollection<'a> {
    /// One collection shared by every row — the collection leg was closed in the iteration,
    /// so `zip` fanned it in as a constant and it arrives as a nested function tile with one
    /// run.
    Shared(&'a Tile),
    /// One collection per row, a level beneath the rows with one run each, as a transaction's
    /// snapshot of a collection-valued variable gives. `complete` is which `[position, key]`
    /// paths are decided: the level's own statement, and every path beneath a row the stream
    /// calls complete, since completeness closes downward.
    Level { tile: &'a Tile, complete: Predicate },
    /// One materialized map value per row, as a mutable collection's mutable variable gives.
    PerRow(&'a ColumnValue),
}

impl CheckedLookupProducer {
    /// The rows' answers, paired with the domain positions they were answered at.
    ///
    /// A key the collection has not decided yet contributes no row, so the answer is a
    /// *prefix* of the key stream and grows with it. Keeping the rows aligned means carrying
    /// each answered key's own domain position.
    fn answer_rows(
        domain: &ColumnValue,
        keys: &ColumnValue,
        collection: &RowCollection<'_>,
    ) -> (Vec<Value>, Vec<Value>) {
        let mut kept = Vec::with_capacity(domain.len());
        let mut answers = Vec::with_capacity(domain.len());
        for i in 0..domain.len() {
            let answer = match collection {
                RowCollection::Shared(tile) => answer_for(&keys.index_at(i), tile),
                RowCollection::Level { tile, complete } => {
                    answer_in_row(&domain.index_at(i), &keys.index_at(i), tile, i, complete)
                }
                RowCollection::PerRow(col) => {
                    Some(answer_in_value(&keys.index_at(i), &col.index_at(i)))
                }
            };
            if let Some(v) = answer {
                kept.push(domain.index_at(i));
                answers.push(v);
            }
        }
        (kept, answers)
    }
}

/// Compact `tile`, which `input` produced, releasing to `input` the rows that drops.
fn compact_releasing(tile: &mut Tile, input: &mut Box<dyn TileProducer>) {
    let dropped = tile.deleted_keys_guard();
    tile.compact();
    if let Some(dropped) = dropped {
        input.release(dropped);
    }
}

impl TileProducer for CheckedLookupProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        match &self.source {
            ProducerSource::Split { collection, keys } => {
                visit("collection", &**collection);
                visit("keys", &**keys);
            }
            ProducerSource::Paired(pairs) => visit("pairs", &**pairs),
        }
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let out_extent = match self.tiling() {
            Tiling::Scalar(e) => e.clone(),
            // One answer per row at one level, and a collection of answers per row —
            // one per key of that row's group — deeper. Either way the answers sit where
            // the keys do.
            t @ Tiling::DataFunction { .. } => t.deepest_values().extent(),
            other => panic!("CheckedLookup tiling is a scalar or a stream, got {other}"),
        };
        // What an answer with nothing in it tiles as: an empty column where one key is
        // answered, an empty collection where a stream of them is.
        let empty = self.tiling().empty_tile();
        if self.released {
            return empty;
        }
        // Every leg is searched by position, and a release marks rows deleted rather than
        // removing them (`Tile::mark_deleted`), so a tile still carrying deletions answers a
        // released or filtered-out key as present. Compacting drops those rows and clears the
        // bitset, which is also what leaves the answer with no deletions of its own. A dropped
        // row reaches no consumer and answers no key, so each leg is released through it.
        match &mut self.source {
            ProducerSource::Split { collection, keys } => {
                let mut key_tile = keys.get(keys.tiling().universal_guard());
                compact_releasing(&mut key_tile, keys);
                let mut coll = collection.get(collection.tiling().universal_guard());
                compact_releasing(&mut coll, collection);
                match key_tile {
                    // One key: the scalar form `m[k]`, the key pivoted to one column where
                    // it is a product. An empty column is a key that has not arrived, so
                    // there is nothing to answer.
                    Tile::Scalar(_) | Tile::Record { .. } => {
                        let keys = scalar_tile_to_column_value(key_tile);
                        if keys.is_empty() {
                            return empty;
                        }
                        match answer_for(&keys.index_at(0), &coll) {
                            Some(v) => Tile::Scalar(ColumnValue::from_values(vec![v], &out_extent)),
                            None => empty,
                        }
                    }
                    // A stream of keys, each answered against the same collection — read
                    // once, not lifted into every row. One key per row at one level, and a
                    // group of keys per row deeper, which is what a correlated
                    // comprehension's key binder is.
                    ref tile @ Tile::DataFunction { .. } => {
                        answer_key_stream(tile, &coll, &out_extent)
                    }
                    other => {
                        panic!("CheckedLookup keys tile as a scalar or a stream, got {other:?}")
                    }
                }
            }
            // An assembled stream of `(collection, key)` rows.
            ProducerSource::Paired(pairs) => {
                let mut tile = pairs.get(pairs.tiling().universal_guard());
                compact_releasing(&mut tile, pairs);
                // Not a shape error: a stream that has produced nothing yet answers with an
                // empty tile, and this operator does the same until its rows arrive.
                let Tile::DataFunction {
                    ref domain,
                    ref codomain,
                    ref domain_predicate,
                    ..
                } = tile
                else {
                    return empty;
                };
                // The row shape, on the other hand, `Self::paired` has already checked.
                let Tile::Record { fields, absent } = codomain.as_ref() else {
                    panic!(
                        "CheckedLookup: input rows are `(collection, key)` pairs; got {codomain:?}"
                    )
                };
                assert_no_absent_cells(absent);
                let (Some(coll_tile), Some(key_tile)) =
                    (fields.get(&tuple_field(0)), fields.get(&tuple_field(1)))
                else {
                    panic!(
                        "CheckedLookup: input rows carry a collection at .0 and one key at .1; got {codomain:?}"
                    )
                };
                // Borrowed where the key is already one column; only a product is pivoted,
                // so the scalar pair stream is not charged a copy of its keys per pull.
                let key_col = match key_tile {
                    Tile::Scalar(col) => Cow::Borrowed(col),
                    record @ Tile::Record { .. } => {
                        Cow::Owned(scalar_tile_to_column_value(record.clone()))
                    }
                    other => panic!(
                        "CheckedLookup: a key is one value, so field 1 tiles as a scalar or a \
                         record of them; got {other:?}"
                    ),
                };
                let collection = match coll_tile {
                    Tile::Scalar(col) => RowCollection::PerRow(col),
                    // One run per row is a collection per row: answering a key against the
                    // whole level would find it in another row's collection, and would ask
                    // for the whole level's completion where this row's is what decides.
                    Tile::DataFunction {
                        row_starts,
                        domain_predicate: level,
                        ..
                    } if row_starts.len() == domain.len() => RowCollection::Level {
                        tile: coll_tile,
                        complete: domain_predicate.descend(1).union(level),
                    },
                    shared => {
                        // A per-row level whose runs fell out of step with the rows would land
                        // here and answer each key against every row's runs at once.
                        if let Tile::DataFunction { row_starts, .. } = shared {
                            debug_assert!(
                                row_starts.len() <= 1,
                                "CheckedLookup: a nested collection is one shared collection, one \
                                 run, or one run per row; got {} runs for {} rows",
                                row_starts.len(),
                                domain.len()
                            );
                        }
                        RowCollection::Shared(shared)
                    }
                };
                let (kept, answers) = Self::answer_rows(domain, &key_col, &collection);
                self.stream_tile(kept, answers, domain, domain_predicate, &out_extent)
            }
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A **domain** release names positions of the answer, and the answer is one option per
        // key at the key's own domain position — so it names key positions and passes through
        // to whatever supplies them. The **collection** is not positional: every key is
        // answered against the whole of it, so no key being finished releases any part of it.
        // That asymmetry is why the two legs are released separately rather than together.
        if let TileGuard::Function(FunctionGuard::Domain(_)) = &obsolete_guard {
            match &mut self.source {
                ProducerSource::Split { keys, .. } => keys.release(obsolete_guard),
                ProducerSource::Paired(pairs) => pairs.release(obsolete_guard),
            }
            return;
        }
        // A split answer holds the keys' levels path for path, one answer per key, so any
        // region of it — a group's keys under a row still growing among them — is the same
        // region of the keys.
        if !obsolete_guard.is_universal()
            && !obsolete_guard.is_empty()
            && let ProducerSource::Split { keys, .. } = &mut self.source
        {
            keys.release(obsolete_guard);
            return;
        }
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            match &mut self.source {
                ProducerSource::Split { collection, keys } => {
                    collection.release(collection.tiling().universal_guard());
                    keys.release(keys.tiling().universal_guard());
                }
                ProducerSource::Paired(pairs) => pairs.release(pairs.tiling().universal_guard()),
            }
        }
    }
}

impl CheckedLookupProducer {
    /// Assemble the answered rows into this producer's own stream tiling.
    ///
    /// `domain` is the input's domain column, which `kept` is a subsequence of.
    fn stream_tile(
        &self,
        kept: Vec<Value>,
        answers: Vec<Value>,
        domain: &ColumnValue,
        domain_predicate: &Predicate,
        out_extent: &Extent,
    ) -> Tile {
        let Tiling::DataFunction {
            domain: dom_ext, ..
        } = self.tiling()
        else {
            panic!("CheckedLookup answers a stream when its keys are one")
        };
        // A key the collection has not decided is a *missing* row, not a decided absence, so
        // the answer states the input's completeness less those rows, the rule
        // [`answer_key_stream`] applies at every level.
        let kept = ColumnValue::from_values(kept, dom_ext);
        let domain_predicate = if kept.len() == domain.len() {
            domain_predicate.clone()
        } else {
            let missing =
                Predicate::from_column_value(domain).minus(&Predicate::from_column_value(&kept));
            domain_predicate.minus(&missing)
        };
        Tile::data_function(
            kept,
            Box::new(Tile::Scalar(ColumnValue::from_values(answers, out_extent))),
            domain_predicate,
            BitSet::new(),
        )
    }
}

// ---------------------------------------------------------------------------
// Lookup / LookupProducer
// ---------------------------------------------------------------------------

/// The total lookup `c(k)`: each row's key read in that row's own collection.
///
/// `apply` over a collection is this lookup. Its type keeps the key inside the collection's
/// domain, so the answer is a value rather than an option, and a row is answered as soon as
/// its key arrives in its collection: a value at a key never changes, and no row waits on a
/// decided absence the way [`CheckedLookup`] does. A row whose key has not arrived yet is
/// withheld, the rule [`answer_key_stream`] applies to an undecided key.
///
/// The rows stand at `level`, each a `(key, collection)` pair. The collection is a level
/// beneath its row, one run of keys per row, which is how a collection computed from each row
/// arrives: the collection a dependent loop's source gives at each enclosing position, say.
///
/// The value read takes the pair's place under its row, whatever it tiles as: a column, a
/// record of columns, or a collection a level beneath the key. A value holding levels of its
/// own is a group moved from beneath `(row, key)` to beneath `row`, so its predicates are
/// restated as `src/interpreter/design-operators.md`, "Restating a moved group" says.
pub struct Lookup {
    /// The input's tiling with the pair at `level` replaced by the value read.
    base: OperatorBase,
    input: Box<dyn TileOperator>,
    level: CurryLevel,
}

impl Lookup {
    /// Read each row's key in its collection, for the `(key, collection)` rows at `level`.
    pub fn new_at(input: Box<dyn TileOperator>, level: CurryLevel) -> Result<Self, String> {
        let Tiling::Record(fields) = input.tiling().values_at(level) else {
            return Err(format!(
                "`apply` reads a key in a collection, so its rows are `(key, collection)` \
                 pairs; got {}",
                input.tiling().values_at(level)
            ));
        };
        match fields.get(&tuple_field(0)) {
            Some(t) if is_key_tiling(t) => {}
            other => {
                return Err(format!(
                    "`apply`'s rows carry one key each at field 0; got {}",
                    other.map_or_else(|| "no field".to_string(), Tiling::to_string)
                ));
            }
        }
        let value = match fields.get(&tuple_field(1)) {
            Some(Tiling::DataFunction { codomain, .. }) => (**codomain).clone(),
            other => {
                return Err(format!(
                    "`apply` compiles where its function is a collection, which field 1 tiles \
                     as; got {}",
                    other.map_or_else(|| "no field".to_string(), Tiling::to_string)
                ));
            }
        };
        let tiling = with_values_at(input.tiling(), level, value);
        Ok(Self {
            base: OperatorBase::new(tiling),
            input,
            level,
        })
    }
}

impl TileOperator for Lookup {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(LookupProducer {
            base: ProducerBase::new(
                LookupProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input: self
                .input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler),
            level: self.level,
        })
    }
}

struct LookupProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    level: CurryLevel,
}

/// Whether `tile` holds a collection at every level above `level`, so that its rows there
/// can be read. An input that has produced nothing yet may not.
fn reaches(tile: &Tile, level: CurryLevel) -> bool {
    let mut node = tile;
    for _ in 0..level.index() {
        let Tile::DataFunction { codomain, .. } = node else {
            return false;
        };
        node = codomain;
    }
    matches!(node, Tile::Record { .. })
}

impl TileProducer for LookupProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut tile = self.input.get(self.input.tiling().universal_guard());
        if !reaches(&tile, self.level) {
            return self.tiling().empty_tile();
        }
        let rows_level = self.level.enclosing();
        // Each row's path through the levels above it. The outermost level is one row, reached
        // by the empty path.
        let paths = match rows_level {
            Some(rows) => tile.paths_at(rows),
            None => vec![Vec::new()],
        };
        // A key is complete in its row's collection where the collection calls it complete or a
        // level above calls its row complete, completeness closing downward.
        let rows_complete = match rows_level {
            Some(rows) => tile.completion_at(rows).descend(1),
            None => Predicate::False,
        };
        let (found, pending, value) = {
            let Tile::Record { fields, absent } = tile.values_at(self.level) else {
                unreachable!("checked by `reaches`")
            };
            assert_no_absent_cells(absent);
            let (Some(key_tile), Some(collection)) =
                (fields.get(&tuple_field(0)), fields.get(&tuple_field(1)))
            else {
                panic!("Lookup: rows carry a key at .0 and a collection at .1; got {fields:?}")
            };
            let keys = match key_tile {
                Tile::Scalar(col) => Cow::Borrowed(col),
                record @ Tile::Record { .. } => {
                    Cow::Owned(scalar_tile_to_column_value(record.clone()))
                }
                other => panic!("Lookup: a key is one value; got {other:?}"),
            };
            let Tile::DataFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
                ..
            } = collection
            else {
                panic!("Lookup: each row's collection is a level beneath it; got {collection:?}")
            };
            assert_eq!(
                collection.rows(),
                keys.len(),
                "Lookup: each row holds its own collection, one run of keys per row"
            );
            let found: Vec<Option<usize>> = (0..keys.len())
                .map(|row| {
                    let key = keys.index_at(row);
                    let (from, to) = collection.row_run(row);
                    (from..to).find(|&i| !deleted.contains(i) && domain.index_at(i) == key)
                })
                .collect();
            let complete = rows_complete.union(domain_predicate);
            let pending: Vec<bool> = paths
                .iter()
                .zip(&found)
                .enumerate()
                .map(|(row, (path, at))| {
                    let mut key_path = path.clone();
                    key_path.push(keys.index_at(row));
                    at.is_none() && !complete.contains_path(&key_path)
                })
                .collect();
            let reads: Vec<ValueRead> = paths
                .iter()
                .zip(&found)
                .filter_map(|(path, at)| {
                    let mut entry = path.clone();
                    entry.push(domain.index_at((*at)?));
                    Some(ValueRead {
                        complete: complete.contains_path(&entry),
                        rows: if rows_level.is_none() {
                            Predicate::True
                        } else {
                            Predicate::exactly(path)
                        },
                        from: entry,
                    })
                })
                .collect();
            let picked: Vec<usize> = found.iter().flatten().copied().collect();
            let groups: Vec<_> = picked.into_iter().map(|row| vec![row]).collect();
            let mut value = gather_applied(codomain, &groups);
            value.map_level_predicates(&mut |depth, pred| moved_beneath_rows(pred, depth, &reads));
            (found, pending, value)
        };
        let Some(rows_level) = rows_level else {
            return match found.first().copied().flatten() {
                Some(_) => value,
                None => self.tiling().empty_tile(),
            };
        };
        let keep: Vec<bool> = found.iter().map(Option::is_some).collect();
        if !keep.iter().all(|&held| held) {
            let withheld: Vec<&[Value]> = paths
                .iter()
                .zip(&pending)
                .filter(|(_, pending)| **pending)
                .map(|(path, _)| path.as_slice())
                .collect();
            tile.withhold(rows_level, &keep, &withheld);
        }
        *tile.values_at_mut(self.level) = value;
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The answer keeps the input's keys at every level above the rows, and each row's
        // pair goes with its row. A region of a row's answer is the same region beneath every
        // key of that row's collection: its own key, whose value the answer holds, and the
        // others, which this lookup never reads.
        let level = self.level.index();
        let Tiling::Record(pair) = self.input.tiling().values_at(self.level) else {
            unreachable!("`Lookup::new_at` reads `(key, collection)` rows")
        };
        let key_kept = pair[&tuple_field(0)].empty_guard();
        let input_guard = crate::interpreter::tiling::through_standing_levels(
            obsolete_guard,
            level,
            self.input.tiling(),
            &mut |answer| {
                let beneath_every_key = answer.map_level_predicates(&mut |depth, pred| {
                    pred.with_level_inserted(level + depth, level)
                });
                TileGuard::Record(HashMap::from([
                    (tuple_field(0), key_kept.clone()),
                    (
                        tuple_field(1),
                        TileGuard::Function(FunctionGuard::Codomain(Box::new(beneath_every_key))),
                    ),
                ]))
            },
        );
        self.input.release(input_guard);
    }
}

/// `pred`, stated over the input's paths `depth` levels into the values the rows read,
/// restated over the answer's: each value taken out from beneath its entry
/// ([`Predicate::within`]) and placed beneath its row ([`Predicate::beneath`]), which the
/// outermost level, one row on the empty path, does not need. An unqualified statement names
/// its keys beneath every entry, the read ones among them, so it reads the same over the
/// answer's paths. A value whose entry is complete is complete throughout.
fn moved_beneath_rows(pred: &Predicate, depth: usize, reads: &[ValueRead]) -> Predicate {
    let arms: Vec<&Predicate> = match pred {
        Predicate::Or(arms) => arms.iter().collect(),
        one => vec![one],
    };
    let (qualified, everywhere): (Vec<&Predicate>, Vec<&Predicate>) =
        arms.into_iter().partition(|arm| arm.qualifies());
    let everywhere = everywhere
        .into_iter()
        .fold(Predicate::False, |all, arm| all.union(arm));
    let qualified = qualified
        .iter()
        .fold(Predicate::False, |all, arm| all.union(arm));
    restate_value_reads(&qualified, depth, reads, everywhere)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::TagMap;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{ReleaseSpy, TestTileProducer};

    fn int() -> Extent {
        Extent::Base(BaseType::Int)
    }

    fn uint() -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn option_of_int() -> Extent {
        Extent::Union(TagMap::from_arms(vec![
            (
                FieldKey::Name(crate::ccl::V_NONE),
                Extent::Base(BaseType::Unit),
            ),
            (FieldKey::Name(crate::ccl::V_SOME), int()),
        ]))
    }

    /// Two rows holding a group of two keys each, `[1, 9]` and `[2, 10]`, as a correlated
    /// comprehension's key binder arrives: the rows final, the groups beneath them whole.
    fn grouped_keys() -> (Tile, Tiling) {
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 9, 2, 10]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        (tile, tiling)
    }

    /// The map `{1: 10, 2: 20}`, with its domain decided or not.
    fn collection(decided: bool) -> (Tile, Tiling) {
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            if decided {
                Predicate::True
            } else {
                Predicate::False
            },
            BitSet::new(),
        );
        (tile, Tiling::data_function(int(), Tiling::Scalar(int())))
    }

    fn lookup_over(keys: (Tile, Tiling), coll: (Tile, Tiling)) -> CheckedLookupProducer {
        let tiling = answer_tiling(&keys.1, option_of_int());
        CheckedLookupProducer {
            base: ProducerBase::unowned(CheckedLookupProducer::alloc_id(), &tiling),
            source: ProducerSource::Split {
                collection: Box::new(TestTileProducer::new(coll.0, coll.1)),
                keys: Box::new(TestTileProducer::new(keys.0, keys.1)),
            },
            released: false,
        }
    }

    /// A group of keys per row answers one option per key where its key sits, the grouping
    /// carried through: `9` and `10` are absent from a decided collection.
    #[test]
    fn a_group_of_keys_per_row_answers_each_key_in_place() {
        let mut lookup = lookup_over(grouped_keys(), collection(true));
        let out = lookup.get(lookup.tiling().universal_guard());
        let levels = out.key_levels();
        assert_eq!(*levels[0].1, ColumnValue::UInts(vec![0, 1]));
        assert_eq!(*levels[1].0, vec![0, 2]);
        assert_eq!(*levels[1].1, ColumnValue::UInts(vec![0, 1, 0, 1]));
        assert_eq!(
            scalar_tile_to_column_value(out.deepest_values().clone()),
            ColumnValue::from_values(
                vec![
                    some_of(Value::Int(10)),
                    none(),
                    some_of(Value::Int(20)),
                    none()
                ],
                &option_of_int()
            )
        );
    }

    /// **What the collection has decided goes out now.** `9` and `10` are neither present nor
    /// decided absent, so each group loses that key and keeps its answered one, and neither
    /// row, nor either missing key under it, is called complete. Every other path stays as
    /// complete as the keys said.
    #[test]
    fn an_undecided_key_leaves_its_group_and_the_rest_goes_out() {
        let mut lookup = lookup_over(grouped_keys(), collection(false));
        let out = lookup.get(lookup.tiling().universal_guard());
        let levels = out.key_levels();
        assert_eq!(
            *levels[0].1,
            ColumnValue::UInts(vec![0, 1]),
            "both rows stand"
        );
        assert_eq!(*levels[1].0, vec![0, 1], "one key each");
        assert_eq!(*levels[1].1, ColumnValue::UInts(vec![0, 0]));
        assert_eq!(
            scalar_tile_to_column_value(out.deepest_values().clone()),
            ColumnValue::from_values(
                vec![some_of(Value::Int(10)), some_of(Value::Int(20))],
                &option_of_int()
            )
        );
        let Tile::DataFunction {
            domain_predicate: rows,
            codomain,
            ..
        } = &out
        else {
            panic!("the answer tiles as a collection: {out:?}")
        };
        let Tile::DataFunction {
            domain_predicate: keys,
            ..
        } = codomain.as_ref()
        else {
            panic!("a group per row: {out:?}")
        };
        let row = |r: u64| vec![Value::UInt(r)];
        let key = |r: u64, k: u64| vec![Value::UInt(r), Value::UInt(k)];
        assert!(!rows.contains_path(&row(0)) && !rows.contains_path(&row(1)));
        assert!(
            rows.contains_path(&row(2)),
            "a row the keys lack stays decided absent"
        );
        assert!(!keys.contains_path(&key(0, 1)) && !keys.contains_path(&key(1, 1)));
        assert!(!out.is_terminal());
    }

    /// A collection's release of a group's keys under a row still growing is a region of the
    /// keys too, and reaches them.
    #[test]
    fn a_release_beneath_a_growing_row_reaches_the_keys() {
        let (keys, keys_tiling) = grouped_keys();
        let (spy, released) = ReleaseSpy::new(keys, keys_tiling.clone());
        let (coll, coll_tiling) = collection(false);
        let tiling = answer_tiling(&keys_tiling, option_of_int());
        let mut lookup = CheckedLookupProducer {
            base: ProducerBase::unowned(CheckedLookupProducer::alloc_id(), &tiling),
            source: ProducerSource::Split {
                collection: Box::new(TestTileProducer::new(coll, coll_tiling)),
                keys: Box::new(spy),
            },
            released: false,
        };
        let out = lookup.get(lookup.tiling().universal_guard());
        let taken = out.to_guard();
        assert!(
            matches!(
                &taken,
                TileGuard::Function(FunctionGuard::Codomain(_)) | TileGuard::Or(_)
            ),
            "the rows are open, so what they hold is named beneath them: {taken:?}"
        );
        lookup.release(taken.clone());
        assert_eq!(*released.borrow(), vec![taken]);
    }

    /// A **one-level** stream is the same rule at depth zero: an undecided key's row is left
    /// out, and only that row is uncalled.
    #[test]
    fn an_undecided_key_in_a_flat_stream_leaves_only_its_row_open() {
        let keys = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 9]))),
            Predicate::True,
            BitSet::new(),
        );
        let keys_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let mut lookup = lookup_over((keys, keys_tiling), collection(false));
        let out = lookup.get(lookup.tiling().universal_guard());
        let Tile::DataFunction {
            domain,
            domain_predicate,
            ..
        } = &out
        else {
            panic!("the answer tiles as a collection: {out:?}")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![0]));
        assert!(domain_predicate.contains(&Value::UInt(0)));
        assert!(!domain_predicate.contains(&Value::UInt(1)));
    }

    /// Two rows, each a key and its own collection: row 0 reads `2` in `{1: 10, 2: 20}` and
    /// row 1 reads `second_key` in `{1: 30}`, whose `2` may still arrive.
    fn keyed_rows(second_key: i64, complete: bool) -> LookupProducer {
        let record = Tile::Record {
            fields: HashMap::from([
                (
                    tuple_field(0),
                    Tile::Scalar(ColumnValue::Ints(vec![2, second_key])),
                ),
                (
                    tuple_field(1),
                    Tile::grouped(
                        vec![0, 2],
                        ColumnValue::Ints(vec![1, 2, 1]),
                        Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                        if complete {
                            Predicate::True
                        } else {
                            Predicate::False
                        },
                        BitSet::new(),
                    ),
                ),
            ]),
            absent: HashMap::new(),
        };
        // Completion applies to both the rows and the collections they hold.
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(record),
            if complete {
                Predicate::True
            } else {
                Predicate::False
            },
            BitSet::new(),
        );
        let tiling = Tiling::data_function(
            uint(),
            Tiling::Record(HashMap::from([
                (tuple_field(0), Tiling::Scalar(int())),
                (
                    tuple_field(1),
                    Tiling::data_function(int(), Tiling::Scalar(int())),
                ),
            ])),
        );
        let out = Tiling::data_function(uint(), Tiling::Scalar(int()));
        LookupProducer {
            base: ProducerBase::unowned(LookupProducer::alloc_id(), &out),
            input: Box::new(TestTileProducer::new(tile, tiling)),
            level: CurryLevel::new(1),
        }
    }

    /// Each row's key is read in that row's own collection, not in one every row shares.
    #[test]
    fn each_row_reads_its_key_in_its_own_collection() {
        let mut lookup = keyed_rows(1, false);
        let out = lookup.get(lookup.tiling().universal_guard());
        assert_eq!(*out.key_levels()[0].1, ColumnValue::UInts(vec![0, 1]));
        assert_eq!(
            scalar_tile_to_column_value(out.deepest_values().clone()),
            ColumnValue::Ints(vec![20, 30])
        );
    }

    /// A row whose key has not arrived in its collection is withheld and not called complete,
    /// while the row whose key has arrived goes out.
    #[test]
    fn a_row_whose_key_has_not_arrived_is_withheld() {
        let mut lookup = keyed_rows(2, false);
        let out = lookup.get(lookup.tiling().universal_guard());
        assert_eq!(*out.key_levels()[0].1, ColumnValue::UInts(vec![0]));
        assert_eq!(
            scalar_tile_to_column_value(out.deepest_values().clone()),
            ColumnValue::Ints(vec![20])
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = &out
        else {
            panic!("the answer tiles as a collection: {out:?}")
        };
        assert!(!domain_predicate.contains_path(&[Value::UInt(1)]));
    }

    #[test]
    fn a_key_absent_from_a_complete_row_leaves_no_unfinished_output() {
        let mut lookup = keyed_rows(2, true);
        let output = lookup.get(lookup.tiling().universal_guard());
        assert_eq!(*output.key_levels()[0].1, ColumnValue::UInts(vec![0]));
        assert_eq!(
            scalar_tile_to_column_value(output.deepest_values().clone()),
            ColumnValue::Ints(vec![20])
        );
        assert!(output.is_terminal());
    }

    /// Three rows, each reading a key in its own collection whose values are `(key, group)`
    /// records, the group a collection beneath each entry. Row 0 reads `2` in
    /// `{1: (1, [5]), 2: (2, [6, 7])}`, rows 1 and 2 read `1` in `{1: (1, [8])}` and
    /// `{1: (1, [9])}`.
    ///
    /// Each read group is complete a different way: row 0's because the group's own level
    /// calls it complete, row 1's because its collection calls the entry complete, and row 2's
    /// not at all. The rows themselves are still growing.
    fn rows_reading_groups() -> (LookupProducer, Rc<std::cell::RefCell<Vec<TileGuard>>>) {
        let groups = Tile::grouped(
            vec![0, 1, 3, 4],
            ColumnValue::UInts(vec![0, 0, 1, 0, 0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 6, 7, 8, 9]))),
            Predicate::True.beneath(&[Value::UInt(0), Value::Int(2)], 0),
            BitSet::new(),
        );
        let entries = Tile::Record {
            fields: HashMap::from([
                (
                    tuple_field(0),
                    Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 1])),
                ),
                (tuple_field(1), groups),
            ]),
            absent: HashMap::new(),
        };
        let record = Tile::Record {
            fields: HashMap::from([
                (
                    tuple_field(0),
                    Tile::Scalar(ColumnValue::Ints(vec![2, 1, 1])),
                ),
                (
                    tuple_field(1),
                    Tile::grouped(
                        vec![0, 2, 3],
                        ColumnValue::Ints(vec![1, 2, 1, 1]),
                        Box::new(entries),
                        Predicate::exactly(&[Value::UInt(1), Value::Int(1)]),
                        BitSet::new(),
                    ),
                ),
            ]),
            absent: HashMap::new(),
        };
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2]),
            Box::new(record),
            Predicate::False,
            BitSet::new(),
        );
        let entry = Tiling::Record(HashMap::from([
            (tuple_field(0), Tiling::Scalar(int())),
            (
                tuple_field(1),
                Tiling::data_function(uint(), Tiling::Scalar(int())),
            ),
        ]));
        let tiling = Tiling::data_function(
            uint(),
            Tiling::Record(HashMap::from([
                (tuple_field(0), Tiling::Scalar(int())),
                (tuple_field(1), Tiling::data_function(int(), entry.clone())),
            ])),
        );
        let (spy, released) = ReleaseSpy::new(tile, tiling);
        let out = Tiling::data_function(uint(), entry);
        let lookup = LookupProducer {
            base: ProducerBase::unowned(LookupProducer::alloc_id(), &out),
            input: Box::new(spy),
            level: CurryLevel::new(1),
        };
        (lookup, released)
    }

    /// A value that is a record holding a collection is read whole: each row gets its entry's
    /// record, and the group in it moves from beneath the entry to beneath the row, complete
    /// exactly where the input called it complete.
    #[test]
    fn a_value_holding_a_collection_moves_beneath_its_row() {
        let (mut lookup, _) = rows_reading_groups();
        let out = lookup.get(lookup.tiling().universal_guard());
        let Tile::DataFunction {
            domain, codomain, ..
        } = &out
        else {
            panic!("the answer tiles as a collection: {out:?}")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![0, 1, 2]));
        let Tile::Record { fields, .. } = codomain.as_ref() else {
            panic!("each row holds its entry's record: {codomain:?}")
        };
        assert_eq!(
            fields[&tuple_field(0)],
            Tile::Scalar(ColumnValue::Ints(vec![2, 1, 1]))
        );
        let group = &fields[&tuple_field(1)];
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate,
            ..
        } = group
        else {
            panic!("each row's group is a level beneath it: {group:?}")
        };
        assert_eq!(*row_starts, vec![0, 2, 3]);
        assert_eq!(*domain, ColumnValue::UInts(vec![0, 1, 0, 0]));
        assert_eq!(
            **codomain,
            Tile::Scalar(ColumnValue::Ints(vec![6, 7, 8, 9]))
        );
        let at = |row: u64, key: u64| {
            domain_predicate.contains_path(&[Value::UInt(row), Value::UInt(key)])
        };
        assert!(
            at(0, 0) && at(0, 1),
            "row 0's group is complete: {domain_predicate:?}"
        );
        assert!(at(1, 0), "row 1's entry is complete: {domain_predicate:?}");
        assert!(
            !at(2, 0),
            "nothing calls row 2's group complete: {domain_predicate:?}"
        );
    }

    /// Releasing part of a row's group releases the same part beneath every key of that row's
    /// collection, the row's key and the collection's keys staying.
    #[test]
    fn releasing_part_of_a_read_group_releases_it_beneath_the_keys() {
        let (mut lookup, released) = rows_reading_groups();
        lookup.get(lookup.tiling().universal_guard());
        let first_of_row_0 = Predicate::qualified(
            Predicate::exactly(&[Value::UInt(0)]),
            Predicate::point(Value::UInt(0)),
        );
        let group_part = |pred: Predicate| {
            TileGuard::Record(HashMap::from([
                (tuple_field(0), TileGuard::Scalar(Predicate::False)),
                (
                    tuple_field(1),
                    TileGuard::Function(FunctionGuard::Domain(pred)),
                ),
            ]))
        };
        lookup.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            group_part(first_of_row_0),
        ))));
        let beneath_every_key = Predicate::qualified(
            Predicate::qualified(Predicate::exactly(&[Value::UInt(0)]), Predicate::True),
            Predicate::point(Value::UInt(0)),
        );
        let expected = TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Record(
            HashMap::from([
                (tuple_field(0), TileGuard::Scalar(Predicate::False)),
                (
                    tuple_field(1),
                    TileGuard::Function(FunctionGuard::Codomain(Box::new(group_part(
                        beneath_every_key,
                    )))),
                ),
            ]),
        ))));
        assert_eq!(*released.borrow(), vec![expected]);
    }
}

#[cfg(test)]
mod empty_lookup_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::TestTileProducer;

    #[test]
    fn bare_lookup_waits_for_its_input() {
        let extent = Extent::Base(crate::interpreter::BaseType::Int);
        let input_tiling = Tiling::tuple(&[
            Tiling::Scalar(extent.clone()),
            Tiling::data_function(extent.clone(), Tiling::Scalar(extent.clone())),
        ]);
        let out = Tiling::Scalar(extent);
        let mut lookup = LookupProducer {
            base: ProducerBase::unowned(LookupProducer::alloc_id(), &out),
            input: Box::new(TestTileProducer::new(
                input_tiling.empty_at_no_rows(),
                input_tiling,
            )),
            level: CurryLevel::OUTERMOST,
        };
        assert!(lookup.get(out.universal_guard()).is_empty());
    }
}

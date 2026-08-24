use bit_set::BitSet;

use super::*;
use crate::{
    ccl::FieldKey,
    interpreter::{ColumnValue, Consumer, Scheduler, Value, tiling::FunctionGuard, tuple_field},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// CheckedLookup / CheckedLookupProducer
// ---------------------------------------------------------------------------

/// The checked lookup `c[k]?` — decide whether `k` is a key of `c`, and answer
/// `` `some(c(k)) `` or `` `none ``.
///
/// **Membership is decided here, not read off an empty tile.** A collection is a total
/// function on its own domain, so applying it at a key outside that domain is not an
/// operation the type system offers; what `c[k]?` returns is a tagged sum, and producing
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
    /// Where the collection and the keys come from — see [`LookupSource`].
    source: LookupSource,
    /// The answer, one `` {`none | `some{𝑉}} `` per key.
    tiling: Tiling,
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
    /// takes the keys' shape: a scalar for `m[1]?`, a stream wherever the keys are one.
    pub fn split(
        collection: Box<dyn TileOperator>,
        keys: Box<dyn TileOperator>,
        option_extent: Extent,
    ) -> Self {
        let tiling = answer_tiling(keys.tiling(), option_extent);
        Self {
            source: LookupSource::Split { collection, keys },
            tiling,
        }
    }

    /// Look each row's key up in that row's collection, over an assembled stream of
    /// `(collection, key)` pairs. The answer's domain is the stream's own.
    pub fn paired(pairs: Box<dyn TileOperator>, option_extent: Extent) -> Result<Self, String> {
        let Tiling::SealedFunction { domain, codomain } = pairs.tiling() else {
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
        // Field 0 is the collection. A nested function tiling is one collection shared by
        // every row; a scalar is a materialized map value per row. Anything else is a
        // collection whose values are themselves collections, which has no answer shape.
        let collection = fields
            .get(&tuple_field(0))
            .ok_or_else(|| "`lookup?`'s input rows have no collection field".to_string())?;
        match collection {
            Tiling::SealedFunction { .. } | Tiling::Scalar(Extent::Function { .. }) => {}
            other => {
                return Err(format!(
                    "`c[k]?` over a collection whose values are themselves collections is not \
                     supported yet: the answer would carry a collection as its `some` \
                     payload, and its tiling is {other}"
                ));
            }
        }
        let tiling = Tiling::SealedFunction {
            domain: domain.clone(),
            codomain: Box::new(Tiling::Scalar(option_extent)),
        };
        Ok(Self {
            source: LookupSource::Paired(pairs),
            tiling,
        })
    }
}

/// The answer's tiling for a given key tiling: one option per key, in the keys' own shape.
fn answer_tiling(keys: &Tiling, option_extent: Extent) -> Tiling {
    match keys {
        Tiling::Scalar(_) => Tiling::Scalar(option_extent),
        Tiling::SealedFunction { domain, .. } => Tiling::SealedFunction {
            domain: domain.clone(),
            codomain: Box::new(Tiling::Scalar(option_extent)),
        },
        other => panic!("CheckedLookup keys must be a scalar or a stream, got {other}"),
    }
}

impl TileOperator for CheckedLookup {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        match &self.source {
            LookupSource::Split { collection, keys } => node
                .child("collection", collection.inspect(opts))
                .child("keys", keys.inspect(opts)),
            LookupSource::Paired(pairs) => node.child("pairs", pairs.inspect(opts)),
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // The keys drive the answer, so they take the consumer's wake-up; the collection is
        // read on demand and wakes nobody of its own.
        let source = match &mut self.source {
            LookupSource::Split { collection, keys } => {
                let keys = keys.subscribe(keys.tiling().universal_guard(), consumer, scheduler);
                let collection = collection.subscribe(
                    collection.tiling().universal_guard(),
                    Box::new(|| {}),
                    scheduler,
                );
                ProducerSource::Split { collection, keys }
            }
            LookupSource::Paired(pairs) => ProducerSource::Paired(pairs.subscribe(
                pairs.tiling().universal_guard(),
                consumer,
                scheduler,
            )),
        };
        Box::new(CheckedLookupProducer {
            base: ProducerBase::new(CheckedLookupProducer::alloc_id(), &self.tiling),
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
        tag: FieldKey::Name(crate::ccl::V_SOME.into()),
        inner: Box::new(v),
    }
}

/// `` `none `` — the tag a decided absence answers with.
fn none() -> Value {
    Value::Union {
        tag: FieldKey::Name(crate::ccl::V_NONE.into()),
        inner: Box::new(Value::Unit),
    }
}

/// The answer for one key against a **materialized** map value.
///
/// A map value is a binding list, so it carries its own keys: it is complete wherever it is
/// present, and absence needs no terminality wait. This is how a mutable collection's
/// register holds its collection, at one store key.
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
        Tile::SealedFunction {
            domain, codomain, ..
        } => match (0..domain.len()).find(|&i| &domain.index_at(i) == key) {
            Some(i) => {
                let Tile::Scalar(values) = codomain.as_ref() else {
                    return None;
                };
                Some(some_of(values.index_at(i)))
            }
            None if coll.is_terminal() => Some(none()),
            None => None,
        },
        Tile::Scalar(col) if !col.is_empty() => Some(answer_in_value(key, &col.index_at(0))),
        // A materialized collection that has not arrived yet.
        Tile::Scalar(_) => None,
        other => panic!("CheckedLookup: collection is not a collection: {other:?}"),
    }
}

/// How the rows of an assembled `(collection, key)` stream supply their collection.
enum RowCollection<'a> {
    /// One collection shared by every row — the collection leg was closed in the iteration,
    /// so `zip` fanned it in as a constant and it arrives as a nested function tile.
    Shared(&'a Tile),
    /// One materialized map value per row, as a mutable collection's register gives.
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

impl TileProducer for CheckedLookupProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        match &self.source {
            ProducerSource::Split { collection, keys } => node
                .child("collection", collection.inspect(opts))
                .child("keys", keys.inspect(opts)),
            ProducerSource::Paired(pairs) => node.child("pairs", pairs.inspect(opts)),
        }
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let out_extent = match self.tiling() {
            Tiling::Scalar(e) => e.clone(),
            Tiling::SealedFunction { codomain, .. } => codomain.extent(),
            other => panic!("CheckedLookup tiling is a scalar or a stream, got {other}"),
        };
        let empty_scalar = Tile::Scalar(ColumnValue::from_values(vec![], &out_extent));
        if self.released {
            return empty_scalar;
        }
        match &mut self.source {
            ProducerSource::Split { collection, keys } => {
                let key_tile = keys.get(keys.tiling().universal_guard());
                let coll = collection.get(collection.tiling().universal_guard());
                match key_tile {
                    // One key: the scalar form `m[k]?`.
                    Tile::Scalar(keys) if !keys.is_empty() => {
                        match answer_for(&keys.index_at(0), &coll) {
                            Some(v) => Tile::Scalar(ColumnValue::from_values(vec![v], &out_extent)),
                            None => empty_scalar,
                        }
                    }
                    // A stream of keys, each answered against the same collection — read
                    // once, not lifted into every row.
                    Tile::SealedFunction {
                        ref domain,
                        ref codomain,
                        ref domain_predicate,
                        ref deleted,
                    } => {
                        let Tile::Scalar(key_col) = codomain.as_ref() else {
                            return empty_scalar;
                        };
                        let (kept, answers) =
                            Self::answer_rows(domain, key_col, &RowCollection::Shared(&coll));
                        self.stream_tile(kept, answers, domain_predicate, deleted, &out_extent)
                    }
                    _ => empty_scalar,
                }
            }
            // An assembled stream of `(collection, key)` rows.
            ProducerSource::Paired(pairs) => {
                let tile = pairs.get(pairs.tiling().universal_guard());
                let Tile::SealedFunction {
                    ref domain,
                    ref codomain,
                    ref domain_predicate,
                    ref deleted,
                } = tile
                else {
                    return empty_scalar;
                };
                let Tile::Record(fields) = codomain.as_ref() else {
                    return empty_scalar;
                };
                let (Some(coll_tile), Some(Tile::Scalar(key_col))) =
                    (fields.get(&tuple_field(0)), fields.get(&tuple_field(1)))
                else {
                    return empty_scalar;
                };
                let collection = match coll_tile {
                    Tile::Scalar(col) => RowCollection::PerRow(col),
                    shared => RowCollection::Shared(shared),
                };
                let (kept, answers) = Self::answer_rows(domain, key_col, &collection);
                self.stream_tile(kept, answers, domain_predicate, deleted, &out_extent)
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
    fn stream_tile(
        &self,
        kept: Vec<Value>,
        answers: Vec<Value>,
        domain_predicate: &Predicate,
        deleted: &BitSet,
        out_extent: &Extent,
    ) -> Tile {
        let Tiling::SealedFunction {
            domain: dom_ext, ..
        } = self.tiling()
        else {
            panic!("CheckedLookup answers a stream when its keys are one")
        };
        Tile::SealedFunction {
            domain: ColumnValue::from_values(kept, dom_ext),
            codomain: Box::new(Tile::Scalar(ColumnValue::from_values(answers, out_extent))),
            domain_predicate: domain_predicate.clone(),
            deleted: deleted.clone(),
        }
    }
}

use super::*;
use crate::{
    ccl::FieldKey,
    interpreter::{ColumnValue, Consumer, Scheduler, Value, tiling::FunctionGuard},
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
    /// The collection to look keys up in — a streamed `SealedFunction`, or a `Scalar`
    /// holding one materialized map value as a mutable collection's register does.
    collection: Box<dyn TileOperator>,
    /// The keys, taking the shape the surrounding chain feeds.
    keys: Box<dyn TileOperator>,
    /// The answer, one `` {`none | `some{𝑉}} `` per key.
    tiling: Tiling,
}

impl CheckedLookup {
    /// Look keys up in `collection`. `keys` is the input the surrounding chain feeds — a
    /// scalar for `m[1]?`, a stream wherever the lookup sits in an iteration — and the
    /// answer takes its shape from it.
    pub fn new(
        collection: Box<dyn TileOperator>,
        keys: Box<dyn TileOperator>,
        option_extent: Extent,
    ) -> Self {
        let tiling = match keys.tiling() {
            Tiling::Scalar(_) => Tiling::Scalar(option_extent),
            Tiling::SealedFunction { domain, .. } => Tiling::SealedFunction {
                domain: domain.clone(),
                codomain: Box::new(Tiling::Scalar(option_extent)),
            },
            other => panic!("CheckedLookup keys must be a scalar or a stream, got {other}"),
        };
        Self {
            collection,
            keys,
            tiling,
        }
    }
}

impl TileOperator for CheckedLookup {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("collection", self.collection.inspect(opts))
            .child("keys", self.keys.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let keys = self
            .keys
            .subscribe(self.keys.tiling().universal_guard(), consumer, scheduler);
        let collection = self.collection.subscribe(
            self.collection.tiling().universal_guard(),
            Box::new(|| {}),
            scheduler,
        );
        Box::new(CheckedLookupProducer {
            base: ProducerBase::new(CheckedLookupProducer::alloc_id(), &self.tiling),
            collection,
            keys,
            released: false,
        })
    }
}

struct CheckedLookupProducer {
    base: ProducerBase,
    collection: Box<dyn TileProducer>,
    keys: Box<dyn TileProducer>,
    released: bool,
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

impl CheckedLookupProducer {
    /// The answer for one key, or `None` while the collection is still deciding.
    ///
    /// A collection carries its keys in the domain column, so an absent key is only an
    /// answer once that domain is decided.
    fn answer_for(&self, key: &Value, coll: &Tile) -> Option<Value> {
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
            other => panic!("CheckedLookup: collection is not a stream: {other:?}"),
        }
    }
}

impl TileProducer for CheckedLookupProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("collection", self.collection.inspect(opts))
            .child("keys", self.keys.inspect(opts))
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
        let key_tile = self.keys.get(self.keys.tiling().universal_guard());
        let coll = self
            .collection
            .get(self.collection.tiling().universal_guard());
        match key_tile {
            // One key: the scalar form `m[k]?`.
            Tile::Scalar(keys) if !keys.is_empty() => {
                match self.answer_for(&keys.index_at(0), &coll) {
                    Some(v) => Tile::Scalar(ColumnValue::from_values(vec![v], &out_extent)),
                    None => empty_scalar,
                }
            }
            // A stream of keys: the lookup sits in an iteration, and each row is answered
            // against the same collection — read once, not lifted into every row.
            Tile::SealedFunction {
                ref domain,
                ref codomain,
                ref domain_predicate,
                ref deleted,
            } => {
                let Tile::Scalar(key_col) = codomain.as_ref() else {
                    return empty_scalar;
                };
                // A key the collection has not decided yet contributes no row, so the
                // answer is a *prefix* of the key stream and grows with it. Keeping the
                // rows aligned means carrying each answered key's own domain position.
                let mut kept: Vec<Value> = Vec::with_capacity(domain.len());
                let mut answers: Vec<Value> = Vec::with_capacity(domain.len());
                for i in 0..domain.len() {
                    if let Some(v) = self.answer_for(&key_col.index_at(i), &coll) {
                        kept.push(domain.index_at(i));
                        answers.push(v);
                    }
                }
                let Tiling::SealedFunction {
                    domain: dom_ext, ..
                } = self.tiling()
                else {
                    panic!("CheckedLookup answers a stream when its keys are one")
                };
                let domain_extent = dom_ext.clone();
                Tile::SealedFunction {
                    domain: ColumnValue::from_values(kept, &domain_extent),
                    codomain: Box::new(Tile::Scalar(ColumnValue::from_values(
                        answers,
                        &out_extent,
                    ))),
                    domain_predicate: domain_predicate.clone(),
                    deleted: deleted.clone(),
                }
            }
            _ => empty_scalar,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A **domain** release names positions of the answer, and the answer is one option per
        // key at the key's own domain position — so it names key positions and passes through
        // to the keys. The **collection** is not positional: every key is answered against the
        // whole of it, so no key being finished releases any part of it. That asymmetry is why
        // the two legs are released separately rather than together.
        if let TileGuard::Function(FunctionGuard::Domain(_)) = &obsolete_guard {
            self.keys.release(obsolete_guard);
            return;
        }
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.collection
                .release(self.collection.tiling().universal_guard());
            self.keys.release(self.keys.tiling().universal_guard());
        }
    }
}

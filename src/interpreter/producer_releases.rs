//! Per-producer release bookkeeping for a data source.

use std::collections::HashMap;

use crate::interpreter::tiling::Predicate;

/// What each producer reading a data source has released, and what a producer
/// registering from now on starts having released.
///
/// A source retains a value until every producer reading it is finished with it,
/// so the intersection of these — the agreement — is what it may drop. Every
/// source keeps this, and keeps it the same way; naming it once is what makes
/// carrying the agreement across a version handover a property of a source rather
/// than of whichever ones happen to store their releases alike.
#[derive(Debug)]
pub(crate) struct ProducerReleases {
    /// What each producer has released, accumulated by union across its releases.
    per_producer: HashMap<String, Predicate>,
    /// What a producer registering from now on is recorded as having already
    /// released.
    ///
    /// `False` until [`carry_to_new_producers`](Self::carry_to_new_producers)
    /// sets it, so a program's own producers — which all register before it
    /// starts consuming — read everything the source holds, including whatever
    /// arrived while the program was being compiled.
    on_registration: Predicate,
}

impl Default for ProducerReleases {
    fn default() -> Self {
        Self {
            per_producer: HashMap::new(),
            on_registration: Predicate::False,
        }
    }
}

impl ProducerReleases {
    /// Accumulate `obsolete` into `producer`'s record, registering it at
    /// [`on_registration`](Self::on_registration) if this is its first release.
    pub(crate) fn record(&mut self, producer: &str, obsolete: &Predicate) {
        let recorded = self
            .per_producer
            .entry(producer.to_string())
            .or_insert_with(|| self.on_registration.clone());
        *recorded = recorded.union(obsolete);
    }

    /// What `producer` has released, or `None` for one that has never released.
    pub(crate) fn of(&self, producer: &str) -> Option<&Predicate> {
        self.per_producer.get(producer)
    }

    /// What every registered producer has released — what the source may drop,
    /// and what a producer registering from now on may skip.
    ///
    /// Nobody registered means nobody has released anything. The fold's identity
    /// is the universal predicate, which for an empty producer list would
    /// otherwise read as "everything".
    pub(crate) fn agreed(&self) -> Predicate {
        if self.per_producer.is_empty() {
            return Predicate::False;
        }
        self.per_producer
            .values()
            .fold(Predicate::True, |agreed, released| {
                agreed.intersect(released)
            })
    }

    /// Record the agreement as the starting point for producers registering from
    /// now on.
    ///
    /// Called when a running program is replaced
    /// ([`LiveProgram::update`](crate::live_program::LiveProgram::update)). The
    /// operators the replacement rebuilds register as new producers, and a source
    /// hands a newly-registered one everything it has retained, so without this
    /// the replacement recomputes the program's history instead of continuing it
    /// and re-emits an output for every input the replaced version answered.
    ///
    /// The agreement is the safe answer: an index some producer has not finished
    /// with is not skipped, so an element that arrived but went unhandled is still
    /// delivered to whoever takes over.
    pub(crate) fn carry_to_new_producers(&mut self) {
        self.on_registration = self.agreed();
    }

    /// What a producer registering now is recorded as having already released.
    pub(crate) fn on_registration(&self) -> &Predicate {
        &self.on_registration
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::Value;

    /// Nobody registered has released nothing, not everything — the fold's
    /// identity is the universal predicate, so an empty list has to be answered
    /// before the fold rather than by it.
    #[test]
    fn an_unread_source_has_released_nothing() {
        assert_eq!(ProducerReleases::default().agreed(), Predicate::False);
    }

    /// A producer's releases accumulate, and the agreement is the part every
    /// producer is finished with — so one producer lagging holds the whole
    /// agreement at where it has got to.
    #[test]
    fn the_agreement_is_where_the_slowest_producer_has_reached() {
        let mut releases = ProducerReleases::default();
        releases.record("a", &Predicate::LessThanEq(Value::UInt(1)));
        releases.record("a", &Predicate::LessThanEq(Value::UInt(4)));
        releases.record("b", &Predicate::LessThanEq(Value::UInt(2)));
        assert_eq!(releases.agreed(), Predicate::LessThanEq(Value::UInt(2)));
    }

    /// A producer registering before the carry reads everything the source holds;
    /// one registering after starts at the agreement, which is what makes a
    /// rebuilt operator continue the stream rather than reprocess it.
    #[test]
    fn a_producer_registering_after_the_carry_starts_at_the_agreement() {
        let mut releases = ProducerReleases::default();
        releases.record("a", &Predicate::LessThanEq(Value::UInt(2)));
        assert_eq!(releases.on_registration(), &Predicate::False);

        releases.carry_to_new_producers();
        assert_eq!(
            releases.on_registration(),
            &Predicate::LessThanEq(Value::UInt(2))
        );

        // The newcomer counts as having released the agreement even before it
        // releases anything itself, so it neither re-reads what is gone nor holds
        // the agreement back to nothing.
        releases.record("b", &Predicate::False);
        assert_eq!(releases.agreed(), Predicate::LessThanEq(Value::UInt(2)));
    }
}

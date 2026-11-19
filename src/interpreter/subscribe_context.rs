//! What a `TileOperator::subscribe` records about the producers it builds.

use super::{SourceRegistry, value_probe::ProbeSlot};

/// What a `subscribe` records about the producers it builds: the probe slot each takes, and the
/// source producers each compilation and fan-out registered. A `GlobalContext` owns one as long
/// as it lives, and lends it to every `TileOperator::subscribe` of its compilations.
#[derive(Default)]
pub struct SubscribeContext {
    probes: ProbeSlot,
    /// The source producers registered under each subscription still in progress, innermost last
    /// ([`begin_source_producers`](Self::begin_source_producers)).
    producer_frames: Vec<Vec<String>>,
    /// Source lifetimes and notification registrations.
    sources: SourceRegistry,
}

impl SubscribeContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// The probe slot every producer subscribed under this context holds. Every `subscribe`
    /// receives the context, so a producer takes the slot at construction with no ambient state.
    pub fn probes(&self) -> &ProbeSlot {
        &self.probes
    }

    /// Open a frame recording every producer that registers with a data source until the matching
    /// [`end_source_producers`](Self::end_source_producers).
    ///
    /// A source producer is attributed to whatever subscribed it, so the branch table can say which
    /// producers a branch holds: a fan-out records the producers its input chain registered, and a
    /// compilation the producers its outputs registered (`src/ccl/design/program-evolution.md`,
    /// "Routes across branches"). Frames nest, because a fan-out's input is subscribed from inside
    /// a compilation's.
    pub fn begin_source_producers(&mut self) {
        self.producer_frames.push(Vec::new());
    }

    /// Close the innermost frame and return the producers registered in it.
    ///
    /// The producers are also added to the enclosing frame, so a frame's record covers every
    /// producer registered below it, including those under a nested fan-out.
    pub fn end_source_producers(&mut self) -> Vec<String> {
        let producers = self
            .producer_frames
            .pop()
            .expect("`end_source_producers` closes a frame `begin_source_producers` opened");
        if let Some(outer) = self.producer_frames.last_mut() {
            outer.extend(producers.iter().cloned());
        }
        producers
    }

    /// Record that the producer named `producer` registered with a data source.
    ///
    /// A registration outside every frame is attributed to nothing. Only a subscription made
    /// outside a compilation does that, which a test that subscribes an operator by hand is.
    pub fn note_source_producer(&mut self, producer: String) {
        if let Some(frame) = self.producer_frames.last_mut() {
            frame.push(producer);
        }
    }

    /// The sources and notification registrations owned by this context.
    pub fn source_registry(&mut self) -> &mut SourceRegistry {
        &mut self.sources
    }
}

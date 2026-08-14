//! Lineage data model: the per-pass rewrite log and the fold that collapses it
//! into a node↔node relation plus a source-span projection.
//!
//! # The model
//!
//! Every IR node has a stable [`NodeId`]. As a pass rewrites the tree it appends
//! [`RewriteStep`]s to a [`LineageLog`]: a [`Op::Transform`] records "these input
//! ids vanished, these output ids appeared"; a [`Op::Copy`] records "these output
//! ids are freshened duplicates of that origin." Each step *separately* carries a
//! `blame` set (the upstream ids the outputs attribute to — **not** the same as
//! what they consumed), a `nature` bit (faithful expansion vs. pure machinery),
//! and a stable `label`. An untouched id is one no step mentions.
//!
//! At an inspector pane boundary the intervening logs are folded once, in pass
//! order, by [`collapse`] into a [`LineageMap`] — a bidirectional node↔node
//! relation with an explicit self-edge for every id that survived — and, in
//! parallel, into a [`SourceProjection`] that resolves each surviving node's
//! blame back to source spans. The fold composes away ids born and consumed
//! within the phase, and its two-sided leak check ([`Leak`]) guarantees no node
//! silently loses its history.
//!
//! # Two independent channels (load-bearing)
//!
//! `consumed` and `blame` are distinct and never mixed:
//!
//! * **`consumed`** drives *fate* accounting — an id is consumed, carried, or
//!   dropped — and the leak audit. Lineage edges resolve through the `roots`
//!   state, which only `consumed`/`produced` move.
//! * **`blame`** drives *span* resolution and may name ids that survive the step.
//!   It resolves through the `attr` projection, never through `roots`.
//!
//! Welding the two would (for example) resolve a channelized feed union — whose
//! step consumes the enclosing `Defer`/`Let` but blames the surviving fed-value
//! operands — to the `defer` keyword's span rather than the operands'.
//!
//! # Domains, not passes
//!
//! [`LineageMap`] is generic over its two id domains so the same relation serves
//! lowering's `SourceKey → NodeId` projection, a pane pair's `NodeId → NodeId`, and a
//! future `NodeId → OperatorId` edge. Passes live in the *data* (each step's
//! `via`/`label`), never in the type.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::ccl::provenance::{NodeId, Pass};
use crate::chl_parser::ast::Span;

/// A stable, human-readable name for a rewrite, e.g. `"channelize.feed_union"`
/// or `"inline.fanout"`. Carried on every [`RewriteStep`] and surfaced through
/// [`RewriteTag`] for inspector tooltips.
pub type RewriteLabel = &'static str;

/// One rewrite's identity relation, in a single hop.
///
/// Appended to a [`LineageLog`] while a pass runs. The two channels it carries —
/// the `op`'s consumed/produced/origin ids and the separate `blame` ids — are
/// resolved independently at [`collapse`] time (see the module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
// Consumed when the passes adopt the recorder (next commit in the stack).
pub(crate) struct RewriteStep {
    /// The identity relation this step performs.
    pub op: Op,
    /// Upstream ids the outputs *attribute* to — separate from `op`'s consumed
    /// set (blame ⊥ consumption). May name ids that survive the step. Resolved
    /// to spans at collapse through the projection being built, never through
    /// the lineage `roots`.
    pub blame: Vec<NodeId>,
    /// Faithful expansion of a user construct vs. pure machinery. The one bit
    /// the collapsed graph cannot recover; display policy derives from it later.
    pub nature: Nature,
    /// Stable rewrite label for tooling.
    pub label: RewriteLabel,
}

/// The identity relation a [`RewriteStep`] performs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    /// `consumed` ids vanish; `produced` ids appear. Empty `produced` = discard.
    ///
    /// An id in `consumed ∩ produced` **survives while absorbing**: the fold
    /// removes every consumed root, unions them (including the surviving id's
    /// own), and assigns that union to each produced id — so a carried id keeps
    /// its own lineage plus the lineage of what it absorbed.
    Transform {
        /// Ids that vanish. Each must be live at the step, else
        /// [`Leak::ConsumedUnknown`].
        consumed: Vec<NodeId>,
        /// Ids that appear. A live id here that was not also consumed is a lying
        /// step, [`Leak::ProducedLive`].
        produced: Vec<NodeId>,
    },
    /// `produced` ids mirror `origin`'s lineage (freshened copies). Silent on
    /// the origin's own fate — the origin stays live, so a later step may still
    /// consume it while the copies retain the lineage snapshotted here.
    Copy {
        /// The id whose lineage is mirrored. Must be live, else
        /// [`Leak::CopyOfUnknown`].
        origin: NodeId,
        /// The freshened copies.
        produced: Vec<NodeId>,
    },
}

/// The fidelity of a node to its blamed source — the one fact the collapsed
/// graph cannot recover. A trinary axis.
///
/// **Work in progress.** This axis exists to carry display metadata to the
/// inspector frontend, and neither the vocabulary nor the tagging is settled: the
/// three variants are a first cut, the rule assigning them is deliberately
/// structural for now (below), and `Expansion` has no production producer yet.
/// Treat a node's nature as a hint the frontend may present, not as a fact any
/// compiler decision should turn on — nothing in `ccl/` branches on it today, and
/// the per-site `label` is the durable datum. Retagging is cheap precisely
/// because of that: a label-keyed remap can recompute a different taxonomy
/// without touching how any pass records.
///
/// Public because it rides in the public [`RewriteTag`] (and thus
/// [`SourceAttribution`]); the recorder-facing [`RewriteStep`] carries it too.
///
/// [`Source`](Nature::Source) is listed first because it is the base case: the
/// root of a lowered source expression. The rule for who gets it is *structural*
/// and stated in one place — see `LoweringContext::tag_source` in
/// `src/ccl/lower/mod.rs`, and `design/provenance.md`, "The seam
/// (`src/ccl/context.rs`)". It is emitted **only by lowering** — the fold's
/// attributing arms and both wire validators carry debug guards that no *pass*
/// step ever carries it. On the wire a `Source`-nature tag null-compresses
/// (serializes as
/// `rewritten: null` via [`is_source`](Nature::is_source)) so the wire stays
/// byte-identical to the retired `rewritten: None` encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Nature {
    /// The node is the root of a lowered source expression. Lowering-only;
    /// guarded off the pass logs and off the wire. Note this is a *positional*
    /// fact, not "images something the user wrote" — an interior image (a call's
    /// callee, a chained comparison's operands) carries `Machinery` with the
    /// `"lower.image"` label instead.
    Source,
    /// Faithful expansion of a source construct (a comparison chain, a
    /// comprehension, a lambda-elim combinator).
    Expansion,
    /// Pure plumbing with no direct source counterpart.
    Machinery,
}

impl Nature {
    /// The lowercase wire discriminant (`"source"` / `"expansion"` /
    /// `"machinery"`), shared by the per-node `ir` tree tag and the
    /// `SourceAttribution` query wire so the two encodings never diverge.
    ///
    /// `"source"` must **never** actually reach the wire — a `Source`-nature tag
    /// null-compresses at the emission sites (see [`is_source`](Self::is_source));
    /// the arm exists for the validators' guard and for completeness.
    ///
    /// Compiled only under the `serde` feature (the `Serialize` impl below is its
    /// sole caller), so a default build sees it as dead.
    #[allow(dead_code)]
    pub(crate) fn wire_str(self) -> &'static str {
        match self {
            Nature::Source => "source",
            Nature::Expansion => "expansion",
            Nature::Machinery => "machinery",
        }
    }

    /// Whether this is the [`Source`](Self::Source) direct-image nature — the
    /// wire null-compression predicate. A `SourceAttribution` whose tag
    /// `is_source()` serializes its `rewritten` as `null`.
    pub(crate) fn is_source(self) -> bool {
        matches!(self, Nature::Source)
    }
}

/// A pass's ordered rewrite record. Passes append; the fold reads.
pub(crate) type LineageLog = Vec<RewriteStep>;

/// Lowering's log entry: the same [`Op`]s a
/// [`RewriteStep`] carries, but anchored by literal source **spans** rather than
/// NodeId blame.
///
/// The distinction from [`RewriteStep::blame`] is load-bearing and is exactly
/// why this is a *sibling* struct rather than one type generic over its
/// attribution domain: an **`anchor`** is a literal span *attached* at
/// construction (lowering knows the source token it is imaging right there),
/// whereas `blame` is a NodeId *reference resolved* later through the
/// accumulating projection (a pass names an upstream id whose spans it does not
/// itself hold). Attached-literal vs resolved-through-state are different
/// semantics, not two instances of one thing — and thread-local statics cannot
/// be generic, so a blame-domain generic would erase to the same at the
/// recorder boundary anyway. There is no NodeId-blame field: the one site that
/// would name an upstream id — a substitution, whose replacement takes the
/// replaced occurrence's attribution — carries the occurrence's identity instead
/// (`crate::ccl::subst`'s `as_expr_preserving`), so there is no id left to
/// resolve. Add one when a site demands it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LoweringStep {
    /// The identity relation this step performs. For lowering: a leaf mint is a
    /// `Transform { consumed: [], produced: [id] }` (pure insertion); a copy
    /// site is a `Copy { origin, produced }`.
    pub op: Op,
    /// The literal source spans the produced nodes image, attached here at
    /// construction. Empty for a `Copy` (it mirrors its origin's folded entry).
    pub anchor: Vec<Span>,
    /// `Source` for a direct image, `Machinery` for manufactured plumbing
    /// (`Expansion` is unused at lowering sites — the split folds into
    /// `Machinery`, the per-rule label being the primary datum).
    pub nature: Nature,
    /// Stable rewrite label for tooling (`"lower.image"`, `"lower.<rule>"`).
    pub label: RewriteLabel,
}

/// Lowering's ordered record. Appended at leaf grain by
/// [`lowering_leaf`]/the copy frames; folded once at the lowering boundary by
/// [`collapse_lowering`] into the always-on lowering projection.
pub(crate) type LoweringLog = Vec<LoweringStep>;

/// A collapsed bidirectional relation between two id domains.
///
/// **Dense**: an id that survived a phase appears as its own self-edge, so there
/// is one uniform edge kind and no identity special case. Self-edges are
/// derivable (an id present in both snapshots is its own edge), so a later
/// sparse re-encoding behind the accessors is a pure re-encoding — consumers
/// must go through [`upstream`](Self::upstream) / [`downstream`](Self::downstream)
/// / [`edges`](Self::edges) and never touch the raw maps.
pub struct LineageMap<U, D> {
    /// upstream → downstream (fan-out).
    down: HashMap<U, Vec<D>>,
    /// downstream → upstream (origins).
    up: HashMap<D, Vec<U>>,
}

impl<U, D> LineageMap<U, D>
where
    U: Eq + Hash + Copy + Ord,
    D: Eq + Hash + Copy + Ord,
{
    /// The upstream origins of a downstream id (empty if the id is unknown to
    /// the map). Sorted, deduplicated.
    pub fn upstream(&self, d: &D) -> &[U] {
        self.up.get(d).map_or(&[], Vec::as_slice)
    }

    /// The downstream fan-out of an upstream id (empty if the id is unknown to
    /// the map). Sorted, deduplicated.
    pub fn downstream(&self, u: &U) -> &[D] {
        self.down.get(u).map_or(&[], Vec::as_slice)
    }

    /// Every `(upstream, downstream)` edge, in deterministic order. Includes the
    /// dense self-edges.
    pub fn edges(&self) -> Vec<(U, D)> {
        let mut out: Vec<(U, D)> = self
            .up
            .iter()
            .flat_map(|(d, us)| us.iter().map(move |u| (*u, *d)))
            .collect();
        out.sort_unstable();
        out
    }
}

/// A pane node's source attribution — the blame channel's terminal form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceAttribution {
    /// Source spans this node traces to. **Empty** = machinery with no source
    /// anchor (a *known* node with no span) — deliberately distinct from a node
    /// that is absent from the [`SourceProjection`] entirely (a node the
    /// projection knows nothing about).
    pub spans: Vec<Span>,
    /// How the node came to exist — **mandatory**. A direct image is
    /// [`RewriteTag::direct_image`] (`{via: Lower, nature: Source, label:
    /// "lower.image"}`), never an absence; every other tag names the rewrite
    /// that produced the node. Null-compressed on the wire when the tag
    /// [`is_source`](Nature::is_source).
    pub rewritten: RewriteTag,
}

// Wire shape (inspector, feature `serde`): the attribution ships natively. The
// query endpoints (`/api/resolve`, `/api/hover`) carry a `SourceAttribution` as
// `{ spans, rewritten: null | { via, nature, label } }` — the same two-channel
// shape the per-node `ir` tree carries (spans + rewrite tag), letting the
// frontend format the tag itself rather than consuming a pre-flattened string.
//
// Null-compression: a `Source`-nature tag (a direct image) serializes its
// `rewritten` as `null`. Both validators carry a debug guard that a `"source"`
// nature never actually ships, so this compression boundary cannot rot.
#[cfg(feature = "serde")]
impl serde::Serialize for SourceAttribution {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        /// The wire form of a [`RewriteTag`]: `via` as the `Pass` debug name,
        /// `nature` as the lowercase discriminant, `label` verbatim.
        #[derive(serde::Serialize)]
        struct WireTag {
            via: String,
            nature: &'static str,
            label: &'static str,
        }

        // Direct images null-compress: a Source-nature tag ships as `null`.
        let rewritten = if self.rewritten.nature.is_source() {
            None
        } else {
            Some(WireTag {
                via: format!("{:?}", self.rewritten.via),
                nature: self.rewritten.nature.wire_str(),
                label: self.rewritten.label,
            })
        };
        let mut s = serializer.serialize_struct("SourceAttribution", 2)?;
        s.serialize_field("spans", &self.spans)?;
        s.serialize_field("rewritten", &rewritten)?;
        s.end()
    }
}

/// How a rewritten node came to exist, for tooltips and display policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RewriteTag {
    /// The pass that performed the rewrite.
    pub via: Pass,
    /// Faithful expansion vs. pure machinery vs. direct source image.
    pub nature: Nature,
    /// The rewrite's stable label.
    pub label: RewriteLabel,
}

impl RewriteTag {
    /// The tag a **lowered expression root** carries: `{via: Lower, nature:
    /// Source, label: "lower.image"}` — a tag, never an absence.
    ///
    /// An interior image shares the `"lower.image"` label but carries
    /// `Nature::Machinery`, per the structural rule on
    /// `LoweringContext::tag_source`, so this constructor is specifically the
    /// root case.
    pub fn direct_image() -> Self {
        RewriteTag {
            via: Pass::Lower,
            nature: Nature::Source,
            label: "lower.image",
        }
    }
}

/// Per-pane node → attribution. The lowering-projection instance (folded from
/// the `LoweringLog` at the lowering boundary) is always-on; a downstream
/// pane's instance is materialized by [`collapse`] at snapshot-serve time.
pub type SourceProjection = HashMap<NodeId, SourceAttribution>;

/// A history-integrity violation surfaced by [`collapse`]. The fold's error
/// channel.
///
/// `Leak::Duplicate` (one id at two tree positions) is deliberately *not* here:
/// it is a tree invariant, checked pipeline-wide by `assert_unique_node_ids`,
/// not a collapse concern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Leak {
    /// An output id with no lineage — a `fresh()` where a preserve was intended
    /// (nothing produced or preserved this id).
    Unexplained { output: NodeId },
    /// An input id that was neither consumed nor carried into the output — its
    /// history vanished silently.
    Dropped { input: NodeId },
    /// A [`Op::Transform`] consumed an id that was not live (an ordering or
    /// attribution bug).
    ConsumedUnknown { consumed: NodeId },
    /// A [`Op::Copy`] named an origin that was not live.
    CopyOfUnknown { origin: NodeId },
    /// A [`Op::Transform`] produced an already-live id it did not also consume
    /// (a lying step: it claims to mint what already exists).
    ProducedLive { produced: NodeId },
    /// A [`Op::Transform`] with **both** empty `consumed` and empty `blame`
    /// (index into the concatenated log) — a truly unanchored mint. Every step
    /// must anchor its outputs through *some* channel: consumption or blame. A
    /// consume-nothing transform that still names `blame` is the legal
    /// *pure-insertion* shape (a node inserted over surviving material,
    /// attributed via blame, with genuinely no lineage ancestor); only the
    /// both-empty case cannot explain where its outputs came from.
    EmptyConsumed { step: usize },
}

/// Resolve a `blame` set to a [`SourceAttribution`] through the `attr`
/// projection: the order-preserving, deduplicated union of each blamed id's
/// spans, tagged with `{via, nature, label}`.
///
/// Blame resolves through `attr` (the span channel), never through the lineage
/// `roots`. A blamed id absent from `attr` contributes no spans (it has no
/// known source), which is legal — empty blame or all-unknown blame yields
/// `spans: []`, the "known node, no source anchor" case.
///
/// A private helper of [`collapse`], so it is dead exactly while `collapse` is.
#[allow(dead_code)]
fn attribute(
    blame: &[NodeId],
    nature: Nature,
    via: Pass,
    label: RewriteLabel,
    attr: &SourceProjection,
) -> SourceAttribution {
    // No *pass* step may carry `Nature::Source`: `Source` means "this node is a
    // source construct's direct one-to-one translation", which only lowering can
    // produce — a later pass rewriting a node changes what it is. The guard sits
    // on the attributing ARM, not on projection entries: an *inherited* Source
    // tag on a preserved id in a later pane is legal and reaches the projection
    // by clone, never through this fn. See `design/provenance.md`, "The lineage
    // model (`src/ccl/lineage.rs`)".
    debug_assert!(
        !nature.is_source(),
        "a pass step carries Nature::Source (label {label:?}, via {via:?}) — \
         Source is emitted only by lowering"
    );
    let mut spans: Vec<Span> = Vec::new();
    for b in blame {
        if let Some(a) = attr.get(b) {
            for s in &a.spans {
                if !spans.contains(s) {
                    spans.push(*s);
                }
            }
        }
    }
    SourceAttribution {
        spans,
        rewritten: RewriteTag { via, nature, label },
    }
}

/// Fold the concatenated per-pass logs between two pane snapshots into the
/// pane-pair [`LineageMap`], the output pane's [`SourceProjection`], and any
/// integrity [`Leak`]s.
///
/// `logs` is the intervening passes' logs in pass order; each step's `via` comes
/// from its owning log's [`Pass`] (passes live in the data, not the types).
/// `input_ids` / `output_ids` are the two pane snapshots; `upstream_attr` is the
/// input pane's already-resolved projection, which untouched ids inherit
/// unchanged.
///
/// # The fold
///
/// State is `roots: id → {input ids it descends from}`, seeded to the identity
/// (`roots[u] = {u}`) for every input id, and `attr`, seeded from
/// `upstream_attr`. Per step, in log order:
///
/// * **[`Op::Transform`]**: every consumed id must be live; their root sets
///   union into `new_roots`; the consumed ids are removed; each produced id gets
///   `new_roots` and a fresh attribution. Survivor-carry works because a carried
///   id's own roots were in the union before removal.
/// * **[`Op::Copy`]**: the origin must be live and *stays* live; each produced
///   id snapshots a clone of the origin's roots and mirrors the origin's
///   attribution (re-tagged when `blame` is empty, else freshly attributed).
///
/// At emit, each output id's roots become its `up` edges and the reverse `down`
/// edges — the bipartite product for N:M steps and self-edges for untouched ids
/// both fall out. Ids born and consumed within the phase never reach an output
/// and compose away.
///
/// Exercised only by this module's tests until a pane boundary calls it, which
/// needs the per-pass logs the passes do not yet record. `collapse_lowering` is
/// the always-on sibling and shares the [`RootTracker`] core, so the fold logic
/// here is not untested — only this entry point is uncalled.
#[allow(dead_code)]
pub(crate) fn collapse(
    logs: &[(Pass, LineageLog)],
    input_ids: &HashSet<NodeId>,
    output_ids: &HashSet<NodeId>,
    upstream_attr: &SourceProjection,
) -> (LineageMap<NodeId, NodeId>, SourceProjection, Vec<Leak>) {
    // Seeded from the input pane's identity roots; attr inherits `upstream_attr`.
    let mut tracker = RootTracker::seeded(input_ids);
    let mut attr: SourceProjection = upstream_attr.clone();

    for (pass, log) in logs {
        let via = *pass;
        for step in log {
            match &step.op {
                Op::Transform { consumed, produced } => {
                    // A step must anchor its outputs through *some* channel:
                    // consumption or blame. Empty-consumed-with-blame is
                    // the legal pure-insertion shape; only both-empty is a leak.
                    let anchored = !step.blame.is_empty();
                    tracker.transform(consumed, produced, anchored, false);
                    let out_attr = attribute(&step.blame, step.nature, via, step.label, &attr);
                    for p in produced {
                        attr.insert(*p, out_attr.clone());
                    }
                }
                Op::Copy { origin, produced } => {
                    // A copy mirrors its origin's lineage, never its fate: the
                    // origin stays live and its roots are snapshotted here, so a
                    // later consume of the origin leaves these copies correct.
                    if !tracker.copy(*origin, produced) {
                        tracker.advance();
                        continue;
                    }
                    let out_attr = if step.blame.is_empty() {
                        // Copy-mirror re-tag: as in `attribute`, no pass step may
                        // carry Source — only lowering emits it.
                        debug_assert!(
                            !step.nature.is_source(),
                            "a pass Copy step carries Nature::Source (label {:?}, via {via:?}) — \
                             Source is emitted only by lowering",
                            step.label,
                        );
                        SourceAttribution {
                            spans: attr
                                .get(origin)
                                .map(|a| a.spans.clone())
                                .unwrap_or_default(),
                            rewritten: RewriteTag {
                                via,
                                nature: step.nature,
                                label: step.label,
                            },
                        }
                    } else {
                        attribute(&step.blame, step.nature, via, step.label, &attr)
                    };
                    for p in produced {
                        attr.insert(*p, out_attr.clone());
                    }
                }
            }
            tracker.advance();
        }
    }

    // Emit. Each output id's surviving roots become its up-edges (and the
    // mirrored down-edges); sorted for determinism.
    let mut down: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    let mut up: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for o in output_ids {
        match tracker.roots_of(o) {
            Some(origins) => {
                let mut origins: Vec<NodeId> = origins.iter().copied().collect();
                origins.sort_unstable();
                for &u in &origins {
                    down.entry(u).or_default().push(*o);
                }
                up.insert(*o, origins);
            }
            None => tracker.push_leak(Leak::Unexplained { output: *o }),
        }
    }
    for ds in down.values_mut() {
        ds.sort_unstable();
    }

    // A live input id that never reached the output was dropped without
    // explanation (a consumed id was removed from `roots`; a carried id is in
    // the output as a self-edge).
    for u in input_ids {
        if tracker.is_live(u) && !output_ids.contains(u) {
            tracker.push_leak(Leak::Dropped { input: *u });
        }
    }

    // The pane projection is exactly the output nodes' attributions: transients
    // (born and consumed within the phase) drop out, untouched ids keep their
    // inherited entry, and an output id with no attribution is legitimately
    // absent (distinct from a present-but-empty `spans`).
    let projection: SourceProjection = output_ids
        .iter()
        .filter_map(|o| attr.get(o).map(|a| (*o, a.clone())))
        .collect();

    (LineageMap { down, up }, projection, tracker.into_leaks())
}

/// The shared roots/leak core of the two folds. Owns the
/// `roots` state (`id → {input ids it descends from}`) and the accumulating
/// [`Leak`]s, exposing the per-step fate operations both [`collapse`] and
/// [`collapse_lowering`] drive. The attribution (`attr`) side lives in each fold
/// — blame-resolved-through-state for a pane pair, literal-anchor for lowering —
/// so it deliberately stays out of the tracker.
struct RootTracker {
    roots: HashMap<NodeId, HashSet<NodeId>>,
    leaks: Vec<Leak>,
    step_index: usize,
}

impl RootTracker {
    /// A tracker seeded with the input pane's identity roots (`roots[u] = {u}`).
    fn seeded(input_ids: &HashSet<NodeId>) -> Self {
        RootTracker {
            roots: input_ids.iter().map(|&u| (u, HashSet::from([u]))).collect(),
            leaks: Vec::new(),
            step_index: 0,
        }
    }

    /// An empty tracker — lowering's degeneration: no input pane, so `roots`
    /// starts empty and nearly every `Transform` is a pure insertion.
    fn empty() -> Self {
        RootTracker {
            roots: HashMap::new(),
            leaks: Vec::new(),
            step_index: 0,
        }
    }

    /// The fate side of a [`Op::Transform`]: check the unanchored-mint leak
    /// (both consumed and the caller-supplied anchor empty), union-and-remove the
    /// consumed roots, then assign that union to every produced id (survivor-carry
    /// works because a carried id's own roots were in the union before removal).
    /// `anchored` is `true` when the step carries *some* attribution anchor —
    /// blame for a pass step, a literal span for a lowering leaf.
    ///
    /// `reimage_ok` suppresses the [`Leak::ProducedLive`] check: a *pass* step
    /// producing a live id it did not consume is a lying step, but a lowering
    /// leaf may legitimately **re-image** a node (last tag wins — `lower_expr`
    /// re-tags an arm's already-tagged root as the construct's direct image), so
    /// the lowering fold passes `true` here. Lowering leaves always have empty
    /// `consumed`, so the re-image just overwrites empty roots with empty roots.
    fn transform(
        &mut self,
        consumed: &[NodeId],
        produced: &[NodeId],
        anchored: bool,
        reimage_ok: bool,
    ) {
        if consumed.is_empty() && !anchored {
            self.leaks.push(Leak::EmptyConsumed {
                step: self.step_index,
            });
        }
        let mut new_roots: HashSet<NodeId> = HashSet::new();
        for c in consumed {
            match self.roots.remove(c) {
                Some(r) => new_roots.extend(r),
                None => self.leaks.push(Leak::ConsumedUnknown { consumed: *c }),
            }
        }
        for p in produced {
            // A produced id still live here was not consumed (consumed ids were
            // just removed): a pass step lies about minting it. A lowering
            // re-image (`reimage_ok`) is legitimate last-tag-wins, not a lie.
            if self.roots.contains_key(p) && !reimage_ok {
                self.leaks.push(Leak::ProducedLive { produced: *p });
            }
            self.roots.insert(*p, new_roots.clone());
        }
    }

    /// The fate side of a [`Op::Copy`]: the origin must be live and *stays* live;
    /// each produced id snapshots a clone of the origin's roots. Returns `false`
    /// (recording [`Leak::CopyOfUnknown`]) when the origin is not live, so the
    /// caller skips the attribution mirror.
    fn copy(&mut self, origin: NodeId, produced: &[NodeId]) -> bool {
        let Some(origin_roots) = self.roots.get(&origin).cloned() else {
            self.leaks.push(Leak::CopyOfUnknown { origin });
            return false;
        };
        for p in produced {
            self.roots.insert(*p, origin_roots.clone());
        }
        true
    }

    /// Advance the step counter (drives [`Leak::EmptyConsumed`]'s index).
    fn advance(&mut self) {
        self.step_index += 1;
    }

    /// The roots of an id, if live.
    fn roots_of(&self, id: &NodeId) -> Option<&HashSet<NodeId>> {
        self.roots.get(id)
    }

    /// Whether `id` is live.
    fn is_live(&self, id: &NodeId) -> bool {
        self.roots.contains_key(id)
    }

    fn push_leak(&mut self, leak: Leak) {
        self.leaks.push(leak);
    }

    fn into_leaks(self) -> Vec<Leak> {
        self.leaks
    }
}

/// Fold a [`LoweringLog`] into the always-on **lowering projection** and any
/// integrity [`Leak`]s. The lowering degeneration of
/// [`collapse`], sharing its [`RootTracker`] core with three simplifications:
///
/// * **no input pane** — lowering mints from scratch, so `roots` starts empty
///   and a leaf `Transform { consumed: [], produced: [id] }` is a pure insertion
///   with empty roots (its attribution comes from the literal `anchor`, not from
///   blame resolved through state);
/// * **no [`LineageMap`] output** — the lowering projection ships as pane-0
///   spans, not edges, so there is no `up`/`down` to build and no `Dropped` class
///   (there are no input ids to drop);
/// * **no upstream attr** — a leaf's attribution is `{spans: anchor, RewriteTag}`
///   built directly here; a `Copy` mirrors its origin's already-folded entry.
///
/// Runs always-on at the lowering→pipeline handoff (the leak *checks* stay
/// debug/test-gated at the boundary). `Leak::Unexplained` is an unrecorded mint
/// (an output-tree node that no leaf produced and no copy placed); a template
/// id born, copied, and never placed composes away (born-copied-discarded — live
/// but neither input nor output, so no leak); orphaned keys are structurally
/// impossible (the projection is produced by the fold, never mutated).
pub(crate) fn collapse_lowering(
    log: &LoweringLog,
    output_ids: &HashSet<NodeId>,
) -> (SourceProjection, Vec<Leak>) {
    let mut tracker = RootTracker::empty();
    let mut attr: SourceProjection = SourceProjection::new();

    for step in log {
        match &step.op {
            Op::Transform { consumed, produced } => {
                // The anchor is the literal attribution channel: a leaf with a
                // non-empty anchor is a legal pure insertion even with empty
                // `consumed`. Both-empty is the unanchored-mint leak.
                let anchored = !step.anchor.is_empty();
                tracker.transform(consumed, produced, anchored, true);
                // Attribution comes straight from the literal anchor spans — no
                // blame resolution (lowering knows the source token here).
                let out_attr = SourceAttribution {
                    spans: dedup_spans(&step.anchor),
                    rewritten: RewriteTag {
                        via: Pass::Lower,
                        nature: step.nature,
                        label: step.label,
                    },
                };
                for p in produced {
                    attr.insert(*p, out_attr.clone());
                }
            }
            Op::Copy { origin, produced } => {
                // A copy mirrors its origin's already-folded entry verbatim (the
                // compare-chain second-use operand and the uncurry template
                // interiors are exactly their origins' images/plumbing).
                if !tracker.copy(*origin, produced) {
                    tracker.advance();
                    continue;
                }
                if let Some(origin_attr) = attr.get(origin).cloned() {
                    for p in produced {
                        attr.insert(*p, origin_attr.clone());
                    }
                }
            }
        }
        tracker.advance();
    }

    // Every output-tree node must be explained (produced by a leaf or a copy).
    // An unexplained output is an unrecorded lowering mint; this leak IS the
    // coverage check (there is no separate gate). There is no `Dropped` class
    // (no input pane).
    for o in output_ids {
        if !tracker.is_live(o) {
            tracker.push_leak(Leak::Unexplained { output: *o });
        }
    }

    let projection: SourceProjection = output_ids
        .iter()
        .filter_map(|o| attr.get(o).map(|a| (*o, a.clone())))
        .collect();

    (projection, tracker.into_leaks())
}

/// Order-preserving deduplicated span union (a leaf anchor is normally one span,
/// but the sink-record's whole-program anchor and future multi-span leaves stay
/// well-behaved).
fn dedup_spans(spans: &[Span]) -> Vec<Span> {
    let mut out: Vec<Span> = Vec::with_capacity(spans.len());
    for s in spans {
        if !out.contains(s) {
            out.push(*s);
        }
    }
    out
}

// ===========================================================================
// The recorder: an ambient thread-local step stack that turns node construction
// into RewriteSteps as a byproduct of the rewrite (never a post-pass diff).
//
// Discipline mirrors `infer_var::ACTIVE_ARENA`: install a capture buffer at a
// pass boundary, let construction hooks feed it, drain at the boundary. The
// compile path is single-threaded (the only `thread::spawn`s are runtime I/O),
// so a per-thread stack is safe. An empty stack means recording is off — the
// overwhelmingly common case (tests, non-recorded compiles), reduced to a cheap
// emptiness check on the construction hot path.
// ===========================================================================

thread_local! {
    /// The open steps, innermost last. Empty ⇒ recording off. A construction
    /// hook ([`on_mint`]/[`on_copy`]) pushes into the innermost frame only;
    /// nesting is by frame depth.
    static STEP_STACK: RefCell<Vec<OpenStep>> = const { RefCell::new(Vec::new()) };

    /// The log the finalized steps flush into, installed per boundary by a
    /// [`RecorderSession`]. `None` ⇒ no session: a step still captures into its
    /// frame, but its flush is a silent no-op (uniform single code path). The
    /// [`ActiveLog`] kind routes each flush to a [`RewriteStep`] (pass) or a
    /// [`LoweringStep`] (lowering).
    static ACTIVE_LOG: RefCell<Option<ActiveLog>> = const { RefCell::new(None) };
}

/// The kind of log a [`RecorderSession`] installs — the session-kind routing.
/// `on_mint`/`on_copy` push NodeIds regardless (they are
/// blame-domain-agnostic); a frame's flush matches this to emit the right step
/// type, and the always-on lowering leaves ([`lowering_leaf`]) append here too.
/// The lowering log, plus the set of [`NodeId`]s it has already explained.
///
/// The set exists for one caller: [`lowering_predicate_leaf`], which sweeps a
/// finished refinement predicate and must **not** re-record a node that already
/// carries precise attribution from its own lowering. The fold is
/// last-write-wins (`attr.insert(p, out_attr)`), so a blanket sweep would
/// silently replace a node's real span and label with the coarse predicate one —
/// a loss no leak class can see, because the node stays explained either way.
#[derive(Default)]
struct LoweringRecord {
    log: LoweringLog,
    recorded: HashSet<NodeId>,
}

enum ActiveLog {
    /// A pass boundary's log (inspector-only sessions).
    Pass(LineageLog),
    /// Lowering's log (the always-on session, all builds).
    Lowering(LoweringRecord),
}

/// An in-flight step accumulating the ids born and copied within its dynamic
/// extent. Finalized (flushed to a [`RewriteStep`]) by its [`StepGuard`]'s
/// `Drop`. The `produced`/copy sides are *captured*, not declared: this is what
/// makes recording a byproduct of construction rather than a parallel
/// annotation.
struct OpenStep {
    label: RewriteLabel,
    /// The ids this step declared it would consume. The `produced` side is
    /// discovered from the construction hooks, never declared.
    consumed: Vec<NodeId>,
    blame: Vec<NodeId>,
    nature: Nature,
    /// Ids minted via `Expr::new` while this was the innermost open frame.
    births: Vec<NodeId>,
    /// `(origin, fresh)` pairs reported by the freshen hooks while this was the
    /// innermost open frame.
    copies: Vec<(NodeId, NodeId)>,
}

impl OpenStep {
    /// Finalize this frame into the active log's [`RewriteStep`]s.
    ///
    /// The frame emits one `Transform { consumed, produced: births }`, and its
    /// captured freshen pairs flush as per-origin `Copy` steps (empty blame — a
    /// copy mirrors its origin, it does not re-attribute), so a deep freshen's
    /// one-pair-per-node duplication lands as one `Copy` step per freshened
    /// origin. A copy's origin is always *discovered* through the `on_copy` hook,
    /// never declared up front: every duplication path funnels through
    /// [`TypedExpr::freshen_node_id`](crate::ccl::expr::TypedExpr::freshen_node_id),
    /// so capture is total and a declared-origin frame kind would be redundant.
    ///
    /// A `Transform` frame whose `consumed` *and* captured `births` are both
    /// empty emits no `Transform` record: it was opened purely to capture the
    /// freshen pairs of a deep clone (its only output is those per-origin `Copy`
    /// steps), and a `Transform { consumed: [], produced: [] }` would be an
    /// unanchored no-op ([`Leak::EmptyConsumed`] were blame also empty).
    fn flush_into(self, log: &mut LineageLog) {
        let OpenStep {
            label,
            consumed,
            blame,
            nature,
            births,
            copies,
        } = self;
        if !(consumed.is_empty() && births.is_empty()) {
            log.push(RewriteStep {
                op: Op::Transform {
                    consumed,
                    produced: births,
                },
                blame,
                nature,
                label,
            });
        }
        for (origin, produced) in group_copies(&copies) {
            log.push(RewriteStep {
                op: Op::Copy { origin, produced },
                blame: Vec::new(),
                nature,
                label,
            });
        }
    }

    /// Finalize this frame into a [`LoweringLog`]. Lowering frames are opened
    /// **only** to capture ambient `Copy`s (uncurry's template-interior freshens,
    /// the compare-chain operand freshens); the leaf mints append directly via
    /// [`lowering_leaf`], so a lowering frame carries no consumed ids and no
    /// births — only the captured per-origin copies flush here, as `Copy`
    /// [`LoweringStep`]s mirroring their origins' folded entries (empty anchor).
    fn flush_into_lowering(self, rec: &mut LoweringRecord) {
        let OpenStep {
            label,
            nature,
            births,
            copies,
            ..
        } = self;
        debug_assert!(
            births.is_empty(),
            "a lowering copy-frame captured a mint ({births:?}) — leaf mints must \
             append via lowering_leaf, frames capture only copies",
        );
        for (origin, produced) in group_copies(&copies) {
            rec.recorded.extend(produced.iter().copied());
            rec.log.push(LoweringStep {
                op: Op::Copy { origin, produced },
                anchor: Vec::new(),
                nature,
                label,
            });
        }
    }
}

/// Append a single-node leaf [`LoweringStep`] (`Transform { consumed: [],
/// produced: [id] }`, `anchor: [span]`) to the active lowering log — the
/// leaf-grain recording that `tag_source`/`tag_machinery`
/// route through. A no-op when no lowering session is installed (the lower
/// submodules' unit tests, which only inspect the tree shape) or when a pass
/// session is active (defensive: lowering leaves belong only to a lowering log).
/// Record one node of a **refinement predicate**, unless it is already
/// explained.
///
/// Lowering builds a predicate out of ordinary sub-expressions that were lowered
/// — and therefore recorded — in the main tree, then mints and copies extra
/// nodes to assemble them (`ccl_utils::refined_data_fun` is where the result is
/// sealed into a `Refinement`). Those assembly nodes live only in a type slot,
/// outside the `walk_children` domain, so nothing recorded them.
///
/// The skip is the whole point. A node the main-tree walk already explained has
/// a precise span and label; re-recording it here would replace both with this
/// sweep's coarse ones, because the fold is last-write-wins. Measured on the
/// pipeline corpus: 318 nodes would be clobbered without it, and no leak class
/// would report anything, since a clobbered node is still explained.
pub(crate) fn lowering_predicate_leaf(id: NodeId, span: Span, nature: Nature, label: RewriteLabel) {
    if id == NodeId::PLACEHOLDER {
        return;
    }
    ACTIVE_LOG.with(|slot| {
        if let Some(ActiveLog::Lowering(rec)) = slot.borrow_mut().as_mut() {
            if !rec.recorded.insert(id) {
                return;
            }
            rec.log.push(LoweringStep {
                op: Op::Transform {
                    consumed: Vec::new(),
                    produced: vec![id],
                },
                anchor: vec![span],
                nature,
                label,
            });
        }
    });
}

pub(crate) fn lowering_leaf(id: NodeId, span: Span, nature: Nature, label: RewriteLabel) {
    ACTIVE_LOG.with(|slot| {
        if let Some(ActiveLog::Lowering(rec)) = slot.borrow_mut().as_mut() {
            rec.recorded.insert(id);
            rec.log.push(LoweringStep {
                op: Op::Transform {
                    consumed: Vec::new(),
                    produced: vec![id],
                },
                anchor: vec![span],
                nature,
                label,
            });
        }
    });
}

/// Group captured `(origin, fresh)` pairs into per-origin produced-lists,
/// preserving first-seen origin order for a deterministic log.
fn group_copies(copies: &[(NodeId, NodeId)]) -> Vec<(NodeId, Vec<NodeId>)> {
    let mut out: Vec<(NodeId, Vec<NodeId>)> = Vec::new();
    for &(origin, fresh) in copies {
        match out.iter_mut().find(|(o, _)| *o == origin) {
            Some((_, freshs)) => freshs.push(fresh),
            None => out.push((origin, vec![fresh])),
        }
    }
    out
}

/// Open a lineage step, returning an RAII guard that finalizes it on drop.
///
/// While the guard is alive the step is the innermost open frame: every id
/// minted (via `Expr::new`) or freshened (via the freshen helpers) on this
/// thread is captured into it. `blame` is the separate attribution channel
/// (blame ⊥ consumption) — the upstream ids the outputs trace to, which may
/// differ from what the step consumes.
///
/// `consumed` is the only thing a frame declares up front; the produced side is
/// discovered from the construction hooks. A frame that consumes nothing and
/// mints nothing — opened purely to capture a clone's freshen pairs — is a
/// [`copy_frame`], which spells that out and has no inert arguments.
pub(crate) fn step(
    label: RewriteLabel,
    consumed: Vec<NodeId>,
    blame: Vec<NodeId>,
    nature: Nature,
) -> StepGuard {
    STEP_STACK.with(|s| {
        let mut stack = s.borrow_mut();
        let depth = stack.len();
        stack.push(OpenStep {
            label,
            consumed,
            blame,
            nature,
            births: Vec::new(),
            copies: Vec::new(),
        });
        StepGuard { depth }
    })
}

/// Open a **lowering** copy-only frame: it consumes nothing, mints nothing, and
/// exists solely to capture the `(origin, fresh)` pairs a clone's freshen reports,
/// which flush as per-origin [`Op::Copy`] steps.
///
/// The distinct constructor is what keeps the frame honest, and the reason it is
/// lowering-specific is the two folds' `Op::Copy` arms:
/// [`collapse_lowering`] mirrors the origin's already-folded attribution
/// *verbatim*, so a lowering copy's `nature` and `blame` are genuinely never read
/// — passing them would be passing unobservable values, and a wrong one (a
/// `Nature::Source` on a copy frame) would look meaningful while being inert.
/// [`collapse`] does **not** mirror: a pass `Op::Copy` with empty blame builds
/// `RewriteTag { nature: step.nature, .. }`, so a pass copy-frame's nature reaches
/// the attribution and must be chosen deliberately. Such a frame opens with
/// [`step`] and names its nature.
pub(crate) fn copy_frame(label: RewriteLabel) -> StepGuard {
    step(label, Vec::new(), Vec::new(), Nature::Machinery)
}

/// RAII finalizer for an open [`step`]. Popping and flushing on `Drop` is
/// panic-safe: an unwind through an open step still pops its frame (so the stack
/// is never left corrupt) and flushes what was captured before the panic.
pub(crate) struct StepGuard {
    /// The stack index this frame occupied when opened, for the LIFO tripwire.
    depth: usize,
}

impl Drop for StepGuard {
    fn drop(&mut self) {
        // Pop our frame. Guards drop in LIFO order in normal control flow and on
        // unwind alike; the tripwire catches a manually-mis-ordered drop.
        let frame = STEP_STACK.with(|s| {
            let mut stack = s.borrow_mut();
            debug_assert_eq!(
                stack.len(),
                self.depth + 1,
                "StepGuard dropped out of LIFO order (expected depth {}, stack has {})",
                self.depth,
                stack.len(),
            );
            stack.pop()
        });
        let Some(frame) = frame else { return };
        // Flush to the active log if a session is installed; a no-op otherwise.
        // The log kind routes the flush to the matching step type.
        ACTIVE_LOG.with(|slot| match slot.borrow_mut().as_mut() {
            Some(ActiveLog::Pass(log)) => frame.flush_into(log),
            Some(ActiveLog::Lowering(rec)) => frame.flush_into_lowering(rec),
            None => {}
        });
    }
}

/// A hook called from `Expr::new` for every minted [`NodeId`]. Pushes the id
/// into the innermost open step's births, or does nothing when no step is open
/// (the common case — a borrow and an emptiness check). The [`PLACEHOLDER`]
/// sentinel is ignored so `Default`/`mem::take` throwaways never pollute a step.
///
/// [`PLACEHOLDER`]: NodeId::PLACEHOLDER
pub(crate) fn on_mint(id: NodeId) {
    if id == NodeId::PLACEHOLDER {
        return;
    }
    STEP_STACK.with(|s| {
        if let Some(top) = s.borrow_mut().last_mut() {
            top.births.push(id);
        }
    });
}

thread_local! {
    /// Depth counter for [`preserve_ids`]: non-zero means a clone in progress is
    /// a **re-allocation of the same node**, not a duplication, so it must carry
    /// the origin's id rather than mint one.
    ///
    /// A counter rather than a flag because the scopes nest — a preserving copy
    /// of a tree recurses through `Clone` for every child.
    static PRESERVING_IDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Guard returned by [`preserve_ids`]. Dropping it re-enables freshening.
pub(crate) struct PreservingIds;

impl Drop for PreservingIds {
    fn drop(&mut self) {
        PRESERVING_IDS.with(|c| c.set(c.get() - 1));
    }
}

/// Open a scope in which [`TypedExpr`](crate::ccl::expr::TypedExpr)'s `Clone`
/// **preserves** ids instead of freshening them.
///
/// Reach for this through
/// [`TypedExpr::clone_preserving_ids`](crate::ccl::expr::TypedExpr::clone_preserving_ids),
/// never directly: the scope must cover the clone and nothing else, and a
/// genuine duplication performed inside one would silently produce a
/// duplicate id.
#[must_use]
pub(crate) fn preserve_ids() -> PreservingIds {
    PRESERVING_IDS.with(|c| c.set(c.get() + 1));
    PreservingIds
}

/// Run `f` with id-preserving clones — a scope over a whole *rewrite region*,
/// not over a copy.
///
/// # TODO(predicate-domain): this is slated for removal. Do not add callers.
///
/// **There is exactly one legitimate user: [`PredMemo`]'s predicate rebuild**
/// (two call sites). Everything else that needs a preserving copy has one —
/// [`TypedExpr::clone_preserving_ids`] — and should use it. A new caller here is
/// almost certainly reaching for the wrong tool: this scope silences the
/// freshening for *every* clone on the thread until `f` returns, including
/// genuine duplications a callee performs, so it can manufacture duplicate ids
/// in a way the per-copy method cannot.
///
/// It exists because what must not mint inside a predicate rebuild is not a copy
/// but an arbitrary caller-supplied rewrite: `f` does not clone the predicate, it
/// mints *into* it (a substitution materializing a template, a rule building a
/// conjunction). Nothing records a predicate rewrite, so a node minted there is
/// one no record explains, and a `Copy` rowed against it folds as
/// [`Leak::CopyOfUnknown`]. `clone_preserving_ids` covers one copy;
/// only a scope covers a region.
///
/// Preserving is honest here because the rebuilt term *replaces* the original
/// everywhere the walk reaches — which holds only because `uniquify` walks the
/// whole tree. It is a **scope cut**, not a design: the predicate domain needs
/// recording, and this function should go when that lands. See the vault's
/// `predicate-lineage-report` and `design/provenance.md`, "Walking the ids".
///
/// [`PredMemo`]: crate::ccl::ccl_utils::PredMemo
/// [`TypedExpr::clone_preserving_ids`]: crate::ccl::expr::TypedExpr::clone_preserving_ids
pub(crate) fn preserving_ids<R>(f: impl FnOnce() -> R) -> R {
    let _guard = preserve_ids();
    f()
}

/// The id a clone of `origin` should carry, and the one place that decides.
///
/// Freshens by default — a clone is a sibling — reporting the pair through
/// [`on_copy`]. Inside a [`preserve_ids`] scope it returns `origin` unchanged
/// and records nothing, because no new node came into being.
pub(crate) fn copy_id(origin: NodeId) -> NodeId {
    if PRESERVING_IDS.with(std::cell::Cell::get) > 0 {
        return origin;
    }
    let fresh = NodeId::fresh();
    on_copy(origin, fresh);
    fresh
}

/// A hook called from the freshen helpers for every `(origin, fresh)`
/// duplication. Pushes the pair into the innermost open step's copies, or does
/// nothing when no step is open. Guards the [`PLACEHOLDER`] sentinel on both
/// sides, as [`on_mint`] does: a placeholder origin would fold as
/// [`Leak::CopyOfUnknown`] against an id that is never live by construction.
///
/// [`PLACEHOLDER`]: NodeId::PLACEHOLDER
pub(crate) fn on_copy(origin: NodeId, fresh: NodeId) {
    if origin == NodeId::PLACEHOLDER || fresh == NodeId::PLACEHOLDER {
        return;
    }
    STEP_STACK.with(|s| {
        if let Some(top) = s.borrow_mut().last_mut() {
            top.copies.push((origin, fresh));
        }
    });
}

/// RAII installer for the active recording log. [`new`](Self::new) installs a
/// **pass** log ([`ActiveLog::Pass`]); [`lowering`](Self::lowering) installs a
/// **lowering** log ([`ActiveLog::Lowering`]). The matching drain
/// ([`into_log`](Self::into_log) / [`into_lowering_log`](Self::into_lowering_log))
/// ends the session; `Drop` clears the slot so a panic never leaves a stale log
/// installed for the next boundary. At most one session per thread, and — since
/// the lowering session installs unconditionally in every build — it must fully
/// drain before the first pass session opens.
pub(crate) struct RecorderSession {
    // Not `Copy`/`Clone`; holds the installed-log invariant for its lifetime.
    _private: (),
}

impl RecorderSession {
    /// Install a fresh, empty **pass** log as the active recording target for
    /// this thread. Non-reentrant: at most one session per thread
    /// (debug-asserted).
    ///
    /// The pass-log counterpart to [`lowering`](Self::lowering), which is
    /// always-on. Uncalled outside this module's tests until a pass boundary
    /// installs a session of its own.
    #[allow(dead_code)]
    pub(crate) fn new() -> Self {
        Self::install(ActiveLog::Pass(Vec::new()))
    }

    /// Install a fresh, empty **lowering** log. The always-on session:
    /// installed for the whole of lowering in every build. Its leaf entries
    /// ([`lowering_leaf`]) and copy-frame flushes route to a [`LoweringLog`].
    pub(crate) fn lowering() -> Self {
        Self::install(ActiveLog::Lowering(LoweringRecord::default()))
    }

    fn install(log: ActiveLog) -> Self {
        ACTIVE_LOG.with(|slot| {
            let mut slot = slot.borrow_mut();
            debug_assert!(
                slot.is_none(),
                "a RecorderSession is already installed on this thread",
            );
            *slot = Some(log);
        });
        RecorderSession { _private: () }
    }

    /// Drain and return the recorded **pass** log, ending the session. The
    /// subsequent `Drop` is then a no-op (the slot is already empty).
    ///
    /// Paired with [`new`](Self::new), so it is dead exactly while that is.
    #[allow(dead_code)]
    pub(crate) fn into_log(self) -> LineageLog {
        ACTIVE_LOG.with(|slot| match slot.borrow_mut().take() {
            Some(ActiveLog::Pass(log)) => log,
            other => {
                debug_assert!(other.is_none(), "into_log on a non-pass session");
                Vec::new()
            }
        })
    }

    /// Drain and return the recorded **lowering** log, ending the session.
    pub(crate) fn into_lowering_log(self) -> LoweringLog {
        ACTIVE_LOG.with(|slot| match slot.borrow_mut().take() {
            Some(ActiveLog::Lowering(rec)) => rec.log,
            other => {
                debug_assert!(
                    other.is_none(),
                    "into_lowering_log on a non-lowering session"
                );
                Vec::new()
            }
        })
    }
}

impl Drop for RecorderSession {
    fn drop(&mut self) {
        // Clear on unwind (and after a plain `into_log`, harmlessly): the next
        // pass must never see a stale log.
        ACTIVE_LOG.with(|slot| *slot.borrow_mut() = None);
    }
}

/// The current open-step depth on this thread — a probe for the panic-safety
/// and no-op tests, which assert the stack is left clean.
#[cfg(test)]
fn step_stack_depth() -> usize {
    STEP_STACK.with(|s| s.borrow().len())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span(start: usize, end: usize) -> Span {
        Span::new(start, end)
    }

    fn ids<const N: usize>() -> [NodeId; N] {
        std::array::from_fn(|_| NodeId::fresh())
    }

    fn set(items: impl IntoIterator<Item = NodeId>) -> HashSet<NodeId> {
        items.into_iter().collect()
    }

    /// The predicate sweep must not overwrite attribution a node already has.
    ///
    /// This is the one property of `lowering_predicate_leaf` that **no leak class
    /// can see**: the fold is last-write-wins, so a node re-recorded by the sweep
    /// is still perfectly *explained* — it has just silently swapped its real
    /// span and label for the sweep's coarse ones. Measured on the pipeline
    /// corpus, a blanket sweep clobbers 318 nodes and every gate stays green.
    #[test]
    fn the_predicate_sweep_skips_already_recorded_nodes() {
        let [recorded, fresh] = ids::<2>();
        let session = RecorderSession::lowering();
        // A node lowered in the main tree: precise span, precise label.
        lowering_leaf(recorded, span(10, 20), Nature::Source, "lower.precise");
        // The sweep runs over a predicate containing both that node and one
        // minted while assembling the predicate.
        lowering_predicate_leaf(recorded, span(0, 99), Nature::Machinery, "lower.sweep");
        lowering_predicate_leaf(fresh, span(0, 99), Nature::Machinery, "lower.sweep");
        let log = session.into_lowering_log();

        assert_eq!(log.len(), 2, "the already-recorded node is not re-recorded");
        let for_recorded: Vec<_> = log
            .iter()
            .filter(
                |s| matches!(&s.op, Op::Transform { produced, .. } if produced == &vec![recorded]),
            )
            .collect();
        assert_eq!(
            for_recorded.len(),
            1,
            "exactly one entry for the lowered node"
        );
        assert_eq!(
            for_recorded[0].label, "lower.precise",
            "its own label survives"
        );
        assert_eq!(
            for_recorded[0].anchor,
            vec![span(10, 20)],
            "its own span survives"
        );

        let for_fresh: Vec<_> = log
            .iter()
            .filter(|s| matches!(&s.op, Op::Transform { produced, .. } if produced == &vec![fresh]))
            .collect();
        assert_eq!(
            for_fresh.len(),
            1,
            "the assembly node is explained by the sweep"
        );
        assert_eq!(for_fresh[0].label, "lower.sweep");
    }

    /// A second sweep over the same predicate adds nothing — the skip is keyed on
    /// the id, not on which sweep recorded it, so overlapping predicates (one
    /// term riding several type slots) cannot double-record.
    #[test]
    fn the_predicate_sweep_is_idempotent() {
        let [n] = ids::<1>();
        let session = RecorderSession::lowering();
        lowering_predicate_leaf(n, span(1, 2), Nature::Machinery, "lower.sweep");
        lowering_predicate_leaf(n, span(3, 4), Nature::Machinery, "lower.sweep");
        let log = session.into_lowering_log();
        assert_eq!(
            log.len(),
            1,
            "one entry per node however many sweeps reach it"
        );
        assert_eq!(log[0].anchor, vec![span(1, 2)], "the first sweep wins");
    }

    fn transform(consumed: Vec<NodeId>, produced: Vec<NodeId>, blame: Vec<NodeId>) -> RewriteStep {
        RewriteStep {
            op: Op::Transform { consumed, produced },
            blame,
            nature: Nature::Expansion,
            label: "test.transform",
        }
    }

    fn copy(origin: NodeId, produced: Vec<NodeId>, blame: Vec<NodeId>) -> RewriteStep {
        RewriteStep {
            op: Op::Copy { origin, produced },
            blame,
            nature: Nature::Expansion,
            label: "test.copy",
        }
    }

    /// One pass' worth of log at `Pass::Inline` (an arbitrary non-lowering pass).
    fn phase(steps: Vec<RewriteStep>) -> Vec<(Pass, LineageLog)> {
        vec![(Pass::Inline, steps)]
    }

    fn sorted(mut v: Vec<NodeId>) -> Vec<NodeId> {
        v.sort_unstable();
        v
    }

    // ---- lineage composition ----------------------------------------------

    #[test]
    fn transient_born_and_consumed_composes_away() {
        // A → B (born) → C. B exists in neither snapshot; lineage flows A → C.
        let [a, b, c] = ids();
        let logs = phase(vec![
            transform(vec![a], vec![b], vec![]),
            transform(vec![b], vec![c], vec![]),
        ]);
        let (map, _proj, leaks) = collapse(&logs, &set([a]), &set([c]), &SourceProjection::new());
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(map.upstream(&c), &[a]);
        assert_eq!(map.downstream(&a), &[c]);
        // B is a transient: unknown to the map in both directions.
        assert!(map.upstream(&b).is_empty());
        assert!(map.downstream(&b).is_empty());
    }

    #[test]
    fn copy_of_copy_chain_composes() {
        // A copied to B, B copied to C; C's roots compose back to A.
        let [a, b, c] = ids();
        let logs = phase(vec![copy(a, vec![b], vec![]), copy(b, vec![c], vec![])]);
        let (map, _proj, leaks) =
            collapse(&logs, &set([a]), &set([a, c]), &SourceProjection::new());
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(map.upstream(&c), &[a]);
        assert_eq!(map.upstream(&a), &[a], "origin keeps its self-edge");
    }

    #[test]
    fn copy_whose_origin_is_consumed_later_keeps_edges() {
        // Copy A→B, then a Transform consumes A→C. B snapshotted A's lineage
        // before A was consumed, so both B and C trace to A.
        let [a, b, c] = ids();
        let logs = phase(vec![
            copy(a, vec![b], vec![]),
            transform(vec![a], vec![c], vec![]),
        ]);
        let (map, _proj, leaks) =
            collapse(&logs, &set([a]), &set([b, c]), &SourceProjection::new());
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(map.upstream(&b), &[a]);
        assert_eq!(map.upstream(&c), &[a]);
        assert_eq!(sorted(map.downstream(&a).to_vec()), sorted(vec![b, c]));
    }

    #[test]
    fn n_to_m_transform_is_the_bipartite_product() {
        // {A,B} → {C,D}: every input reaches every output (2×2 = 4 edges).
        let [a, b, c, d] = ids();
        let logs = phase(vec![transform(vec![a, b], vec![c, d], vec![])]);
        let (map, _proj, leaks) =
            collapse(&logs, &set([a, b]), &set([c, d]), &SourceProjection::new());
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(map.upstream(&c), sorted(vec![a, b]).as_slice());
        assert_eq!(map.upstream(&d), sorted(vec![a, b]).as_slice());
        assert_eq!(map.downstream(&a), sorted(vec![c, d]).as_slice());
        assert_eq!(map.downstream(&b), sorted(vec![c, d]).as_slice());
        assert_eq!(map.edges().len(), 4);
    }

    #[test]
    fn untouched_id_gets_self_edge_and_inherits_attribution() {
        // No steps mention A: it survives with a self-edge and its upstream
        // attribution passes through unchanged.
        let [a] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(
            a,
            SourceAttribution {
                spans: vec![span(3, 9)],
                rewritten: RewriteTag::direct_image(),
            },
        );
        let (map, proj, leaks) = collapse(&phase(vec![]), &set([a]), &set([a]), &upstream);
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(map.upstream(&a), &[a]);
        assert_eq!(map.downstream(&a), &[a]);
        assert_eq!(proj.get(&a), upstream.get(&a), "attribution unchanged");
    }

    #[test]
    fn survivor_carry_keeps_own_root_and_absorbs_others() {
        // consumed = {A, B}, produced = {A}: A survives while absorbing B.
        let [a, b] = ids();
        let logs = phase(vec![transform(vec![a, b], vec![a], vec![])]);
        let (map, _proj, leaks) =
            collapse(&logs, &set([a, b]), &set([a]), &SourceProjection::new());
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(map.upstream(&a), sorted(vec![a, b]).as_slice());
    }

    // ---- leak taxonomy -----------------------------------------------------

    #[test]
    fn clean_log_produces_no_leaks() {
        let [a, b] = ids();
        let logs = phase(vec![transform(vec![a], vec![b], vec![a])]);
        let (_map, _proj, leaks) = collapse(&logs, &set([a]), &set([b]), &SourceProjection::new());
        assert!(leaks.is_empty(), "{leaks:?}");
    }

    #[test]
    fn leak_unexplained_fires_on_output_with_no_lineage() {
        // Z appears in the output snapshot but nothing produced or preserved it.
        let [a, z] = ids();
        let (_map, _proj, leaks) = collapse(
            &phase(vec![]),
            &set([a]),
            &set([a, z]),
            &SourceProjection::new(),
        );
        assert!(
            leaks.contains(&Leak::Unexplained { output: z }),
            "{leaks:?}"
        );
    }

    #[test]
    fn leak_dropped_fires_on_live_input_missing_from_output() {
        // B is live at the end (never consumed) but absent from the output.
        let [a, b] = ids();
        let (_map, _proj, leaks) = collapse(
            &phase(vec![]),
            &set([a, b]),
            &set([a]),
            &SourceProjection::new(),
        );
        assert!(leaks.contains(&Leak::Dropped { input: b }), "{leaks:?}");
    }

    #[test]
    fn leak_consumed_unknown_fires_on_non_live_consume() {
        let [a, x, b] = ids();
        let logs = phase(vec![transform(vec![x], vec![b], vec![])]);
        let (_map, _proj, leaks) =
            collapse(&logs, &set([a]), &set([a, b]), &SourceProjection::new());
        assert!(
            leaks.contains(&Leak::ConsumedUnknown { consumed: x }),
            "{leaks:?}"
        );
    }

    #[test]
    fn leak_copy_of_unknown_fires_on_non_live_origin() {
        let [a, x, b] = ids();
        let logs = phase(vec![copy(x, vec![b], vec![])]);
        let (_map, _proj, leaks) = collapse(&logs, &set([a]), &set([a]), &SourceProjection::new());
        assert!(
            leaks.contains(&Leak::CopyOfUnknown { origin: x }),
            "{leaks:?}"
        );
    }

    #[test]
    fn leak_produced_live_fires_when_producing_an_unconsumed_live_id() {
        // Transform consumes A but produces B, which was already live.
        let [a, b] = ids();
        let logs = phase(vec![transform(vec![a], vec![b], vec![])]);
        let (_map, _proj, leaks) =
            collapse(&logs, &set([a, b]), &set([b]), &SourceProjection::new());
        assert!(
            leaks.contains(&Leak::ProducedLive { produced: b }),
            "{leaks:?}"
        );
    }

    #[test]
    fn empty_consumed_with_blame_is_the_legal_pure_insertion_shape() {
        // A consume-nothing Transform that names blame is a pure insertion: the
        // output gets empty lineage roots (present in the map with empty `up`)
        // and a blame-attributed projection entry. No EmptyConsumed leak.
        let [a, b] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(
            a,
            SourceAttribution {
                spans: vec![span(1, 4)],
                rewritten: RewriteTag::direct_image(),
            },
        );
        let logs = phase(vec![transform(vec![], vec![b], vec![a])]);
        let (map, proj, leaks) = collapse(&logs, &set([a]), &set([a, b]), &upstream);
        assert!(leaks.is_empty(), "pure insertion is leak-free: {leaks:?}");
        // b is present in the map with genuinely empty lineage roots.
        assert!(
            map.upstream(&b).is_empty(),
            "pure insertion has no lineage ancestor"
        );
        // b is attributed via its blame, not via consumption.
        let attr = proj.get(&b).expect("b attributed via blame");
        assert_eq!(attr.spans, vec![span(1, 4)]);
    }

    #[test]
    fn leak_empty_consumed_fires_when_consumed_and_blame_both_empty() {
        // A truly unanchored mint: neither consumption nor blame explains it.
        let [a, b] = ids();
        let logs = phase(vec![transform(vec![], vec![b], vec![])]);
        let (_map, _proj, leaks) =
            collapse(&logs, &set([a]), &set([a, b]), &SourceProjection::new());
        assert!(
            leaks
                .iter()
                .any(|l| matches!(l, Leak::EmptyConsumed { .. })),
            "{leaks:?}"
        );
    }

    // ---- blame / attribution ----------------------------------------------

    #[test]
    fn expansion_blame_yields_deduped_ordered_span_union() {
        // blame = [A, B]; A: [s1, s2], B: [s2, s3] → [s1, s2, s3].
        let [a, b, out] = ids();
        let (s1, s2, s3) = (span(0, 1), span(2, 3), span(4, 5));
        let mut upstream = SourceProjection::new();
        upstream.insert(
            a,
            SourceAttribution {
                spans: vec![s1, s2],
                rewritten: RewriteTag::direct_image(),
            },
        );
        upstream.insert(
            b,
            SourceAttribution {
                spans: vec![s2, s3],
                rewritten: RewriteTag::direct_image(),
            },
        );
        // A and B survive (blame ⊥ consumption); the step consumes neither but
        // carries them, so use a survivor-carry-free shape: consume a separate
        // transient. Here we consume A and produce `out`, blaming both A and B.
        let logs = phase(vec![transform(vec![a], vec![out], vec![a, b])]);
        let (_map, proj, leaks) = collapse(&logs, &set([a, b]), &set([out, b]), &upstream);
        // B is carried to the output to avoid a Dropped leak; A is consumed.
        assert_eq!(
            leaks,
            vec![],
            "blame does not affect fate accounting: {leaks:?}"
        );
        let attr = proj.get(&out).expect("out attributed");
        assert_eq!(attr.spans, vec![s1, s2, s3]);
        let tag = &attr.rewritten;
        assert_eq!(tag.via, Pass::Inline);
        assert_eq!(tag.nature, Nature::Expansion);
    }

    #[test]
    fn machinery_empty_blame_is_present_with_empty_spans() {
        // The "known node, no source anchor" case: present in the projection
        // with spans: [], distinct from a node absent from the projection.
        let [a, b] = ids();
        let logs = vec![(
            Pass::Inline,
            vec![RewriteStep {
                op: Op::Transform {
                    consumed: vec![a],
                    produced: vec![b],
                },
                blame: vec![],
                nature: Nature::Machinery,
                label: "machinery.plumbing",
            }],
        )];
        let (_map, proj, leaks) = collapse(&logs, &set([a]), &set([b]), &SourceProjection::new());
        assert!(leaks.is_empty(), "{leaks:?}");
        let attr = proj.get(&b).expect("b present in projection");
        assert!(attr.spans.is_empty(), "known node, no source anchor");
        let tag = &attr.rewritten;
        assert_eq!(tag.nature, Nature::Machinery);
    }

    #[test]
    fn node_absent_from_projection_is_distinct_from_empty_spans() {
        // An input id with no upstream attribution that survives untouched has
        // no projection entry at all — distinct from present-but-empty spans.
        let [a] = ids();
        let (_map, proj, leaks) = collapse(
            &phase(vec![]),
            &set([a]),
            &set([a]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert!(
            !proj.contains_key(&a),
            "unknown node absent from projection"
        );
    }

    #[test]
    fn copy_empty_blame_mirrors_origin_retagged() {
        // Copy with empty blame mirrors the origin's spans, re-tagged with the
        // copy's {via, nature, label}.
        let [a, b] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(
            a,
            SourceAttribution {
                spans: vec![span(1, 2)],
                rewritten: RewriteTag::direct_image(),
            },
        );
        let logs = vec![(
            Pass::Inline,
            vec![RewriteStep {
                op: Op::Copy {
                    origin: a,
                    produced: vec![b],
                },
                blame: vec![],
                nature: Nature::Expansion,
                label: "copy.mirror",
            }],
        )];
        let (_map, proj, leaks) = collapse(&logs, &set([a]), &set([a, b]), &upstream);
        assert!(leaks.is_empty(), "{leaks:?}");
        let attr = proj.get(&b).expect("copy attributed");
        assert_eq!(attr.spans, vec![span(1, 2)], "mirrors origin spans");
        let tag = &attr.rewritten;
        assert_eq!(tag.via, Pass::Inline);
        assert_eq!(tag.nature, Nature::Expansion);
        assert_eq!(tag.label, "copy.mirror");
    }

    // ---- the lowering fold (collapse_lowering) -----------------------------

    fn leaf(id: NodeId, sp: Span, nature: Nature, label: RewriteLabel) -> LoweringStep {
        LoweringStep {
            op: Op::Transform {
                consumed: Vec::new(),
                produced: vec![id],
            },
            anchor: vec![sp],
            nature,
            label,
        }
    }

    fn lowering_copy(origin: NodeId, produced: Vec<NodeId>) -> LoweringStep {
        LoweringStep {
            op: Op::Copy { origin, produced },
            anchor: Vec::new(),
            nature: Nature::Source,
            label: "lower.copy",
        }
    }

    #[test]
    fn lowering_pure_insertion_leaf_is_attributed_from_its_anchor() {
        // A leaf mint: no input pane, empty roots, attribution straight from the
        // literal anchor span with the direct-image tag.
        let [a] = ids();
        let log = vec![leaf(a, span(2, 7), Nature::Source, "lower.image")];
        let (proj, leaks) = collapse_lowering(&log, &set([a]));
        assert!(leaks.is_empty(), "{leaks:?}");
        let attr = proj.get(&a).expect("leaf attributed");
        assert_eq!(attr.spans, vec![span(2, 7)]);
        assert_eq!(attr.rewritten.via, Pass::Lower);
        assert_eq!(attr.rewritten.nature, Nature::Source);
    }

    #[test]
    fn lowering_copy_mirrors_its_origins_folded_entry() {
        // The compare-chain shape: an operand leaf (Source), then a freshened
        // second-use copy mirroring it verbatim.
        let [orig, copy] = ids();
        let log = vec![
            leaf(orig, span(0, 1), Nature::Source, "lower.image"),
            lowering_copy(orig, vec![copy]),
        ];
        let (proj, leaks) = collapse_lowering(&log, &set([orig, copy]));
        assert!(leaks.is_empty(), "{leaks:?}");
        let orig_attr = proj.get(&orig).expect("origin");
        let copy_attr = proj.get(&copy).expect("copy");
        assert_eq!(
            copy_attr.spans, orig_attr.spans,
            "copy mirrors origin spans"
        );
        assert_eq!(
            copy_attr.rewritten.nature,
            Nature::Source,
            "copy mirrors origin's Source tag"
        );
    }

    #[test]
    fn lowering_born_copied_discarded_template_composes_away() {
        // The uncurry shape: a template proj node is minted (leaf, Machinery),
        // copied into an occurrence's interior, and never itself placed in the
        // output tree. It is live at the end but neither placed nor an output id,
        // so it composes away with NO leak (there is no Dropped class in
        // lowering, and Unexplained checks outputs only).
        let [template, occ_interior] = ids();
        let log = vec![
            leaf(
                template,
                span(4, 9),
                Nature::Machinery,
                "lower.uncurry_proj",
            ),
            lowering_copy(template, vec![occ_interior]),
        ];
        // Output = only the copied interior; the template is discarded.
        let (proj, leaks) = collapse_lowering(&log, &set([occ_interior]));
        assert!(
            leaks.is_empty(),
            "born-copied-discarded template must compose away leak-free: {leaks:?}"
        );
        assert_eq!(
            proj.get(&occ_interior).expect("interior").rewritten.nature,
            Nature::Machinery,
            "interior mirrors the template's machinery tag"
        );
        assert!(
            !proj.contains_key(&template),
            "the discarded template is not an output node"
        );
    }

    #[test]
    fn lowering_unexplained_fires_on_unrecorded_mint() {
        // An output-tree node that no leaf produced and no copy placed — the
        // unrecorded-lowering-mint class.
        let [tagged, orphan] = ids();
        let log = vec![leaf(tagged, span(0, 1), Nature::Source, "lower.image")];
        let (_proj, leaks) = collapse_lowering(&log, &set([tagged, orphan]));
        assert!(
            leaks.contains(&Leak::Unexplained { output: orphan }),
            "{leaks:?}"
        );
    }

    #[test]
    fn lowering_substituted_root_inherits_its_occurrences_leaf_attribution() {
        // A substituted root carries the occurrence's own id, so the log holds no
        // step for it — just the occurrence's leaf entry — while its interior
        // children are copies of the replacement template. The root keeps its own
        // (Source) attribution; the interior mirrors the template (Machinery).
        let [occurrence, tmpl_child, occ_child] = ids();
        let log = vec![
            // The param-use occurrence, imaged Source at its mint.
            leaf(occurrence, span(10, 11), Nature::Source, "lower.image"),
            // The template child (tuple ref / projection index), machinery.
            leaf(
                tmpl_child,
                span(3, 6),
                Nature::Machinery,
                "lower.uncurry_proj",
            ),
            // The occurrence's interior is a freshened copy of the template child.
            lowering_copy(tmpl_child, vec![occ_child]),
        ];
        // Output tree: the carried root (occurrence id) + its fresh interior.
        let (proj, leaks) = collapse_lowering(&log, &set([occurrence, occ_child]));
        assert!(leaks.is_empty(), "{leaks:?}");
        let root_attr = proj.get(&occurrence).expect("carried root");
        assert_eq!(
            root_attr.rewritten.nature,
            Nature::Source,
            "the carried root keeps the occurrence's own Source attribution"
        );
        assert_eq!(root_attr.spans, vec![span(10, 11)]);
        assert_eq!(
            proj.get(&occ_child).expect("interior").rewritten.nature,
            Nature::Machinery,
            "the interior mirrors the template's machinery tag"
        );
    }

    #[test]
    fn lowering_reimage_last_tag_wins_without_produced_live_leak() {
        // `lower_expr` re-tags an arm's already-tagged root as the construct's
        // direct image: two leaf steps for one id. The lowering fold treats the
        // re-image as last-tag-wins (no ProducedLive leak); the later Source tag
        // wins over the earlier machinery one.
        let [id] = ids();
        let log = vec![
            leaf(id, span(0, 5), Nature::Machinery, "lower.compare_chain"),
            leaf(id, span(0, 5), Nature::Source, "lower.image"),
        ];
        let (proj, leaks) = collapse_lowering(&log, &set([id]));
        assert!(leaks.is_empty(), "re-image is not a leak: {leaks:?}");
        assert_eq!(
            proj.get(&id).expect("reimaged").rewritten.nature,
            Nature::Source,
            "the later (Source) tag wins"
        );
    }

    // ---- the recorder ------------------------------------------------------
    //
    // These exercise the hooks through *real* `Expr` construction (`Expr::lit`,
    // `Expr::tuple`) and the freshening `Clone`, not hand-built steps, so the hook
    // wiring in `expr.rs` is under test too.

    use crate::ccl::Lit;
    use crate::ccl::expr::Expr;

    #[test]
    fn transform_step_captures_births_as_produced() {
        let session = RecorderSession::new();
        let consumed = NodeId::fresh();
        let (a, b);
        {
            let _g = step("rw.build", vec![consumed], vec![], Nature::Expansion);
            a = Expr::lit(Lit::Int(1)).node_id();
            b = Expr::lit(Lit::Int(2)).node_id();
        }
        let log = session.into_log();
        assert_eq!(log.len(), 1);
        assert_eq!(
            log[0].op,
            Op::Transform {
                consumed: vec![consumed],
                produced: vec![a, b],
            },
            "produced = exactly the ids built in the step's extent, in order",
        );
        assert_eq!(step_stack_depth(), 0, "guard popped its frame");
    }

    #[test]
    fn nested_steps_capture_births_in_the_innermost_frame_only() {
        let session = RecorderSession::new();
        let (outer_c, inner_c) = (NodeId::fresh(), NodeId::fresh());
        let (outer_pre, inner_id, outer_post);
        {
            let _outer = step("rw.outer", vec![outer_c], vec![], Nature::Expansion);
            outer_pre = Expr::lit(Lit::Int(0)).node_id();
            {
                let _inner = step("rw.inner", vec![inner_c], vec![], Nature::Expansion);
                inner_id = Expr::lit(Lit::Int(1)).node_id();
            }
            outer_post = Expr::lit(Lit::Int(2)).node_id();
        }
        let log = session.into_log();
        // Inner flushes on its (earlier) drop, then outer.
        assert_eq!(log.len(), 2);
        assert_eq!(
            log[0].op,
            Op::Transform {
                consumed: vec![inner_c],
                produced: vec![inner_id],
            },
            "inner step owns only the birth in its extent",
        );
        assert_eq!(
            log[1].op,
            Op::Transform {
                consumed: vec![outer_c],
                produced: vec![outer_pre, outer_post],
            },
            "outer step owns the births outside the inner extent, not the inner birth",
        );
    }

    #[test]
    fn deep_freshen_in_a_step_yields_per_origin_copies() {
        // Build a 3-node tree (tuple + two lits) OUTSIDE any step, then clone it
        // inside a copy-only frame — one that consumes nothing and mints nothing
        // of its own, so its whole output is the freshen pairs `Clone` reports
        // through the `on_copy` hook.
        let source = Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]);
        // The source's node ids are the origins each per-node `Copy` should record.
        let old_ids: HashSet<NodeId> = std::iter::once(source.node_id())
            .chain(source.child_exprs().iter().map(|c| c.node_id()))
            .collect();

        let session = RecorderSession::new();
        let clone = {
            let _g = copy_frame("dup");
            source.clone()
        };
        let log = session.into_log();

        // The clone is a distinct 3-node tree sharing no id with its source.
        let fresh_ids: HashSet<NodeId> = std::iter::once(clone.node_id())
            .chain(clone.child_exprs().iter().map(|c| c.node_id()))
            .collect();
        assert_eq!(fresh_ids.len(), 3);
        assert!(
            fresh_ids.is_disjoint(&old_ids),
            "a clone shares no id with its source"
        );

        // Three nodes freshened: three per-origin Copy steps, one produced each,
        // one Copy per pre-freshen origin id.
        assert_eq!(log.len(), 3, "one Copy step per freshened origin");
        let mut copied_origins = HashSet::new();
        for s in &log {
            match &s.op {
                Op::Copy { origin, produced } => {
                    assert_eq!(produced.len(), 1, "one produced entry per freshened node");
                    copied_origins.insert(*origin);
                }
                other => panic!("expected only Copy steps, got {other:?}"),
            }
        }
        assert_eq!(
            copied_origins, old_ids,
            "every freshened node recorded a per-origin copy",
        );
    }

    #[test]
    fn transform_frame_capturing_only_freshens_emits_no_empty_transform() {
        // A Transform frame opened purely to capture a deep freshen (no consumed
        // ids, no births) emits only its per-origin Copy steps — never an empty
        // `Transform { consumed: [], produced: [] }`.
        let source = Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]);

        let session = RecorderSession::new();
        {
            let _g = step("wrap.freshen", vec![], vec![], Nature::Machinery);
            let _clone = source.clone();
        }
        let log = session.into_log();
        assert_eq!(log.len(), 3, "only the three per-origin Copy steps");
        assert!(
            log.iter().all(|s| matches!(s.op, Op::Copy { .. })),
            "no empty Transform emitted: {log:?}",
        );
    }

    #[test]
    fn no_step_open_records_nothing() {
        let session = RecorderSession::new();
        // Construction and cloning with an empty stack capture nowhere.
        let _e = Expr::lit(Lit::Int(1));
        let x = Expr::lit(Lit::Int(2));
        let _copy = x.clone();
        let log = session.into_log();
        assert!(log.is_empty(), "empty stack ⇒ nothing recorded: {log:?}");
    }

    #[test]
    fn no_session_installed_makes_the_flush_a_silent_no_op() {
        // A step open with no ACTIVE_LOG: births still capture into the frame,
        // but the guard's flush finds no log and does nothing (no panic).
        assert!(
            ACTIVE_LOG.with(|s| s.borrow().is_none()),
            "precondition: no session installed",
        );
        {
            let _g = step("rw", vec![NodeId::fresh()], vec![], Nature::Expansion);
            let _a = Expr::lit(Lit::Int(1));
        }
        assert_eq!(
            step_stack_depth(),
            0,
            "guard still pops cleanly with no log"
        );
    }

    #[test]
    fn panic_inside_a_step_unwinds_without_poisoning_the_stack() {
        assert_eq!(step_stack_depth(), 0, "clean precondition");
        let result = std::panic::catch_unwind(|| {
            let _g = step("boom", vec![NodeId::fresh()], vec![], Nature::Expansion);
            let _a = Expr::lit(Lit::Int(1));
            panic!("deliberate panic inside an open step");
        });
        assert!(result.is_err(), "the panic propagated");
        assert_eq!(
            step_stack_depth(),
            0,
            "the guard's Drop popped the frame on unwind"
        );

        // Recording still works afterward.
        let session = RecorderSession::new();
        let consumed = NodeId::fresh();
        let a;
        {
            let _g = step("rw", vec![consumed], vec![], Nature::Expansion);
            a = Expr::lit(Lit::Int(7)).node_id();
        }
        let log = session.into_log();
        assert_eq!(log.len(), 1);
        assert_eq!(
            log[0].op,
            Op::Transform {
                consumed: vec![consumed],
                produced: vec![a],
            },
        );
    }

    #[test]
    fn default_uses_placeholder_records_nothing_and_two_defaults_share_id() {
        let session = RecorderSession::new();
        let d1 = Expr::default();
        let d2 = Expr::default();
        // Even inside an open step, a Default throwaway must not be captured.
        let consumed = NodeId::fresh();
        {
            let _g = step("rw", vec![consumed], vec![], Nature::Expansion);
            let _d3 = Expr::default();
        }
        let log = session.into_log();

        assert_eq!(
            d1.node_id(),
            NodeId::PLACEHOLDER,
            "Default mints the sentinel"
        );
        assert_eq!(
            d1.node_id(),
            d2.node_id(),
            "two Defaults share the placeholder id (they compare equal regardless — \
             node_id is excluded from PartialEq)",
        );
        assert_eq!(log.len(), 1);
        match &log[0].op {
            Op::Transform { produced, .. } => {
                assert!(
                    produced.is_empty(),
                    "the Default was not captured: {produced:?}"
                )
            }
            other => panic!("expected a Transform, got {other:?}"),
        }
    }

    #[test]
    fn end_to_end_session_step_feeds_collapse() {
        // Ties (a) and (b): record a real rewrite through a session, then fold
        // the drained log with `collapse` and check the resulting relation.
        let a = Expr::lit(Lit::Int(1));
        let a_id = a.node_id();

        let session = RecorderSession::new();
        let out_id;
        {
            let _g = step("rw.replace", vec![a_id], vec![a_id], Nature::Expansion);
            out_id = Expr::lit(Lit::Int(2)).node_id();
        }
        let log = session.into_log();

        let logs = vec![(Pass::Inline, log)];
        let (map, proj, leaks) = collapse(
            &logs,
            &set([a_id]),
            &set([out_id]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(map.upstream(&out_id), &[a_id]);
        assert_eq!(map.downstream(&a_id), &[out_id]);
        // The output attributes to the (blamed) input via this pass.
        let attr = proj.get(&out_id).expect("output attributed");
        let tag = &attr.rewritten;
        assert_eq!(tag.via, Pass::Inline);
        assert_eq!(tag.label, "rw.replace");
    }

    #[test]
    fn born_copied_discarded_template_composes_without_leaks() {
        // The `fold_induction_loop`/`build_writer` template shape (transact/letrec
        // instrumentation hazard): a single frame births a template `T`, copies
        // it per read site (via `Subst::discharge_env_in_place`), and discards
        // `T` (it never reaches the output tree). Per `OpenStep::flush_into`'s
        // refinement the frame's `Transform` (which produces `T`) flushes BEFORE
        // the captured `Copy` steps, so `T` is live when the copies are processed —
        // the whole shape composes in ONE frame, no split needed. `T` remains live
        // at collapse (never consumed) but is neither an input-pane nor an
        // output-pane id, so it triggers no leak (`Dropped` checks inputs only,
        // `Unexplained` checks outputs only).
        let origin = NodeId::fresh(); // an input-pane id the template descends from
        let (t, c1, c2);
        let session = RecorderSession::new();
        {
            let _g = step(
                "test.template",
                vec![origin],
                vec![origin],
                Nature::Machinery,
            );
            // Birth the template inside the frame (a mint captured as `produced`).
            let template = Expr::lit(Lit::Int(0));
            t = template.node_id();
            // Copy it twice — one freshened clone per read site.
            let r1 = template.clone();
            c1 = r1.node_id();
            let r2 = template.clone();
            c2 = r2.node_id();
        }
        let log = session.into_log();
        // Flush order: the Transform producing T first, then a Copy per origin.
        assert_eq!(
            log[0].op,
            Op::Transform {
                consumed: vec![origin],
                produced: vec![t],
            },
            "the Transform (producing T) flushes before the captured copies: {log:?}",
        );
        assert!(
            log[1..]
                .iter()
                .all(|s| matches!(&s.op, Op::Copy { origin: o, .. } if *o == t)),
            "the per-origin copies of T flush after it is live: {log:?}",
        );

        let logs = vec![(Pass::Inline, log)];
        let (map, _proj, leaks) = collapse(
            &logs,
            &set([origin]),
            &set([c1, c2]),
            &SourceProjection::new(),
        );
        assert!(
            leaks.is_empty(),
            "born-copied-discarded template composes leak-free in one frame: {leaks:?}",
        );
        // c1/c2 carry T's roots — the frame's consumed lineage (`origin`).
        assert_eq!(map.upstream(&c1), &[origin]);
        assert_eq!(map.upstream(&c2), &[origin]);
        assert_eq!(
            sorted(map.downstream(&origin).to_vec()),
            sorted(vec![c1, c2])
        );
    }
}

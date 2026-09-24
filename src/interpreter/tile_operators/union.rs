use bit_set::BitSet;

use super::*;
use crate::interpreter::operator_graph::value_at;
use crate::{
    ccl::TagMap,
    interpreter::{
        ColumnValue, Consumer, Extent, Scheduler, UnionArm, Value, forwarding_consumer,
        shared_consumer,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// UnionOperator / UnionProducer
// ---------------------------------------------------------------------------

/// Merges N `DataFunction` operators into one by taking the discriminated
/// union of their domains, over a codomain its **caller declares**.
///
/// The output tiling is `DataFunction { domain: Union(d₀, …, dₙ₋₁), codomain }`.
/// The domain keeps every arm apart — which arm a row came from is what
/// `final_or_default` dispatches on. The codomain does the opposite: the arms are
/// alternative values at one row, so it is their **join** — but that join is
/// already computed, by inference, and stamped on the union node as its value
/// type. It is passed in rather than re-derived here (see [`new`](Self::new)).
pub struct UnionOperator {
    base: OperatorBase,
    /// Input operators; each must have a `DataFunction` tiling.
    inputs: Vec<Box<dyn TileOperator>>,
    /// Flat-merge mode (see [`new_flat`](Self::new_flat)): arms share one domain
    /// extent with disjoint positions, merged into a single flat `DataFunction`
    /// (sorted by domain key) rather than a tagged `ColumnValue::Union`.
    flat: bool,
    /// The level the union merges at, which leaves every level above it standing — the
    /// same parameter [`Zip::new_at`](super::Zip::new_at) takes, and for the same reason. A
    /// partition inside a nested recurrence runs once per enclosing row, so its arms
    /// agree above the level being merged and differ only below it.
    level: CurryLevel,
}

impl UnionOperator {
    /// Create a new `UnionOperator` from the given input operators.
    ///
    /// All inputs must be `DataFunction` tilings.  The output domain is
    /// `Extent::Union` of all input domains.
    ///
    /// `declared_codomain` is the merged column's value extent, read off the union
    /// node's type — the arms' join as inference computed it. Re-deriving it here
    /// ran a second join over a weaker lattice, which disagreed: `Extent` has no
    /// record rule, so arms at different record widths came out a positional sum
    /// where the type layer said `{a: Int}`.
    pub fn new(inputs: Vec<Box<dyn TileOperator>>, declared_codomain: Extent) -> Self {
        let tiling = Self::coproduct_tiling(&inputs, declared_codomain);
        Self {
            base: OperatorBase::new(tiling),
            inputs,
            flat: false,
            level: CurryLevel::OUTERMOST,
        }
    }

    /// The tiling of each input `level` levels in — what the union combines, with the
    /// levels above it left standing.
    fn inner_tilings(inputs: &[Box<dyn TileOperator>], level: CurryLevel) -> Vec<Tiling> {
        inputs
            .iter()
            .map(|op| {
                let mut t = op.tiling();
                for _ in 0..level.index() {
                    let Tiling::DataFunction { codomain, .. } = t else {
                        panic!("UnionOperator: no {level} in {}", op.tiling())
                    };
                    t = codomain;
                }
                t.clone()
            })
            .collect()
    }

    /// The tagged coproduct tiling the arms imply: one `Extent::Union` domain,
    /// and the codomain they agree on or the declared one they merge into.
    fn coproduct_tiling(inputs: &[Box<dyn TileOperator>], declared_codomain: Extent) -> Tiling {
        let arms = Self::inner_tilings(inputs, CurryLevel::OUTERMOST);
        Self::coproduct_of(&arms, declared_codomain)
    }

    /// [`coproduct_tiling`](Self::coproduct_tiling) over the arm tilings themselves, so
    /// the same rule applies at a standing level as at the top.
    fn coproduct_of(arms: &[Tiling], declared_codomain: Extent) -> Tiling {
        assert!(
            !arms.is_empty(),
            "UnionOperator requires at least one input"
        );
        let domains: Vec<Extent> = arms
            .iter()
            .map(|t| match t {
                Tiling::DataFunction { domain, .. } => domain.clone(),
                other => panic!("UnionOperator: expected a function tiling, got {other}"),
            })
            .collect();
        let codomains: Vec<&Tiling> = arms
            .iter()
            .map(|t| match t {
                Tiling::DataFunction { codomain, .. } => codomain.as_ref(),
                _ => unreachable!(),
            })
            .collect();

        // Agreeing arms keep their shared tiling: a `Tiling` carries layout an
        // `Extent` cannot (a record column is struct-of-arrays), and that is the
        // one thing the operands know that the type does not.
        let codomain = if codomains.windows(2).all(|w| w[0] == w[1]) {
            debug_assert_eq!(
                codomains[0].extent(),
                declared_codomain,
                "the arms agree on a codomain the node's type does not declare"
            );
            codomains[0].clone()
        } else {
            // Differing arms get merged into one column, so each must fit in one:
            // a `Scalar`, or a `Record` of them — a compound mutable variable's arms are
            // the latter and disagree on *layout* (a constructed tuple arrives as
            // a record of columns, the carried snapshot as one column of record
            // values), which `flat_merge` reconciles by rebuilding the column at
            // the declared tiling. A function-tiled arm is what must not pass:
            // flattening it would declare a scalar column of *functions*, which no
            // producer can emit. Rejected here, where the shape is known.
            for t in &codomains {
                match t {
                    Tiling::Scalar(_) => {}
                    Tiling::Record(fields)
                        if fields.values().all(|f| matches!(f, Tiling::Scalar(_))) => {}
                    other => panic!(
                        "UnionOperator: arms with differing codomains merge into one \
                         column, so each must be a `Scalar` or a `Record` of them; \
                         got {other}"
                    ),
                }
            }
            Tiling::Scalar(declared_codomain)
        };

        Tiling::data_function(Extent::Union(TagMap::from_positional(domains)), codomain)
    }

    /// Collapse the coproduct domain [`new`](Self::new) built back to the one
    /// extent the arms share.
    ///
    /// Sharing it is the precondition — the arms are disjoint slices of one
    /// collection, which is what makes the merge a reassembly rather than a
    /// concatenation — so this is a check, not a reconciliation. Arms that
    /// genuinely differ are a copairing, and [`new`](Self::new) is the
    /// constructor for those.
    fn flatten_domain(tiling: Tiling) -> Tiling {
        let (domain, codomain) = match tiling {
            Tiling::DataFunction { domain, codomain } => (domain, codomain),
            other => return other,
        };
        // A nest is not the shape a flat merge reassembles; hand it back untouched.
        if codomain.as_ref().holds_a_level() {
            return Tiling::DataFunction { domain, codomain };
        }
        let mut arms = match domain {
            Extent::Union(ds) => ds.into_values(),
            other => vec![other],
        }
        .into_iter();
        let domain = arms.next().expect("at least one arm");
        for other in arms {
            assert_eq!(
                other, domain,
                "a flat merge reassembles one domain, but the arms carry different \
                 extents; arms over distinct index sets are a copairing"
            );
        }
        Tiling::DataFunction { domain, codomain }
    }

    /// A **flat-merge** union: arms over the *same* base extent (disjoint runtime
    /// subsets of one domain) merge back to that base rather than a tagged
    /// `Extent::Union`, so the result co-iterates with a sibling field. This is the
    /// writer-body value-`Case` fan-out `⧺ᵢ filter_values(π̂ᵢ) ≫ eᵢ`: every arm
    /// filters the *same* fed element stream, so their domains share one extent and
    /// their positions are disjoint by first-match. (The tagged [`new`](Self::new)
    /// is for a sourceless union whose arms have genuinely distinct extents — a Σ /
    /// C-form dispatch read by `final_or_default`.)
    pub fn new_flat(inputs: Vec<Box<dyn TileOperator>>, declared_codomain: Extent) -> Self {
        Self::new_flat_at(inputs, declared_codomain, CurryLevel::OUTERMOST)
    }

    /// [`new_flat`](Self::new_flat) at `level`, leaving every level above it standing.
    ///
    /// `level` is the caller's to state, exactly as it is for
    /// [`Zip::new_at`](super::Zip::new_at): the arms of a partition agree below the
    /// merged level just as readily as at it, so their own shapes cannot say where the
    /// merge belongs.
    pub fn new_flat_at(
        inputs: Vec<Box<dyn TileOperator>>,
        declared_codomain: Extent,
        level: CurryLevel,
    ) -> Self {
        // Narrow before minting, so the identity an operator is born with carries
        // the tiling it keeps. Reaching into `base.tiling` afterwards would leave
        // the shape recorded at construction stale.
        let arms = Self::inner_tilings(&inputs, level);
        let merged = Self::flatten_domain(Self::coproduct_of(&arms, declared_codomain));
        let tiling = with_values_at(inputs[0].tiling(), level, merged);
        Self {
            base: OperatorBase::new(tiling),
            inputs,
            flat: true,
            level,
        }
    }
}

/// Flat-merge disjoint `DataFunction` arms into one flat tile, sorted by domain
/// key. Each arm is a filtered slice of the *same* fed element stream (a
/// writer-body value-`Case` fan-out `⧺ᵢ filter_values(π̂ᵢ) ≫ eᵢ`, or a `match`'s
/// tag fan-out), so the arms' keys are disjoint and reassemble the full column —
/// which then co-iterates with the decision record's sibling `commit` field. The
/// codomain is a scalar decision-field value, or a materialized compound `Tile::Record`
/// for a tuple/record accumulator. A key is complete once every arm calls it complete,
/// and beneath a key each level states what the arm holding it says.
///
/// **The key is the domain value, not a position.** Reassembling needs only a
/// total order (to restore the fed order) and equality (to catch two arms
/// claiming one key), and both hold for any *one* collection's keys — its domain
/// is a single [`Extent`], so its values are homogeneous in shape. A `UInt`
/// position is the common case; a fed stream whose own index set is a coproduct
/// carries `Union { tag, inner }` keys instead, which [`Value`]'s order already
/// compares lexicographically by tag then payload. Keying on `usize` is what
/// restricted this to the former.
fn flat_merge(tiles: Vec<Tile>, domain_extent: &Extent, codomain_tiling: &Tiling) -> Tile {
    // The arms' codomains are concatenated and then gathered in key order, rather than
    // reassembled as a list of `Value` pairs. A gather is shape-agnostic, so an arm whose
    // codomain carries a level — a collection-valued mutable variable's write — travels like
    // any other; materializing each row into a value could not carry one.
    let mut pairs: Vec<(Value, usize)> = Vec::new();
    let mut codomains: Option<Tile> = None;
    // A key comes from whichever arm holds it, so it is complete once every arm calls it
    // complete: an arm finished with a key it never held says nothing about its siblings.
    let mut domain_predicate = Predicate::True;
    let mut offset = 0usize;
    for tile in tiles {
        let Tile::DataFunction {
            domain,
            codomain,
            domain_predicate: dp,
            deleted,
            ..
        } = tile
        else {
            panic!("flat_merge: expected a collection arm, got {tile:?}");
        };
        domain_predicate = domain_predicate.intersect(&dp);
        let live: Vec<usize> = (0..domain.len())
            .filter(|r| !deleted.contains(*r))
            .collect();
        // An arm contributing no row is skipped rather than concatenated: it carries an
        // empty column whose kind is whatever its producer happened to build, and
        // concatenating that against a sibling's is a mismatch over nothing.
        if live.is_empty() {
            continue;
        }
        for &row in &live {
            pairs.push((domain.index_at(row), offset + row));
        }
        offset += domain.len();
        // Arms disagree on whether a compound value rides materialized (`Scalar(Records)`)
        // or as a struct-of-arrays `Record`, so a value-shaped arm is restated in the
        // declared shape before being concatenated. An arm carrying a level passes through:
        // it is already the shape its tiling names, and materializing it is what has no
        // column to go in.
        let codomain = if codomain.holds_a_level() {
            // What an arm states beneath a key is the arm's to say only for the keys it holds
            // live: a key it deleted or never held is a sibling's, whose own statement is the
            // one that counts there.
            let mut codomain = *codomain;
            let held = Predicate::from_column_value(
                &domain.select_indices(live.iter().copied(), live.len()),
            );
            codomain.map_level_predicates(&mut |depth, stated| {
                stated.intersect(&Predicate::True.qualified_by(&held, depth))
            });
            codomain
        } else if codomain_tiling.holds_a_level() {
            unreachable!(
                "flat_merge: an arm with live rows under a codomain tiling that holds a level \
                 carries the level itself, got {codomain:?}"
            )
        } else {
            column_value_to_tile(scalar_tile_to_column_value(*codomain), codomain_tiling)
        };
        match &mut codomains {
            Some(acc) => acc.merge_rows(codomain),
            None => codomains = Some(codomain),
        }
    }
    // Disjoint by first-match, so a stable sort by key reassembles the full column
    // in the fed order — matching the sibling `commit` field's domain.
    //
    // The keys come from one collection's domain, so they are one `Extent`'s
    // values and mutually comparable. An incomparable pair means two arms were fed
    // *different* domains, which is not a disjoint join at all — the caller built
    // the wrong node — so say that rather than ordering them arbitrarily.
    pairs.sort_by(|(a, _), (b, _)| {
        a.partial_cmp(b).unwrap_or_else(|| {
            panic!(
                "flat_merge: domain keys {a:?} and {b:?} are not comparable, so these \
                 arms are not slices of one domain — a disjoint join requires that, \
                 and a copairing (whose arms deliberately live over distinct index \
                 sets) is the node for arms that do not"
            )
        })
    });
    // Disjointness is a *precondition*, not something the merge can repair: two
    // arms claiming one position put two values at one domain key, which the tile
    // contract forbids ("known data inside a Tile is immutable" — see the
    // interpreter's module docs) and which no type checks. It would fail
    // *silently*: the sort just leaves the duplicates adjacent, and a column one
    // row too long flows on downstream. The guard fan-out gets disjointness from
    // first-match and the tag fan-out from the tags; neither is enforced. Check it
    // where the arms are actually side by side rather than trusting the caller: a
    // value-`Case` whose first-match gates overlap, and a tag fan-out that lost a
    // `variant_project` to const-reduction, both land here. The scan is free
    // beside the sort above, so this is a hard assert rather than a debug one.
    if let Some(w) = pairs.windows(2).find(|w| w[0].0 == w[1].0) {
        panic!(
            "flat_merge: arms are not disjoint — domain key {} is claimed by more \
             than one arm, so the merge would place two values at that key",
            w[0].0
        );
    }
    let keys: Vec<Value> = pairs.iter().map(|(k, _)| k.clone()).collect();
    let picked: Vec<usize> = pairs.iter().map(|(_, row)| *row).collect();
    let codomain = match codomains {
        Some(all) => all.select_rows(&picked),
        None => codomain_tiling.empty_at_no_rows(),
    };
    Tile::data_function(
        ColumnValue::from_values(keys, domain_extent),
        Box::new(codomain),
        domain_predicate,
        BitSet::new(),
    )
}

impl TileOperator for UnionOperator {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(value_at(i, &**input));
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let shared = shared_consumer(consumer);
        let input_producers: Vec<Box<dyn TileProducer>> = self
            .inputs
            .iter_mut()
            .map(|op| {
                op.subscribe(
                    op.tiling().universal_guard(),
                    forwarding_consumer(&shared),
                    scheduler,
                )
            })
            .collect();
        Box::new(UnionProducer {
            base: ProducerBase::new(UnionProducer::alloc_id(), self.tiling()),
            inputs: input_producers,
            flat: self.flat,
            level: self.level,
        })
    }
}

/// Producer for [`UnionOperator`]: concatenates all input `DataFunction` tiles
/// into a single tile with a `ColumnValue::Union` domain and interleaved codomain.
struct UnionProducer {
    base: ProducerBase,
    /// The level the union merges at — see [`UnionOperator::new_flat_at`].
    level: CurryLevel,
    inputs: Vec<Box<dyn TileProducer>>,
    /// Flat-merge mode (see [`UnionOperator::new_flat`]).
    flat: bool,
}

impl UnionProducer {
    /// [`flat_merge`] once per row of the standing levels, reassembled beneath them.
    ///
    /// A row's group is a collection in its own right, so retaining it leaves exactly the
    /// flat tile the merge already knows how to handle — which is why the standing case
    /// needs no second merge, only [`Tile::regroup_beneath`]. At level zero that is the
    /// whole tile as one group, so this is the only path.
    fn merged(
        &self,
        mut tiles: Vec<Tile>,
        domain_extent: &Extent,
        codomain_tiling: &Tiling,
    ) -> Tile {
        tiles.retain(Tile::is_data_function);
        if tiles.is_empty() {
            return self.tiling().empty_tile();
        }
        let Some(enclosing) = self.level.enclosing() else {
            return flat_merge(tiles, domain_extent, codomain_tiling);
        };
        // The arms are one collection's disjoint slices over the same standing levels. Each
        // is pulled through its own branch and holds the rows it has reached and not
        // released, so the standing rows are the arms' together: every arm's standing
        // levels with nothing beneath, merged by key.
        let empty_group = self.tiling().values_at(self.level).empty_tile();
        let mut standing = tiles
            .iter()
            .map(|tile| tile.per_group(self.tiling(), self.level, &mut |_| empty_group.clone()))
            .reduce(|mut all, one| {
                all.merge(one);
                all
            })
            .expect("at least one arm is a collection");
        // A standing row is complete once every arm calls it complete, since each holds its
        // own share of what lies beneath: the statements meet, as `flat_merge` meets them at
        // the level it merges. An arm released whole states `True` and constrains nothing.
        for depth in (0..self.level.index()).map(CurryLevel::new) {
            let met = tiles
                .iter()
                .filter_map(|tile| match tile.values_at(depth) {
                    Tile::DataFunction {
                        domain_predicate, ..
                    } => Some(domain_predicate),
                    _ => None,
                })
                .fold(Predicate::True, |all, one| all.intersect(one));
            if let Tile::DataFunction {
                domain_predicate, ..
            } = standing.values_at_mut(depth)
            {
                *domain_predicate = met;
            }
        }
        let rows: Vec<_> = tiles
            .iter()
            .map(|tile| tile.rows_by_path(enclosing))
            .collect();
        let paths = standing.paths_at(enclosing);
        standing.per_group(self.tiling(), self.level, &mut |row| {
            // An arm that has not reached this row contributes nothing to it. The arms are
            // disjoint slices of one collection, so a missing arm is an absence rather
            // than a gap the merge has to reconcile.
            let per_arm: Vec<Tile> = tiles
                .iter()
                .zip(&rows)
                .filter_map(|(tile, rows)| {
                    let at = *rows.get(&paths[row])?;
                    tile.group_at(self.level, at).map(|g| g.into_owned())
                })
                .collect();
            flat_merge(per_arm, domain_extent, codomain_tiling)
        })
    }
}

impl TileProducer for UnionProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, p) in self.inputs.iter().enumerate() {
            node = node.child(format!("_{i}"), p.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let tiles: Vec<Tile> = self
            .inputs
            .iter_mut()
            .map(|p| {
                // An arm the consumer has fully released contributes nothing.
                // `release_impl` below splits a per-variant guard, so one arm can be
                // universally released while its siblings are still producing — and
                // released positions must never reappear in this operator's output.
                // The arm still has to *appear* here, since the arms are
                // positional, so it contributes an empty but **decided** tile: empty
                // because its positions are released, decided because nothing more
                // will ever arrive from it (the default `empty_tile` reads as "not
                // ready", which would hold the union non-terminal forever).
                if p.obsolete_guard().is_universal() {
                    let mut released = p.tiling().empty_tile();
                    if let Tile::DataFunction {
                        domain_predicate, ..
                    } = &mut released
                    {
                        *domain_predicate = Predicate::True;
                    }
                    released
                } else {
                    p.get(p.tiling().universal_guard())
                }
            })
            .collect();

        if self.flat {
            // The merged column is described by the operator's *declared* tiling at
            // both ends: the domain the arms share, and the codomain shape the
            // decision field carries. Under a standing level the same description sits
            // `level` levels in, and the merge runs once per row of the level above.
            let mut merged_at = self.tiling();
            for _ in 0..self.level.index() {
                let Tiling::DataFunction { codomain, .. } = merged_at else {
                    panic!("a flat union has a standing level it does not tile for")
                };
                merged_at = codomain;
            }
            let (domain_extent, codomain_tiling) = match merged_at {
                Tiling::DataFunction { domain, codomain } => (domain.clone(), (**codomain).clone()),
                other => panic!("a flat union tiling is a function, got {other}"),
            };
            return self.merged(tiles, &domain_extent, &codomain_tiling);
        }

        let mut domains: Vec<ColumnValue> = Vec::new();
        let mut codomains: Vec<Tile> = Vec::new();
        let mut domain_predicates: Vec<Predicate> = Vec::new();
        let mut combined_deleted = BitSet::new();
        let mut domain_offset: usize = 0;

        for tile in tiles {
            match tile {
                Tile::DataFunction {
                    domain,
                    codomain,
                    domain_predicate: dp,
                    deleted,
                    ..
                } => {
                    // Shift each deleted index into the combined domain's position space.
                    for idx in deleted.iter() {
                        combined_deleted.insert(idx + domain_offset);
                    }
                    domain_offset += domain.len();
                    domains.push(domain);
                    codomains.push(*codomain);
                    domain_predicates.push(dp);
                }
                other => panic!("UnionProducer: expected a collection tile, got {other:?}"),
            }
        }

        // One predicate per arm, and the arms are every tag of the union's domain.
        let domain_predicate =
            Predicate::over_every_tag(TagMap::from_positional(domain_predicates));

        // Build the discriminated-union domain column. Each arm occupies a
        // contiguous run of rows, in arm order.
        let mut next_row = 0usize;
        let union_domain = ColumnValue::Union(TagMap::from_positional(
            domains
                .into_iter()
                .map(|d| {
                    let rows: Vec<usize> = (next_row..next_row + d.len()).collect();
                    next_row += d.len();
                    UnionArm::new(rows, d)
                })
                .collect(),
        ));
        union_domain.debug_assert_union_invariants();

        // The arms' values stand one after another over the concatenated keys, in arm order
        // — which is what [`Tile::merge_rows`] appends, whatever the values are. A column
        // appends; a collection appends its rows with each run shifted past the keys already
        // there, so an arm holding a collection per key keeps its own grouping.
        //
        // The arms always agree on shape, because two alternative value spaces at one
        // position can only be *tagged* — the solver won't infer an untagged sum from a
        // collision — so differing arms are both `ColumnValue::Union` and appending merges
        // their tag maps.
        let codomain_tile: Tile = {
            let mut arms = codomains.into_iter();
            let mut combined = arms.next().expect("at least one arm");
            for arm in arms {
                combined.merge_rows(arm);
            }
            combined
        };

        Tile::data_function(
            union_domain,
            Box::new(codomain_tile),
            domain_predicate,
            combined_deleted,
        )
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match obsolete_guard {
            g if g.is_empty() => {}
            g if g.is_universal() => {
                for input in &mut self.inputs {
                    input.release(input.tiling().universal_guard());
                }
            }
            // Split the per-variant predicates and forward each to the input that
            // produced that variant's data.
            TileGuard::Function(FunctionGuard::Domain(pred @ Predicate::Union { .. })) => {
                for (arm, input) in self.inputs.iter_mut().enumerate() {
                    let pred = pred
                        .under_tag(&crate::ccl::FieldKey::Index(arm))
                        .unwrap_or_else(|| unreachable!("matched as a union predicate"));
                    input.release(TileGuard::Function(FunctionGuard::Domain(pred)));
                }
            }
            // A **flat** union has one flat domain (not per-variant tags), so a released
            // region over it forwards to every arm — each arm holds a disjoint subset of
            // it and ignores the rest. That holds whatever shape the region takes: a
            // prefix of the positions, the `Codomain` half of a nested release, or the
            // `Or` of the two that `to_guard` emits for a collection of collections.
            g if self.flat => {
                for input in &mut self.inputs {
                    input.release(g.clone());
                }
            }
            other => panic!("UnionProducer::release_impl: unexpected guard {other:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::FieldKey;
    use crate::interpreter::{BaseType, ColumnValue, Extent};
    use std::cell::RefCell;
    use std::rc::Rc;

    // ── UnionProducer::release_impl ───────────────────────────────────────────

    fn int_function_tiling() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    fn int_function_tile() -> Tile {
        Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            Predicate::True,
            BitSet::new(),
        )
    }

    /// A `DataFunction` operator with a chosen tiling, for asserting on what
    /// [`UnionOperator::new`] *declares* (the tiling), independent of any data.
    struct TilingOnly(Tiling);

    impl TileOperator for TilingOnly {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.0
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            unimplemented!("tiling-only stub is never pulled")
        }
    }

    fn named_variant(arms: &[(&str, Extent)]) -> Extent {
        Extent::Union(TagMap::from_arms(
            arms.iter()
                .map(|(t, e)| (FieldKey::Name((*t).into()), e.clone()))
                .collect(),
        ))
    }

    fn function_with_codomain(codomain: Extent) -> Box<dyn TileOperator> {
        Box::new(TilingOnly(Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(codomain),
        )))
    }

    fn union_codomain(op: &UnionOperator) -> Tiling {
        let Tiling::DataFunction { codomain, .. } = op.tiling() else {
            panic!("a union of functions is a function");
        };
        (**codomain).clone()
    }

    /// **The declared codomain is used, not one derived from the arms.**
    ///
    /// The two cases that used to be told apart by whether the arms' extents had
    /// a join — differently-tagged variants merging into one tag set, and
    /// unrelated extents staying a positional sum — are now one case: whatever
    /// the node's type says. Both are exercised here at a declaration the old
    /// derivation would *not* have reached from these arms, so the test fails if
    /// anything starts re-deriving.
    #[test]
    fn codomain_of_differing_arms_is_the_declared_one() {
        // Differently-tagged variant arms, declared as the merged tag set —
        // the column the union actually builds, with the arm that did not occur
        // left empty.
        let merged = named_variant(&[
            ("neg", Extent::Base(BaseType::Int)),
            ("pos", Extent::Base(BaseType::Int)),
        ]);
        let op = UnionOperator::new(
            vec![
                function_with_codomain(named_variant(&[("pos", Extent::Base(BaseType::Int))])),
                function_with_codomain(named_variant(&[("neg", Extent::Base(BaseType::Int))])),
            ],
            merged.clone(),
        );
        assert_eq!(union_codomain(&op), Tiling::Scalar(merged));

        // Unrelated arm extents, declared as the positional sum a `++` of two
        // differently-typed collections is typed at.
        let positional = Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::String),
        ]));
        let op = UnionOperator::new(
            vec![
                function_with_codomain(Extent::Base(BaseType::Int)),
                function_with_codomain(Extent::Base(BaseType::String)),
            ],
            positional.clone(),
        );
        assert_eq!(union_codomain(&op), Tiling::Scalar(positional));

        // And a declaration *narrower* than either arm — the record-width join
        // the type layer computes and `Extent` has no rule for. The old
        // derivation answered a positional sum here, which nothing downstream
        // could project.
        let rec = |fields: &[(&str, Extent)]| {
            Extent::record(
                fields
                    .iter()
                    .map(|(n, e)| ((*n).to_string(), e.clone()))
                    .collect(),
            )
        };
        let narrow = rec(&[("a", Extent::Base(BaseType::Int))]);
        let op = UnionOperator::new(
            vec![
                function_with_codomain(rec(&[
                    ("a", Extent::Base(BaseType::Int)),
                    ("b", Extent::Base(BaseType::Int)),
                ])),
                function_with_codomain(narrow.clone()),
            ],
            narrow.clone(),
        );
        assert_eq!(union_codomain(&op), Tiling::Scalar(narrow));
    }

    /// Agreeing arms keep their shared **tiling**, which is the one thing the
    /// operands know that the declared extent does not: a `Tiling::Record` is
    /// struct-of-arrays, and an `Extent::Record` cannot say which of the two
    /// column representations is meant.
    #[test]
    fn codomain_of_agreeing_arms_keeps_their_tiling() {
        let op = UnionOperator::new(
            vec![
                function_with_codomain(Extent::Base(BaseType::Int)),
                function_with_codomain(Extent::Base(BaseType::Int)),
            ],
            Extent::Base(BaseType::Int),
        );
        assert_eq!(
            union_codomain(&op),
            Tiling::Scalar(Extent::Base(BaseType::Int))
        );
    }

    /// Differing arms merge into one *column*, which is also the only codomain
    /// shape `UnionProducer` can build. A non-`Scalar` arm is therefore rejected
    /// here rather than declared as a scalar column of functions — a tile the
    /// producer cannot emit, and which would have failed at the first `get`
    /// instead of at graph construction where the shape is known.
    #[test]
    #[should_panic(expected = "arms with differing codomains merge into one column")]
    fn differing_non_scalar_codomains_are_rejected_at_construction() {
        let nested = Box::new(TilingOnly(Tiling::data_function(
            Extent::Base(BaseType::UInt),
            int_function_tiling(),
        ))) as Box<dyn TileOperator>;
        let _ = UnionOperator::new(
            vec![function_with_codomain(Extent::Base(BaseType::Int)), nested],
            Extent::Base(BaseType::Int),
        );
    }

    // ── flat_merge: the arms' domains must partition, not overlap ─────────────

    /// A `DataFunction` arm holding `(key, value)` pairs — one slice of the
    /// fed element stream, as a tag fan-out or a first-match value-`Case` produces.
    fn flat_arm(pairs: &[(usize, i64)]) -> Tile {
        Tile::data_function(
            ColumnValue::from_uints(pairs.iter().map(|(k, _)| *k).collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(
                pairs.iter().map(|(_, v)| *v).collect(),
            ))),
            Predicate::True,
            BitSet::new(),
        )
    }

    /// The precondition holding: disjoint arms reassemble into the full column,
    /// sorted by position, whatever order the arms arrive in.
    #[test]
    fn flat_merge_reassembles_disjoint_arms_by_position() {
        let out = flat_merge(
            vec![flat_arm(&[(1, 20), (3, 40)]), flat_arm(&[(0, 10), (2, 30)])],
            &Extent::uint_range(4),
            &Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let Tile::DataFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("flat merge yields a Function");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 1, 2, 3]));
        assert_eq!(
            *codomain,
            Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))
        );
    }

    /// A fed stream whose own index set is a **coproduct** keys its rows
    /// `Union { tag, inner }`, not `UInt` — the shape a `match` over a
    /// conditional-element comprehension merges. Reassembly needs nothing new: the
    /// order on a tagged pair is lexicographic by tag then payload, so the arms
    /// interleave back into the fed order across both tags.
    #[test]
    fn flat_merge_reassembles_coproduct_keyed_arms() {
        let key = |tag: usize, inner: usize| Value::Union {
            tag: FieldKey::Index(tag),
            inner: Box::new(Value::UInt(inner)),
        };
        let arm = |pairs: Vec<(Value, i64)>| {
            Tile::data_function(
                ColumnValue::from_values(
                    pairs.iter().map(|(k, _)| k.clone()).collect(),
                    &coproduct_extent(),
                ),
                Box::new(Tile::Scalar(ColumnValue::Ints(
                    pairs.iter().map(|(_, v)| *v).collect(),
                ))),
                Predicate::True,
                BitSet::new(),
            )
        };
        // Arms arrive out of order and each straddles both tags.
        let out = flat_merge(
            vec![
                arm(vec![(key(0, 1), 20), (key(1, 0), 30)]),
                arm(vec![(key(0, 0), 10), (key(1, 1), 40)]),
            ],
            &coproduct_extent(),
            &Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let Tile::DataFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("flat merge yields a Function");
        };
        assert_eq!(
            (0..domain.len())
                .map(|i| domain.index_at(i))
                .collect::<Vec<_>>(),
            vec![key(0, 0), key(0, 1), key(1, 0), key(1, 1)],
            "tagged keys reassemble by tag then payload"
        );
        assert_eq!(
            *codomain,
            Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))
        );
    }

    /// Two `[0, 1]` halves under a positional sum — the extent a conditional-element
    /// comprehension gives its result.
    fn coproduct_extent() -> Extent {
        Extent::Union(TagMap::from_positional(vec![
            Extent::uint_range(2),
            Extent::uint_range(2),
        ]))
    }

    /// The precondition violated. Overlapping arms are a **caller** bug — a
    /// value-`Case` whose first-match gates are not actually exclusive, or a tag
    /// fan-out that lost a `variant_project` — and the merge cannot repair it:
    /// two values at one domain key violate monotonic merge however it picks.
    /// Left unchecked it is silent, since the sort just leaves the duplicates
    /// adjacent and a column one row too long flows on downstream.
    #[test]
    #[should_panic(expected = "domain key u1 is claimed by more than one arm")]
    fn flat_merge_rejects_arms_that_claim_one_position_twice() {
        let _ = flat_merge(
            vec![flat_arm(&[(0, 10), (1, 20)]), flat_arm(&[(1, 99)])],
            &Extent::uint_range(2),
            &Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
    }

    /// `release_impl` splits a per-variant guard, so one arm can be fully released
    /// while its siblings still produce. That arm must not be pulled again — the
    /// release promised never to request those positions, and re-delivering
    /// released data is exactly what a consumer that has moved on must not see.
    ///
    /// Both arms here hold data, so a pull that ignored the release would show arm
    /// 0's rows in the output. (In a debug build the central pull-after-release
    /// assertion in `TileProducer::get` catches it too.)
    #[test]
    fn a_fully_released_arm_is_not_pulled_again() {
        use crate::interpreter::tile_operators::test_helpers::TestTileProducer;

        let arm_tiling = int_function_tiling();
        let inputs: Vec<Box<dyn TileProducer>> = (0..2)
            .map(|_| {
                Box::new(TestTileProducer::new(
                    int_function_tile(),
                    arm_tiling.clone(),
                )) as Box<dyn TileProducer>
            })
            .collect();
        let union_tiling = Tiling::data_function(
            Extent::Union(TagMap::from_positional(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            ])),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let mut producer = UnionProducer {
            base: ProducerBase::new(UnionProducer::alloc_id(), &union_tiling),
            inputs,
            // Tagged, not flat-merged: the assertions below read per-arm
            // variants off a `ColumnValue::Union` domain.
            flat: false,
            level: CurryLevel::OUTERMOST,
        };

        // Release arm 0 in full, leaving arm 1 live.
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::over_every_tag(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::False,
            ])),
        )));
        let tile = producer.get(union_tiling.universal_guard());

        let Tile::DataFunction { domain, .. } = tile else {
            panic!("a union of functions is a function");
        };
        let ColumnValue::Union(arms) = domain else {
            panic!("the union domain is a discriminated union, got {domain:?}");
        };
        let variants = arms.into_values();
        assert_eq!(
            variants[0].len(),
            0,
            "the released arm contributes nothing; it was not re-pulled"
        );
        assert_eq!(
            variants[1].len(),
            2,
            "the live arm still contributes its rows"
        );
    }

    /// Build a `UnionProducer` with two spy inputs that record what guard they receive.
    ///
    /// Returns the producer plus `Rc<RefCell<Vec<TileGuard>>>` for each input.
    #[allow(clippy::type_complexity)]
    fn make_union_producer_with_spies() -> (
        UnionProducer,
        Rc<RefCell<Vec<TileGuard>>>,
        Rc<RefCell<Vec<TileGuard>>>,
    ) {
        struct SpyProducer {
            base: ProducerBase,
            tile: Tile,
            log: Rc<RefCell<Vec<TileGuard>>>,
        }

        impl TileProducer for SpyProducer {
            impl_producer_base!();
            fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
                node
            }
            fn get_impl(&mut self, _: TileGuard) -> Tile {
                self.tile.clone()
            }
            fn release_impl(&mut self, obsolete_guard: TileGuard) {
                self.log.borrow_mut().push(obsolete_guard);
            }
        }

        let log0: Rc<RefCell<Vec<TileGuard>>> = Rc::new(RefCell::new(Vec::new()));
        let log1: Rc<RefCell<Vec<TileGuard>>> = Rc::new(RefCell::new(Vec::new()));

        let union_tiling = Tiling::data_function(
            Extent::Union(TagMap::from_positional(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            ])),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );

        let producer = UnionProducer {
            level: CurryLevel::OUTERMOST,
            base: ProducerBase::new(UnionProducer::alloc_id(), &union_tiling),
            inputs: vec![
                Box::new(SpyProducer {
                    base: ProducerBase::new(0, &int_function_tiling()),
                    tile: int_function_tile(),
                    log: log0.clone(),
                }),
                Box::new(SpyProducer {
                    base: ProducerBase::new(1, &int_function_tiling()),
                    tile: int_function_tile(),
                    log: log1.clone(),
                }),
            ],
            flat: false,
        };

        (producer, log0, log1)
    }

    /// An empty guard is a no-op: no release signal reaches any input.
    #[test]
    fn union_producer_release_empty_is_noop() {
        let (mut producer, log0, log1) = make_union_producer_with_spies();
        producer.release(producer.tiling().empty_guard());
        assert!(
            log0.borrow().is_empty(),
            "input 0 should receive no release"
        );
        assert!(
            log1.borrow().is_empty(),
            "input 1 should receive no release"
        );
    }

    /// A universal guard forwards a universal guard to every input.
    #[test]
    fn union_producer_release_universal_forwards_to_all_inputs() {
        let (mut producer, log0, log1) = make_union_producer_with_spies();
        producer.release(producer.tiling().universal_guard());
        let l0 = log0.borrow();
        let l1 = log1.borrow();
        assert_eq!(l0.len(), 1, "input 0 should receive exactly one release");
        assert_eq!(l1.len(), 1, "input 1 should receive exactly one release");
        assert!(
            l0[0].is_universal(),
            "input 0 should receive a universal guard"
        );
        assert!(
            l1[0].is_universal(),
            "input 1 should receive a universal guard"
        );
    }

    /// A `Predicate::Union` guard splits per-variant predicates to the correct inputs.
    #[test]
    fn union_producer_release_union_pred_routes_to_correct_inputs() {
        let (mut producer, log0, log1) = make_union_producer_with_spies();

        let pred0 = Predicate::from_column_value(&ColumnValue::Ints(vec![1, 2]));
        let pred1 = Predicate::from_column_value(&ColumnValue::Ints(vec![3, 4]));
        let guard = TileGuard::Function(FunctionGuard::Domain(Predicate::tagged(
            TagMap::from_positional(vec![pred0.clone(), pred1.clone()]),
            false,
        )));

        producer.release(guard);

        let l0 = log0.borrow();
        let l1 = log1.borrow();
        assert_eq!(l0.len(), 1, "input 0 should receive exactly one release");
        assert_eq!(l1.len(), 1, "input 1 should receive exactly one release");
        assert_eq!(
            l0[0],
            TileGuard::Function(FunctionGuard::Domain(pred0)),
            "input 0 should receive pred0"
        );
        assert_eq!(
            l1[0],
            TileGuard::Function(FunctionGuard::Domain(pred1)),
            "input 1 should receive pred1"
        );
    }

    /// Beneath each key, a flat merge states what the arm holding that key says, not what
    /// a sibling arm says of keys it does not hold.
    #[test]
    fn flat_merge_states_beneath_each_key_what_its_own_arm_does() {
        use bit_set::BitSet;
        let uint = || Extent::Base(BaseType::UInt);
        let arm = |key: usize, inner: usize, inner_pred: Predicate, outer: Predicate| {
            Tile::data_function(
                ColumnValue::UInts(vec![key]),
                Box::new(Tile::grouped(
                    ColumnValue::UInts(vec![0]),
                    ColumnValue::UInts(vec![inner]),
                    Box::new(Tile::Scalar(ColumnValue::UInts(vec![inner]))),
                    inner_pred,
                    BitSet::new(),
                )),
                outer,
                BitSet::new(),
            )
        };
        let a = arm(0, 7, Predicate::True, Predicate::True);
        let b = arm(1, 8, Predicate::False, Predicate::False);
        let merged = flat_merge(
            vec![a, b],
            &uint(),
            &Tiling::data_function(uint(), Tiling::Scalar(uint())),
        );
        let Tile::DataFunction { codomain, .. } = &merged else {
            panic!("expected a collection")
        };
        let Tile::DataFunction {
            domain_predicate, ..
        } = &**codomain
        else {
            panic!("expected a nested collection")
        };
        assert!(
            !domain_predicate.contains_path(&[Value::UInt(1), Value::UInt(8)]),
            "arm B's row 1 is open, yet the merged inner level calls [1, 8] complete: {merged:?}"
        );
    }
}

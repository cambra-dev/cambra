use bit_set::BitSet;

use super::*;
use crate::interpreter::live_keys;
use crate::interpreter::operator_graph::value_at;
use crate::{
    ccl::TagMap,
    interpreter::{
        ColumnValue, Consumer, Extent, Projection, Scheduler, UnionArm, Value, shared_consumer,
    },
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
    /// partition inside a nested recurrence runs once per enclosing position, so its arms
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
            .map(|op| op.tiling().values_at(level).clone())
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
            // Arms whose tilings differ merge into one column at the declared codomain, so
            // each must fit in one: `Tiling::is_scalar`, a `Scalar` or a `Record` of such
            // tilings at any depth. A record that `MakeRecord` or a `Zip` builds arrives as a
            // record of tiles, and a literal list, the map an element-wise chain fuses into,
            // or a compound mutable variable's carried value as one column of records.
            // `flat_merge` and `UnionProducer::get_impl` rebuild each arm as one column,
            // keeping its own record fields. An arm holding a level, an `Aggregation` or a
            // `Store` has no column to go in, so it is rejected here, where the shape is known.
            for t in &codomains {
                assert!(
                    t.is_scalar(),
                    "UnionOperator: arms with differing codomains merge into one column, so \
                     each must be a `Scalar` or a `Record` of them at any depth; got {t}"
                );
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
        let pairs_before = pairs.len();
        let live: Vec<usize> = live_keys(&domain, &deleted).map(|(row, _)| row).collect();
        for &row in &live {
            pairs.push((domain.index_at(row), offset + row));
        }
        // An arm contributing no row is skipped rather than concatenated: it carries an
        // empty column whose kind is whatever its producer happened to build, and
        // concatenating that against a sibling's is a mismatch over nothing.
        if pairs.len() == pairs_before {
            continue;
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
        let (shared, gate) = shared_consumer(consumer);
        // The arms of a flat union are disjoint slices of one collection, pulled at the
        // projection. A tagged union keys its rows by arm, which a region of plain keys does not
        // name.
        let flat = self.flat;
        let input_producers: Vec<Box<dyn TileProducer>> = self
            .inputs
            .iter_mut()
            .map(|op| subscribe_forwarding_keeping_keys_if(flat, &mut **op, &shared, scheduler))
            .collect();
        Box::new(UnionProducer {
            base: ProducerBase::new(
                UnionProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
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
    /// needs no second merge, only [`Tile::regroup_beneath`]. At level zero there are no
    /// standing levels, and the whole tile goes to [`flat_merge`] directly.
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
            // An arm that has not reached this row holds nothing of it, but still says
            // whether more may come: complete where the arm calls the row complete, and not
            // otherwise. The arms are disjoint slices of one collection, so its keys are an
            // absence the merge takes as none, and its statement is one the merged row's
            // has to meet.
            let per_arm: Vec<Tile> = tiles
                .iter()
                .zip(&rows)
                .map(|(tile, rows)| {
                    if let Some(group) = rows
                        .get(&paths[row])
                        .and_then(|&at| tile.group_at(self.level, at))
                    {
                        return group.into_owned();
                    }
                    let mut group = empty_group.clone();
                    if let Tile::DataFunction {
                        domain_predicate, ..
                    } = &mut group
                    {
                        *domain_predicate =
                            match tile.completion_at(enclosing).contains_path(&paths[row]) {
                                true => Predicate::True,
                                false => Predicate::False,
                            };
                    }
                    group
                })
                .collect();
            flat_merge(per_arm, domain_extent, codomain_tiling)
        })
    }

    /// The arms' tiles as one tile of the union's tiling.
    fn combine(&self, tiles: Vec<Tile>) -> Tile {
        if self.flat {
            // The merged column is described by the operator's *declared* tiling at
            // both ends: the domain the arms share, and the codomain shape the
            // decision field carries. Under a standing level the same description sits
            // `level` levels in, and the merge runs once per row of the level above.
            let merged_at = self.tiling().values_at(self.level);
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
        //
        // Arms whose codomain tilings differ merge into one column at the declared codomain
        // ([`Self::new`]), so a value-shaped arm is restated in that shape first, as
        // [`flat_merge`] restates its arms: a product arm may arrive as a record of columns.
        let Tiling::DataFunction {
            codomain: codomain_tiling,
            ..
        } = self.tiling()
        else {
            panic!("a union tiling is a function, got {}", self.tiling())
        };
        let codomain_tiling = (**codomain_tiling).clone();
        let restated = |arm: Tile| {
            if arm.holds_a_level() || codomain_tiling.holds_a_level() {
                arm
            } else {
                column_value_to_tile(scalar_tile_to_column_value(arm), &codomain_tiling)
            }
        };
        let codomain_tile: Tile = {
            let mut arms = codomains.into_iter().map(restated);
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
}

impl TileProducer for UnionProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        for (i, p) in self.inputs.iter().enumerate() {
            visit(&format!("_{i}"), &**p);
        }
    }

    /// A flat union's arms are disjoint slices of one collection, so each is pulled at the
    /// projection and the merge is cut to it. A tagged union's keys carry the arm's tag, and
    /// splitting a projection per arm is not implemented: only `Everything` and `Nothing`
    /// reach it.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        assert!(
            self.flat || projection == Projection::Everything,
            "{} keys its rows by arm, which a projection over the keys cannot name: \
             {projection_guard:?}",
            self.name()
        );
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
                    p.get(projection.guard(p.tiling()))
                }
            })
            .collect();
        let mut merged = self.combine(tiles);
        merged.restrict_to(&projection, self.tiling());
        merged
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
            // produced that variant's data. Only a tagged union's domain is its arms' tags; a
            // flat union's is the one domain its arms share, which may itself be keyed by a
            // union (a loop over a concatenation), and forwards whole below.
            TileGuard::Function(FunctionGuard::Domain(pred @ Predicate::Union { .. }))
                if !self.flat =>
            {
                for (arm, input) in self.inputs.iter_mut().enumerate() {
                    let pred = pred
                        .under_tag(&crate::ccl::FieldKey::Index(arm))
                        .unwrap_or_else(|| unreachable!("matched as a union predicate"));
                    input.release(TileGuard::Function(FunctionGuard::Domain(pred)));
                }
            }
            // A **flat** union has one flat domain (not per-variant tags), so a released
            // region over it forwards to every arm — each arm holds a disjoint subset of
            // it and ignores the rest. The release names every key the consumer held,
            // including keys outside what an arm has decided, which is sound only because
            // the arms are disjoint: an arm that later delivered a key a sibling held would
            // lose it to this release, as released data. That holds whatever shape the region takes: a
            // prefix of the positions, the `Codomain` half of a nested release, or the
            // `Or` of the two that `to_guard` emits for a collection of collections.
            // The arms share the flat domain's keys and may hold their values in different
            // representations, so a release reaches each arm's values only whole.
            g if self.flat => {
                let levels = self.tiling().levels();
                for input in &mut self.inputs {
                    let guard = crate::interpreter::tiling::through_shared_levels(
                        g.clone(),
                        levels,
                        input.tiling(),
                    );
                    input.release(guard);
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
    use std::sync::Arc;
    use std::sync::Mutex;

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
                    .map(|(n, e)| ((*n).into(), e.clone()))
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

    /// Differing arms merge into one column, which is also the only codomain shape
    /// `UnionProducer` can build. An arm holding a level is rejected at construction. Declaring
    /// it a scalar column of functions would describe a tile the producer cannot emit, and the
    /// program would fail at the first `get`.
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

    /// `{a: Int, n: {c: Int, d: Int}}`, a record holding a record.
    fn nested_record() -> Extent {
        let int = || Extent::Base(BaseType::Int);
        let inner = Extent::record(HashMap::from([("c".into(), int()), ("d".into(), int())]));
        Extent::record(HashMap::from([("a".into(), int()), ("n".into(), inner)]))
    }

    /// The tiling of [`nested_record`] as a record of tiles, field by field.
    fn nested_record_of_tiles() -> Tiling {
        let int = || Tiling::Scalar(Extent::Base(BaseType::Int));
        Tiling::Record(HashMap::from([
            ("a".into(), int()),
            (
                "n".into(),
                Tiling::Record(HashMap::from([("c".into(), int()), ("d".into(), int())])),
            ),
        ]))
    }

    /// A nested record arrives as a record of tiles from `MakeRecord` or a `Zip`, and as one
    /// column of records from a literal list or a fused element-wise map. The two layouts hold
    /// the same values, so the union takes both and declares one column of records.
    #[test]
    fn arms_that_lay_out_a_nested_record_differently_merge_into_one_column() {
        let tiles = Box::new(TilingOnly(Tiling::data_function(
            Extent::Base(BaseType::UInt),
            nested_record_of_tiles(),
        ))) as Box<dyn TileOperator>;
        let op = UnionOperator::new(
            vec![function_with_codomain(nested_record()), tiles],
            nested_record(),
        );
        assert_eq!(union_codomain(&op), Tiling::Scalar(nested_record()));
    }

    /// A record holding a level at any depth has no column to go in, so an arm that is one is
    /// rejected at construction, as a bare level is.
    #[test]
    #[should_panic(expected = "arms with differing codomains merge into one column")]
    fn a_record_holding_a_level_at_any_depth_is_rejected_at_construction() {
        let int = || Tiling::Scalar(Extent::Base(BaseType::Int));
        let holding = Tiling::Record(HashMap::from([
            ("a".into(), int()),
            (
                "n".into(),
                Tiling::Record(HashMap::from([("c".into(), int_function_tiling())])),
            ),
        ]));
        let arm = Box::new(TilingOnly(Tiling::data_function(
            Extent::Base(BaseType::UInt),
            holding,
        ))) as Box<dyn TileOperator>;
        let _ = UnionOperator::new(
            vec![function_with_codomain(nested_record()), arm],
            nested_record(),
        );
    }

    /// The values of the two layouts merge into one column of records, in key order.
    #[test]
    fn flat_merge_restates_a_nested_record_of_tiles_as_a_column() {
        let ints = |v: &[i64]| ColumnValue::Ints(v.to_vec());
        let column = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Records(HashMap::from([
                ("a".into(), ints(&[1])),
                (
                    "n".into(),
                    ColumnValue::Records(HashMap::from([
                        ("c".into(), ints(&[2])),
                        ("d".into(), ints(&[3])),
                    ])),
                ),
            ])))),
            Predicate::True,
            BitSet::new(),
        );
        let tiles = Tile::data_function(
            ColumnValue::from_uints(vec![1]),
            Box::new(Tile::record(HashMap::from([
                ("a".into(), Tile::Scalar(ints(&[4]))),
                (
                    "n".into(),
                    Tile::record(HashMap::from([
                        ("c".into(), Tile::Scalar(ints(&[5]))),
                        ("d".into(), Tile::Scalar(ints(&[6]))),
                    ])),
                ),
            ]))),
            Predicate::True,
            BitSet::new(),
        );
        let out = flat_merge(
            vec![tiles, column],
            &Extent::uint_range(2),
            &Tiling::Scalar(nested_record()),
        );
        let Tile::DataFunction { codomain, .. } = out else {
            panic!("flat merge yields a Function");
        };
        let want = ColumnValue::Records(HashMap::from([
            ("a".into(), ints(&[1, 4])),
            (
                "n".into(),
                ColumnValue::Records(HashMap::from([
                    ("c".into(), ints(&[2, 5])),
                    ("d".into(), ints(&[3, 6])),
                ])),
            ),
        ]));
        assert_eq!(*codomain, Tile::Scalar(want));
    }

    // ── flat_merge: the arms' domains must partition, not overlap ─────────────

    /// A `DataFunction` arm holding `(key, value)` pairs — one slice of the
    /// fed element stream, as a tag fan-out or a first-match value-`Case` produces.
    fn flat_arm(pairs: &[(u64, i64)]) -> Tile {
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
        let key = |tag: usize, inner: u64| Value::Union {
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
            base: ProducerBase::unowned(UnionProducer::alloc_id(), &union_tiling),
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
    /// Returns the producer plus `Arc<Mutex<Vec<TileGuard>>>` for each input.
    #[allow(clippy::type_complexity)]
    fn make_union_producer_with_spies() -> (
        UnionProducer,
        Arc<Mutex<Vec<TileGuard>>>,
        Arc<Mutex<Vec<TileGuard>>>,
    ) {
        struct SpyProducer {
            base: ProducerBase,
            tile: Tile,
            log: Arc<Mutex<Vec<TileGuard>>>,
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
                self.log.lock_now().push(obsolete_guard);
            }
        }

        let log0: Arc<Mutex<Vec<TileGuard>>> = Arc::new(Mutex::new(Vec::new()));
        let log1: Arc<Mutex<Vec<TileGuard>>> = Arc::new(Mutex::new(Vec::new()));

        let union_tiling = Tiling::data_function(
            Extent::Union(TagMap::from_positional(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            ])),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );

        let producer = UnionProducer {
            level: CurryLevel::OUTERMOST,
            base: ProducerBase::unowned(UnionProducer::alloc_id(), &union_tiling),
            inputs: vec![
                Box::new(SpyProducer {
                    base: ProducerBase::unowned(0, &int_function_tiling()),
                    tile: int_function_tile(),
                    log: log0.clone(),
                }),
                Box::new(SpyProducer {
                    base: ProducerBase::unowned(1, &int_function_tiling()),
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
            log0.lock_now().is_empty(),
            "input 0 should receive no release"
        );
        assert!(
            log1.lock_now().is_empty(),
            "input 1 should receive no release"
        );
    }

    /// A universal guard forwards a universal guard to every input.
    #[test]
    fn union_producer_release_universal_forwards_to_all_inputs() {
        let (mut producer, log0, log1) = make_union_producer_with_spies();
        producer.release(producer.tiling().universal_guard());
        let l0 = log0.lock_now();
        let l1 = log1.lock_now();
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

        let l0 = log0.lock_now();
        let l1 = log1.lock_now();
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
        let arm = |key: u64, inner: u64, inner_pred: Predicate, outer: Predicate| {
            Tile::data_function(
                ColumnValue::UInts(vec![key]),
                Box::new(Tile::grouped(
                    vec![0],
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

    /// Beneath a standing level, a row one arm has not reached stays open: that arm may
    /// still deliver keys under it, whatever the arm that holds the row says.
    #[test]
    fn a_flat_union_keeps_a_row_open_that_one_arm_has_not_reached() {
        use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
        let uint = || Extent::Base(BaseType::UInt);
        let tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::Scalar(Extent::Base(BaseType::Int))),
        );
        // Arm 0 holds row 0 whole (key 0 under it) and calls every row complete.
        let arm0 = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        // Arm 1 has reached no row yet and calls nothing complete.
        let arm1 = tiling.empty_tile();
        let mut producer = UnionProducer {
            base: ProducerBase::unowned(UnionProducer::alloc_id(), &tiling),
            level: CurryLevel::new(1),
            inputs: vec![
                Box::new(TestTileProducer::new(arm0, tiling.clone())),
                Box::new(TestTileProducer::new(arm1, tiling.clone())),
            ],
            flat: true,
        };
        let out = producer.get(tiling.universal_guard());
        let Tile::DataFunction {
            domain_predicate: rows,
            codomain,
            ..
        } = &out
        else {
            panic!("a flat union tiles as a collection, got {out:?}")
        };
        assert!(
            !rows.contains(&Value::UInt(0)),
            "row 0 is open while arm 1 has not reached it: {rows:?}"
        );
        let Tile::DataFunction {
            domain_predicate: keys,
            ..
        } = codomain.as_ref()
        else {
            panic!("the merged level is a collection, got {codomain:?}")
        };
        assert!(
            !keys.contains_path(&[Value::UInt(0), Value::UInt(5)]),
            "arm 1 may still deliver key 5 under row 0, so (0, 5) is not complete: {keys:?}"
        );
    }
}

#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, ScriptedOp, ScriptedProducer, assert_conforms, int_column,
        int_entries, keys_between,
    };
    use crate::interpreter::{BaseType, ColumnValue, Extent};

    const ROWS: u64 = 8;

    fn stream_tiling() -> Tiling {
        Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    /// One arm of a split stream: the rows `keys` of `0..ROWS`, stated complete.
    fn arm(
        keys: impl Iterator<Item = u64>,
        value: impl Fn(u64) -> i64,
    ) -> (ProjectionSpy, GuardLog) {
        let keys: Vec<u64> = keys.collect();
        let values = keys.iter().map(|&key| value(key)).collect();
        let tile = Tile::data_function(
            ColumnValue::from_uints(keys),
            Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            Predicate::True,
            BitSet::new(),
        );
        let (spy, pulled, _) = ProjectionSpy::new(tile, stream_tiling());
        (spy, pulled)
    }

    /// What a collection tile states complete.
    fn stated(tile: &Tile) -> Predicate {
        let Tile::DataFunction {
            domain_predicate, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}")
        };
        domain_predicate.clone()
    }

    /// `[if even(x) then x * 10 else x for x in xs]`: a case splits a stream into an arm per
    /// branch, and the branches merge back into one flat stream.
    fn merged_branches(flat: bool) -> (UnionProducer, GuardLog, GuardLog) {
        let (even, even_pulled) = arm((0..ROWS).filter(|k| k % 2 == 0), |k| k as i64 * 10);
        let (odd, odd_pulled) = arm((0..ROWS).filter(|k| k % 2 == 1), |k| k as i64);
        let producer = UnionProducer {
            base: ProducerBase::unowned(UnionProducer::alloc_id(), &stream_tiling()),
            level: CurryLevel::OUTERMOST,
            inputs: vec![Box::new(even), Box::new(odd)],
            flat,
        };
        (producer, even_pulled, odd_pulled)
    }

    /// A morsel of the merged stream pulls every branch at that morsel and answers the
    /// morsel's rows in key order, each from the branch that produced it.
    #[test]
    fn a_morsel_of_merged_branches_pulls_each_branch_at_the_morsel() {
        let (mut union, even_pulled, odd_pulled) = merged_branches(true);
        let morsel = union.get(keys_between(2, 5));
        assert_eq!(int_entries(&morsel), vec![(2, 20), (3, 3), (4, 40), (5, 5)]);
        assert_eq!(*even_pulled.lock_now(), vec![keys_between(2, 5)]);
        assert_eq!(*odd_pulled.lock_now(), vec![keys_between(2, 5)]);
    }

    /// The consumer releases a morsel before taking the next, and the branches are released
    /// with it, so the next morsel is pulled at its own rows.
    #[test]
    fn successive_morsels_of_merged_branches_are_disjoint() {
        let (mut union, even_pulled, _) = merged_branches(true);
        union.get(keys_between(0, 3));
        union.release(keys_between(0, 3));
        let next = union.get(keys_between(4, 7));
        assert_eq!(int_entries(&next), vec![(4, 40), (5, 5), (6, 60), (7, 7)]);
        assert_eq!(even_pulled.lock_now()[1], keys_between(4, 7));
    }

    #[test]
    fn the_morsels_together_are_the_whole_pull() {
        for guard in [keys_between(0, 3), keys_between(2, 5), keys_between(5, 5)] {
            assert_conforms(|| Box::new(merged_branches(true).0), guard);
        }
    }

    /// A released arm contributes an empty tile that states every key decided. Once every arm is
    /// released, a morsel is the empty merge and states completeness over the morsel only.
    #[test]
    fn a_morsel_after_every_arm_is_released_states_completeness_over_the_morsel() {
        let (mut union, _, _) = merged_branches(true);
        union.get(keys_between(0, 3));
        union.release(stream_tiling().universal_guard());
        let next = union.get(keys_between(4, 7));
        let Tile::DataFunction {
            domain_predicate, ..
        } = &next
        else {
            panic!("a collection, got {next:?}")
        };
        let TileGuard::Function(FunctionGuard::Domain(asked)) = keys_between(4, 7) else {
            unreachable!("keys_between names a key region")
        };
        assert_eq!(*domain_predicate, asked);
    }

    /// One pull of `0..=7` while the odd arm has decided only `0..=3`. The merge answers what
    /// both arms hold and states completeness for `0..=3` alone, so the consumer can tell that
    /// `4..=7` is still open. The odd arm then grows over the rest, and the same ask answers the
    /// whole range: the rows the arm held back appear in the second answer.
    #[test]
    fn an_arm_that_grows_after_the_ask_is_merged_on_the_next_pull() {
        let TileGuard::Function(FunctionGuard::Domain(through_3)) = keys_between(0, 3) else {
            unreachable!("keys_between names a key region")
        };
        let (even, _) = ScriptedProducer::new(
            int_column(vec![0, 2, 4, 6], Predicate::True),
            stream_tiling(),
        );
        let (odd, odd_cell) =
            ScriptedProducer::new(int_column(vec![1, 3], through_3.clone()), stream_tiling());
        let mut union = UnionProducer {
            base: ProducerBase::unowned(UnionProducer::alloc_id(), &stream_tiling()),
            level: CurryLevel::OUTERMOST,
            inputs: vec![Box::new(even), Box::new(odd)],
            flat: true,
        };

        let first = union.get(keys_between(0, 7));
        assert_eq!(
            int_entries(&first),
            vec![(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6)]
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = &first
        else {
            panic!("a collection, got {first:?}")
        };
        assert_eq!(
            *domain_predicate, through_3,
            "only the odd arm's decided prefix is complete"
        );

        *odd_cell.lock_now() = int_column(vec![1, 3, 5, 7], Predicate::True);
        let second = union.get(keys_between(0, 7));
        assert_eq!(
            int_entries(&second),
            (0..8).map(|k| (k, k as i64)).collect::<Vec<_>>()
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = &second
        else {
            panic!("a collection, got {second:?}")
        };
        let TileGuard::Function(FunctionGuard::Domain(asked)) = keys_between(0, 7) else {
            unreachable!("keys_between names a key region")
        };
        assert_eq!(
            *domain_predicate, asked,
            "every arm has now decided the whole ask"
        );
    }

    /// A consumer that takes the merged stream more than once, releasing what it holds each
    /// time, sees every row once: a row it released does not come back from either arm, however
    /// often the union is pulled while an arm is still delivering.
    #[test]
    fn a_union_pulled_repeatedly_delivers_each_row_once() {
        let TileGuard::Function(FunctionGuard::Domain(through_3)) = keys_between(0, 3) else {
            unreachable!("keys_between names a key region")
        };
        let (mut union, odd_cell) = scripted_union(int_column(vec![1, 3], through_3.clone()));

        let first = union.get(keys_between(0, ROWS - 1));
        assert_eq!(
            int_entries(&first),
            vec![(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6)]
        );
        union.release(first.to_guard());

        // Nothing new has arrived, so nothing comes back, and the statement is still the odd
        // arm's decided prefix.
        let idle = union.get(keys_between(0, ROWS - 1));
        assert!(int_entries(&idle).is_empty());
        assert_eq!(stated(&idle), through_3);

        // The odd arm delivers some of what is left without finishing: row 5 arrives, the
        // range stays open, and row 5 is the only row delivered.
        *odd_cell.lock_now() = int_column(vec![1, 3, 5], Predicate::exactly(&[Value::UInt(5)]));
        let partial = union.get(keys_between(0, ROWS - 1));
        assert_eq!(int_entries(&partial), vec![(5, 5)]);
        union.release(partial.to_guard());

        *odd_cell.lock_now() = int_column(vec![1, 3, 5, 7], Predicate::True);
        let last = union.get(keys_between(0, ROWS - 1));
        assert_eq!(int_entries(&last), vec![(7, 7)]);
        let TileGuard::Function(FunctionGuard::Domain(asked)) = keys_between(0, ROWS - 1) else {
            unreachable!("keys_between names a key region")
        };
        assert_eq!(stated(&last), asked, "both arms have decided the whole ask");
    }

    /// A flat union over two scripted arms, subscribed at the universal guard. The even arm
    /// holds `[0, 2, 4, 6]` and the odd arm `odd`, each with its own statement.
    fn scripted_union(odd: Tile) -> (Box<dyn TileProducer>, Arc<Mutex<Tile>>) {
        let (even, _) = ScriptedOp::new(
            int_column(vec![0, 2, 4, 6], Predicate::True),
            stream_tiling(),
        );
        let (odd, odd_cell) = ScriptedOp::new(odd, stream_tiling());
        let mut operator = UnionOperator::new_flat(
            vec![Box::new(even), Box::new(odd)],
            Extent::Base(BaseType::Int),
        );
        let union = operator.subscribe(
            operator.tiling().universal_guard(),
            Box::new(|| {}),
            &mut Scheduler::new(),
        );
        (union, odd_cell)
    }

    /// Two arms that hold one key in the same pull are not disjoint. The merge rejects them
    /// when the union is pulled at a projection, as `flat_merge_rejects_overlapping_arms` does
    /// for the merge alone.
    #[test]
    #[should_panic(expected = "claimed by more than one arm")]
    fn arms_that_deliver_one_key_in_the_same_pull_are_rejected() {
        let (mut union, _) = scripted_union(int_column(vec![1, 3, 6], Predicate::True));
        union.get(keys_between(0, ROWS - 1));
    }

    /// An arm that delivers a key a sibling delivered earlier, after the consumer released it,
    /// loses the row without an error. The union forwards the consumer's release to every arm,
    /// so the key is already released from the arm when the arm holds it. The arm's answer
    /// drops the key before the merge compares keys, and only the sibling's value reached the
    /// consumer. Disjoint arms never reach this. The test records what overlapping arms do and
    /// is not a contract: a union that rejects the overlap replaces it.
    #[test]
    fn a_key_a_sibling_already_delivered_is_dropped_from_the_arm_after_release() {
        let (mut union, odd_cell) = scripted_union(int_column(vec![1, 3], Predicate::True));
        let first = union.get(keys_between(0, ROWS - 1));
        assert_eq!(
            int_entries(&first),
            vec![(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6)]
        );
        union.release(first.to_guard());

        // The odd arm now holds key 6 with a value of its own, which the even arm delivered
        // as 6 in the first pull.
        let mut tile = int_column(vec![1, 3, 6], Predicate::True);
        if let Tile::DataFunction { codomain, .. } = &mut tile {
            **codomain = Tile::Scalar(ColumnValue::Ints(vec![1, 3, 600]));
        }
        *odd_cell.lock_now() = tile;
        let second = union.get(keys_between(0, ROWS - 1));
        assert!(
            int_entries(&second).is_empty(),
            "neither the odd arm's 6 nor anything released comes back"
        );
    }

    #[test]
    fn merged_branches_asked_for_nothing_pull_nothing() {
        let (mut union, even_pulled, odd_pulled) = merged_branches(true);
        let tile = union.get(stream_tiling().empty_guard());
        assert!(int_entries(&tile).is_empty());
        assert!(even_pulled.lock_now().is_empty() && odd_pulled.lock_now().is_empty());
    }

    /// A tagged union keys its rows by arm, which a projection over plain keys does not
    /// name, so a morsel pull fails rather than answering a different region.
    #[test]
    #[should_panic(expected = "keys its rows by arm")]
    fn a_tagged_union_rejects_a_key_projection() {
        let (mut union, _, _) = merged_branches(false);
        union.get(keys_between(0, 3));
    }
}

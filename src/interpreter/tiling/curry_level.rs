//! Which curried domain of a tiling an operator acts at.

use crate::interpreter::{FunctionGuard, TileGuard, Tiling};

/// Which curried domain of a tiling an operator acts at, counted from the outside.
///
/// A collection tiling is a curried data function `K₀ ⤇ K₁ ⤇ … ⤇ V` — one `⤇` per
/// level, which a tile stores Compressed-Sparse-Row-wise as one [`Tile::DataFunction`] per
/// level. `CurryLevel(0)` is `K₀` and `CurryLevel(n)` is `Kₙ`, grouped by the `n` levels
/// above it; `CurryLevel(levels)` is the values every level stands over, which is the
/// level an operator that replaces a codomain acts at. An operator acts at one level and
/// leaves the rest standing.
///
/// **A level index, not a count of the levels above.** The two are the same number. A site
/// that re-derives `levels() − k` for its own `k` reads a level its operator was not built
/// with, so the level is stated once, at construction, and read back from there. See
/// `src/interpreter/design-operators.md`, "Curry levels".
///
/// [`Tile::DataFunction`]: crate::interpreter::Tile::DataFunction
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CurryLevel(usize);

impl CurryLevel {
    /// The outermost level of any collection — the one a single implicit row groups.
    pub const OUTERMOST: CurryLevel = CurryLevel(0);

    /// The level `n` levels in.
    pub fn new(n: usize) -> Self {
        CurryLevel(n)
    }

    /// The innermost collection level of `tiling` — its last level. `None` where `tiling`
    /// is not a collection.
    pub fn innermost_of(tiling: &Tiling) -> Option<Self> {
        tiling.levels().checked_sub(1).map(CurryLevel)
    }

    /// The level holding what every level of `tiling` stands over: one past its innermost.
    /// An operator that replaces a codomain rather than a collection level acts here.
    pub fn values_of(tiling: &Tiling) -> Self {
        CurryLevel(tiling.levels())
    }

    /// The level that groups this one — where its rows, and which of them are complete,
    /// are stated. `None` at [`OUTERMOST`](Self::OUTERMOST), which one implicit row groups.
    pub fn enclosing(self) -> Option<Self> {
        self.0.checked_sub(1).map(CurryLevel)
    }

    /// This level counted from a **codomain** rather than from the whole tile, which is the
    /// rebase a recursive accessor takes when it steps one level in.
    ///
    /// The same arithmetic as [`enclosing`](Self::enclosing) and a different level: that
    /// one names the level above this, where this names *this* level from inside. Panics
    /// at [`OUTERMOST`](Self::OUTERMOST), which is the accessors' base case and so never
    /// stepped past.
    pub fn in_codomain(self) -> Self {
        CurryLevel(
            self.0
                .checked_sub(1)
                .expect("the outermost level is the accessors' base case"),
        )
    }

    /// The raw index, for the accessors that address a level positionally.
    pub fn index(self) -> usize {
        self.0
    }

    /// `inner` read at this level rather than at the outermost one: a
    /// [`FunctionGuard::Codomain`] per level standing above it, since a codomain guard is
    /// read against every row of the values it wraps.
    pub fn wrap_guard(self, inner: TileGuard) -> TileGuard {
        (0..self.0).fold(inner, |g, _| {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(g)))
        })
    }
}

impl std::fmt::Display for CurryLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "level {}", self.0)
    }
}

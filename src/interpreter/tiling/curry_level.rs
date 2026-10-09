//! Which curried domain of a tiling an operator acts at.

use crate::interpreter::{FunctionGuard, TileGuard, Tiling};

/// Zero-based collection level, counted from the outermost domain.
/// For `K₀ ⤇ … ⤇ Kₙ ⤇ V`, indices `0..=n` address collection levels and `n + 1`
/// addresses `V`. Operators retain the level selected at construction rather than
/// deriving it again from each input's depth.
/// See `src/interpreter/design-operators.md`, "Curry levels".
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

    /// Rebase this level after an accessor descends into a codomain.
    /// Unlike [`enclosing`](Self::enclosing), this still addresses the same collection.
    /// Panics at [`OUTERMOST`](Self::OUTERMOST), the accessors' base case.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{BaseType, Extent};

    /// The innermost level is the last one, at any depth; a tiling that is not a collection
    /// has none.
    #[test]
    fn innermost_of_is_the_last_collection_level() {
        let int = || Extent::Base(BaseType::Int);
        let one = Tiling::data_function(int(), Tiling::Scalar(int()));
        let three = Tiling::data_function(int(), Tiling::data_function(int(), one.clone()));
        assert_eq!(CurryLevel::innermost_of(&Tiling::Scalar(int())), None);
        assert_eq!(CurryLevel::innermost_of(&one), Some(CurryLevel::OUTERMOST));
        assert_eq!(CurryLevel::innermost_of(&three), Some(CurryLevel::new(2)));
    }
}

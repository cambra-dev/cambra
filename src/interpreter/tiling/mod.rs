//! Core tiling types: [`Tiling`], [`Tile`], [`TileGuard`], [`FunctionGuard`], [`Predicate`].
//!
//! These types describe the shape, data, and region-tracking for the tile-based
//! dataflow evaluation model.

use std::{collections::HashMap, hash::Hash};

mod guard;
mod predicate;
mod tile;
mod tiling_kind;

pub use guard::*;
pub use predicate::*;
pub use tile::*;
pub use tiling_kind::*;

/// Apply `f` to every value in a `HashMap`, producing a new map with the same keys.
pub(crate) fn transform_hashmap_values<K: Clone + Eq + Hash, InputV, V, F: Fn(&InputV) -> V>(
    source: &HashMap<K, InputV>,
    f: F,
) -> HashMap<K, V> {
    source.iter().map(|(k, v)| (k.clone(), f(v))).collect()
}

#[cfg(test)]
pub(super) mod tests {
    use crate::ccl::BaseType;
    use crate::interpreter::{Extent, Tiling};

    // ── helpers ───────────────────────────────────────────────────────────────

    pub(crate) fn int() -> Extent {
        Extent::Base(BaseType::Int)
    }

    pub(crate) fn bool_ext() -> Extent {
        Extent::Base(BaseType::Bool)
    }

    pub(crate) fn range(end: usize) -> Extent {
        Extent::uint_range(end)
    }

    /// A one-level function tiling over a scalar codomain.
    pub(crate) fn scalar_function(domain: Extent, codomain: Extent) -> Tiling {
        Tiling::function(domain, Tiling::Scalar(codomain))
    }

    /// A two-level tiling, the shape most callers want.
    pub(crate) fn two_level(outer: Extent, inner: Extent, codomain: Extent) -> Tiling {
        Tiling::function(outer, Tiling::function(inner, Tiling::Scalar(codomain)))
    }

    pub(crate) fn record_tiling(fields: &[(&str, Tiling)]) -> Tiling {
        Tiling::Record(
            fields
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect(),
        )
    }
}

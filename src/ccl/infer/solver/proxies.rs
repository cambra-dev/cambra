//! Where a deeper solver variable stands at a shallower level: its proxy, one per original,
//! level and direction while the scope that minted it is live.
//!
//! During emission a scope at a level is a `let`'s right-hand side, and it closes when the
//! right-hand side ends and its variables are generalized at the binding. A proxy minted inside
//! it is that scope's: a later scope at the same level is another scope, and the proxy must not
//! stand in for its original there. After emission every such scope has closed, and each walk
//! of the graph is a scope of its own: a specialization's pin relates its clone to its use, and a
//! proxy one pin related must not carry what it holds into another's. Each level counts the
//! scopes that have closed at it, and a proxy is reused only within the count it was minted at.

use super::held::{Held, HeldKey};
use crate::ccl::Level;
use std::collections::HashMap;

/// The proxies a run has minted, and the scope each was minted in.
#[derive(Default)]
pub(crate) struct Proxies {
    /// Each original's proxy at a level in a direction: the proxy, the generation of the scope at
    /// that level it was minted in, and whether it has been related in that direction.
    by_original: HashMap<(HeldKey, Level, bool), (Held, u64, bool)>,
    /// How many scopes have closed at each level.
    generations: Vec<u64>,
    /// Whether emission has ended, after which each walk is a scope of its own.
    emitted: bool,
}

impl Proxies {
    /// The scope now open at `level`, by how many have closed there.
    fn generation(&self, level: Level) -> u64 {
        self.generations.get(level as usize).copied().unwrap_or(0)
    }

    /// Close the scopes at `level` and every deeper level: what is minted there from now on is
    /// a later scope's.
    pub(crate) fn close_from(&mut self, level: Level) {
        let level = level as usize;
        if self.generations.len() <= level {
            self.generations.resize(level + 1, 0);
        }
        for g in &mut self.generations[level..] {
            *g += 1;
        }
    }

    /// Emission has ended: from now on each walk is a scope of its own ([`Self::walk`]).
    pub(crate) fn finish_emission(&mut self) {
        self.emitted = true;
        self.close_from(0);
    }

    /// A walk of the graph begins: after emission, it is a scope of its own at every level.
    pub(crate) fn walk(&mut self) {
        if self.emitted {
            self.close_from(0);
        }
    }

    /// The proxy of `original` at `level` in `direction`, minted in the scope now open there.
    pub(crate) fn get(&self, original: HeldKey, level: Level, direction: bool) -> Option<&Held> {
        let (proxy, generation, _) = self.by_original.get(&(original, level, direction))?;
        (*generation == self.generation(level)).then_some(proxy)
    }

    /// Whether `proxy` stands for `original` at `level` and is related to it in `direction`, in
    /// the scope now open there.
    pub(crate) fn linked(
        &self,
        original: HeldKey,
        level: Level,
        direction: bool,
        proxy: &HeldKey,
    ) -> bool {
        self.by_original
            .get(&(original, level, direction))
            .is_some_and(|(p, generation, linked)| {
                *linked && *generation == self.generation(level) && p.key() == *proxy
            })
    }

    /// Record `proxy` as `original`'s at `level` in `direction`, in the scope now open there, not
    /// yet related in that direction.
    pub(crate) fn insert(&mut self, original: HeldKey, level: Level, direction: bool, proxy: Held) {
        let generation = self.generation(level);
        self.by_original
            .insert((original, level, direction), (proxy, generation, false));
    }

    /// Record that the proxy of `original` at `level` in `direction` is related to it.
    pub(crate) fn mark_linked(&mut self, original: HeldKey, level: Level, direction: bool) {
        if let Some(entry) = self.by_original.get_mut(&(original, level, direction)) {
            entry.2 = true;
        }
    }
}

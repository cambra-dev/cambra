//! Sites: which place in the program a feed or a call is, in terms two versions of the program
//! agree on (`src/ccl/design/sites.md`).
//!
//! A [`Site`] is the [`Place`] something is written at and the places of the calls that
//! reached it, under the run whose evaluation started them. Lowering looks each feed's and each
//! named call's place up ([`places`]), linking puts each run's copy of a module under that run's
//! path, and inlining extends a copied body's sites with the call that copied it. Every other
//! pass carries a site with the node it rides, a clone included.

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use chl_parser::ast::{Span, Spanned, Stmt};
pub use chl_parser::places::{Place, PlaceKind};
use chl_parser::places::{places, site_tag};
use smol_str::SmolStr;

use crate::ccl::{FieldKey, RunPath, Type};

/// A place, the calls that reached it, outermost first, and the run whose evaluation began
/// with the first of them.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Site {
    pub run: RunPath,
    pub calls: Arc<[Place]>,
    pub place: Place,
}

impl Site {
    /// The site of `place`, reached by no call, in the root.
    pub fn written(place: Place) -> Rc<Site> {
        Rc::new(Site {
            run: RunPath::default(),
            calls: Arc::from([]),
            place,
        })
    }

    /// This site reached through `call`: `call`'s run, its calls and its own place, then this
    /// site's calls.
    pub fn through(&self, call: &Site) -> Rc<Site> {
        let calls: Vec<Place> = call
            .calls
            .iter()
            .cloned()
            .chain(std::iter::once(call.place.clone()))
            .chain(self.calls.iter().cloned())
            .collect();
        Rc::new(Site {
            run: call.run.clone(),
            calls: calls.into(),
            place: self.place.clone(),
        })
    }

    /// This site in the run at `run`, which a run's copy of its module evaluates.
    pub fn in_run(&self, run: &RunPath) -> Rc<Site> {
        Rc::new(Site {
            run: run.clone(),
            calls: self.calls.clone(),
            place: self.place.clone(),
        })
    }

    /// The tag a channel's arm for this site carries ([`site_tag`]).
    pub fn tag(&self) -> String {
        site_tag(&self.run.to_string(), self.calls.iter(), &self.place)
    }
}

impl fmt::Display for Site {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.tag())
    }
}

/// Lowering's view of each module's places ([`places`]), by span.
#[derive(Debug, Default)]
pub struct Naming {
    places: HashMap<Span, Place>,
}

impl Naming {
    /// Name the places of the module at `module`, empty for the root, whose body is `body`.
    pub fn add_module(&mut self, module: &[SmolStr], body: &[Spanned<Stmt>]) {
        self.places.extend(places(module, body));
    }

    /// The site of the place at `at`: a feed's target, a `yield`, or a named call's callee.
    ///
    /// # Panics
    /// When `at` is no place's span, which would leave the feed or call without the identity a
    /// channel's tag and an inlined copy's sites are built from.
    pub fn site(&self, at: Span) -> Rc<Site> {
        let place = self
            .places
            .get(&at)
            .unwrap_or_else(|| panic!("no feed or named call is written at {at:?}"));
        Site::written(place.clone())
    }
}

/// The site of the `index`th place of `kind` spelled `spelling` in the root, outside every
/// binding: what a test builds a node's site from.
#[cfg(test)]
pub(crate) fn root_site(kind: PlaceKind, spelling: &str, index: u32) -> Rc<Site> {
    Site::written(Place {
        module: Arc::from([]),
        bindings: Arc::from([]),
        kind,
        spelling: SmolStr::new(spelling),
        index,
    })
}

/// The tags a copairing's recorded type `ty` gives its `n` operands, when it is a channel's:
/// the arms of the variant its domain is, which are sites' tags (`FieldKey::Name`). A `++`'s arms
/// are its operands' positions (`FieldKey::Index`), which a pass that flattens one `++` into
/// another renumbers, so it answers `None` for them, as for a type that records no variant.
///
/// # Panics
/// When the variant tags a channel's sites but has other than `n` arms: a pass spliced a
/// channel's copairing into another or dropped one of its operands, and the arms would no longer
/// say which site fed which.
pub fn channel_tags(ty: &Type, n: usize) -> Option<Vec<FieldKey>> {
    let domain = ty.domain()?;
    let Type::Variant(arms, _) = domain.peel_refinements() else {
        return None;
    };
    if arms
        .iter()
        .all(|(key, _)| matches!(key, FieldKey::Index(_)))
    {
        return None;
    }
    assert_eq!(
        arms.len(),
        n,
        "a channel's copairing has {n} operands for the {} sites its type tags: {ty}",
        arms.len()
    );
    Some(arms.iter().map(|(key, _)| key.clone()).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BaseType, Label};

    fn copair(keys: &[FieldKey]) -> Type {
        let arms = keys
            .iter()
            .map(|key| (key.clone(), Type::UIntRange(0)))
            .collect();
        Type::data_fun(Type::variant(arms), Type::Base(BaseType::Int))
    }

    fn site(tag: &str) -> FieldKey {
        FieldKey::Name(Label::new(tag))
    }

    #[test]
    fn a_channel_keeps_its_sites_tags() {
        let tags = [site("f()/f.out<<"), site("out<<")];
        assert_eq!(channel_tags(&copair(&tags), 2), Some(tags.to_vec()));
    }

    #[test]
    fn positions_and_unrecorded_types_record_no_tags() {
        let positions = copair(&[FieldKey::Index(0), FieldKey::Index(1)]);
        assert_eq!(channel_tags(&positions, 3), None);
        assert_eq!(channel_tags(&Type::Base(BaseType::Int), 2), None);
    }

    #[test]
    #[should_panic(expected = "3 operands for the 2 sites")]
    fn a_channel_of_another_arity_panics() {
        channel_tags(&copair(&[site("out<<"), site("out<<#1")]), 3);
    }
}

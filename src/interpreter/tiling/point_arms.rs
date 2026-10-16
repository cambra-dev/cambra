//! The arms of an [`Or`](Predicate::Or) that each admit exactly one record, read as a finite set
//! of keys.
//!
//! A column of records arrives as one point per row ([`Predicate::from_column_value`]), and the
//! operations that combine two such sets, [`Predicate::flatten_or`], [`Predicate::intersect`] and
//! [`Predicate::minus`], compare every arm with every arm. Points are equal or disjoint, so over
//! a set of points the same answers come from hashing each point once.

use std::collections::HashSet;

use intervalsets::Bounding;
use smol_str::SmolStr;

use super::Predicate;
use crate::interpreter::Value;

/// A list of arms that are each a record whose fields each admit exactly one value, over one set
/// of field names. `rows[i]` holds the values of arm `i` in field-name order.
pub(super) struct PointArms<'a> {
    names: Vec<&'a SmolStr>,
    rows: Vec<Vec<&'a Value>>,
}

impl<'a> PointArms<'a> {
    /// `arms` as points, or `None` unless every arm is a record of points over the field names of
    /// the first.
    pub(super) fn of(arms: &'a [Predicate]) -> Option<Self> {
        let mut names: Vec<&SmolStr> = Vec::new();
        let mut rows = Vec::with_capacity(arms.len());
        for (at, arm) in arms.iter().enumerate() {
            let Predicate::Record(fields) = arm else {
                return None;
            };
            let mut fields: Vec<(&SmolStr, &Predicate)> = fields.iter().collect();
            fields.sort_unstable_by(|a, b| a.0.cmp(b.0));
            if at == 0 {
                names = fields.iter().map(|(name, _)| *name).collect();
            } else if fields.len() != names.len()
                || fields
                    .iter()
                    .zip(&names)
                    .any(|((name, _), first)| name != first)
            {
                return None;
            }
            rows.push(
                fields
                    .iter()
                    .map(|(_, field)| single_value(field))
                    .collect::<Option<Vec<&Value>>>()?,
            );
        }
        (!names.is_empty()).then_some(PointArms { names, rows })
    }

    /// Whether no two arms are equal or agree on all fields but one, so that
    /// [`Componentwise::join`](super::Componentwise::join) joins none of them and
    /// [`Predicate::flatten_or`] returns them as they are.
    ///
    /// Two points join where they differ in at most one field. A field is left out in turn, and
    /// the arms must be distinct on the rest.
    pub(super) fn independent(&self) -> bool {
        let fields = self.names.len();
        if fields < 2 {
            return self.rows.len() < 2;
        }
        (0..fields).all(|left_out| {
            let mut seen: HashSet<Vec<&Value>> = HashSet::with_capacity(self.rows.len());
            self.rows.iter().all(|row| {
                let rest = row
                    .iter()
                    .enumerate()
                    .filter_map(|(at, v)| (at != left_out).then_some(*v))
                    .collect();
                seen.insert(rest)
            })
        })
    }

    /// The positions of the arms of `self` that are, or are not, arms of `other`, or `None` where
    /// the two have different field names.
    pub(super) fn positions_in(&self, other: &PointArms, present: bool) -> Option<Vec<usize>> {
        if self.names != other.names {
            return None;
        }
        let held: HashSet<&[&Value]> = other.rows.iter().map(Vec::as_slice).collect();
        Some(
            (0..self.rows.len())
                .filter(|&at| held.contains(self.rows[at].as_slice()) == present)
                .collect(),
        )
    }
}

/// The one value `predicate` admits, where it admits exactly one.
fn single_value(predicate: &Predicate) -> Option<&Value> {
    let Predicate::Intervals(set) = predicate else {
        return None;
    };
    match set.intervals().as_slice() {
        [one] => match (one.lval(), one.rval()) {
            (Some(least), Some(greatest)) if least == greatest => Some(least),
            _ => None,
        },
        _ => None,
    }
}

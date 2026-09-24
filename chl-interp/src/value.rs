//! The values a program's meaning is stated in.
//!
//! A [`Collection`] is a key-to-value map, and [`PartialEq`] compares its entries as a
//! multiset: its keys are part of its value (a filter keeps its survivors' positions, a
//! group-by is keyed by the group key) and its order is not. A commit time
//! ([`Value::CommitTime`]) compares by its rank, not its number, since `docs/chl-spec.md`, "8.5
//! Ordering and concurrency" orders commits without numbering them.

use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Str(String),
    Bool(bool),
    Unit,
    /// A commit time: the key a reply fed inside a `with begin():` block carries.
    CommitTime(i64),
    Record(Vec<(String, Value)>),
    Variant {
        tag: String,
        payload: Box<Value>,
    },
    Collection(Collection),
}

/// A key-to-value map. Keys are unique; order is not part of the value.
#[derive(Clone, Debug, Default)]
pub struct Collection {
    entries: Vec<(Value, Value)>,
}

impl Collection {
    /// Build from entries in any order.
    ///
    /// # Panics
    ///
    /// When two entries share a key: a collection is a function of its keys, and a caller
    /// holding entries that may repeat one uses [`Self::try_from_entries`].
    pub fn from_entries(entries: Vec<(Value, Value)>) -> Self {
        match Self::try_from_entries(entries) {
            Ok(c) => c,
            Err(key) => panic!("two entries share the key {key}"),
        }
    }

    /// Build from entries in any order, answering the first key two entries share.
    pub fn try_from_entries(entries: Vec<(Value, Value)>) -> Result<Self, Value> {
        let mut keys: Vec<&Value> = entries.iter().map(|(k, _)| k).collect();
        keys.sort_by(|a, b| total_cmp(a, b));
        if let Some(w) = keys.windows(2).find(|w| w[0] == w[1]) {
            return Err(w[0].clone());
        }
        Ok(Self { entries })
    }

    /// The positional form: keys `0..n` in order, which is what a list literal denotes.
    pub fn from_list(values: Vec<Value>) -> Self {
        Self {
            entries: values
                .into_iter()
                .enumerate()
                .map(|(i, v)| (Value::Int(i as i64), v))
                .collect(),
        }
    }

    pub fn entries(&self) -> &[(Value, Value)] {
        &self.entries
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Entries in a canonical order, for comparison and rendering.
    fn sorted(&self) -> Vec<&(Value, Value)> {
        let mut v: Vec<&(Value, Value)> = self.entries.iter().collect();
        v.sort_by(|a, b| total_cmp(&a.0, &b.0).then_with(|| total_cmp(&a.1, &b.1)));
        v
    }
}

impl PartialEq for Collection {
    /// Multiset equality over `(key, value)` pairs: order is not part of the value, and the
    /// key is, with each commit time replaced by its rank (`Collection::ranked_commit_times`).
    fn eq(&self, other: &Self) -> bool {
        let (a, b) = (self.ranked_commit_times(), other.ranked_commit_times());
        a.entries.len() == b.entries.len()
            && a.sorted()
                .iter()
                .zip(b.sorted())
                .all(|(x, y)| x.0 == y.0 && x.1 == y.1)
    }
}

impl Collection {
    /// This collection with every commit time in a key replaced by its rank among the commit
    /// times that share the rest of that key.
    ///
    /// Keys that differ outside their commit time, such as the site tags of a reply channel
    /// fed from two blocks, rank their commit times separately, since only commits of one site are
    /// ordered against each other.
    fn ranked_commit_times(&self) -> Collection {
        fn context(key: &Value) -> Option<Value> {
            match key {
                Value::CommitTime(_) => Some(Value::Unit),
                Value::Variant { tag, payload } => context(payload).map(|c| Value::Variant {
                    tag: tag.clone(),
                    payload: Box::new(c),
                }),
                _ => None,
            }
        }
        fn commit_time(key: &Value) -> Option<i64> {
            match key {
                Value::CommitTime(t) => Some(*t),
                Value::Variant { payload, .. } => commit_time(payload),
                _ => None,
            }
        }
        fn replace(key: &Value, rank: i64) -> Value {
            match key {
                Value::CommitTime(_) => Value::CommitTime(rank),
                Value::Variant { tag, payload } => Value::Variant {
                    tag: tag.clone(),
                    payload: Box::new(replace(payload, rank)),
                },
                other => other.clone(),
            }
        }
        let mut by_context: Vec<(Value, Vec<i64>)> = Vec::new();
        for (key, _) in &self.entries {
            if let (Some(c), Some(t)) = (context(key), commit_time(key)) {
                match by_context.iter_mut().find(|(k, _)| *k == c) {
                    Some((_, times)) => times.push(t),
                    None => by_context.push((c, vec![t])),
                }
            }
        }
        for (_, times) in &mut by_context {
            times.sort_unstable();
        }
        let entries = self
            .entries
            .iter()
            .map(|(key, value)| {
                let key = match (context(key), commit_time(key)) {
                    (Some(c), Some(t)) => {
                        let times = &by_context
                            .iter()
                            .find(|(k, _)| *k == c)
                            .expect("collected")
                            .1;
                        let rank = times.binary_search(&t).expect("collected") as i64;
                        replace(key, rank)
                    }
                    _ => key.clone(),
                };
                (key, value.clone())
            })
            .collect();
        Collection { entries }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Unit, Value::Unit) => true,
            (Value::CommitTime(a), Value::CommitTime(b)) => a == b,
            // A record is its fields; the order they were written in is not part of it.
            (Value::Record(a), Value::Record(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                let (mut a, mut b) = (a.clone(), b.clone());
                a.sort_by(|x, y| x.0.cmp(&y.0));
                b.sort_by(|x, y| x.0.cmp(&y.0));
                a.iter().zip(&b).all(|(x, y)| x.0 == y.0 && x.1 == y.1)
            }
            (
                Value::Variant {
                    tag: t1,
                    payload: p1,
                },
                Value::Variant {
                    tag: t2,
                    payload: p2,
                },
            ) => t1 == t2 && p1 == p2,
            (Value::Collection(a), Value::Collection(b)) => a == b,
            _ => false,
        }
    }
}

/// A total order over values, used only to canonicalize for comparison and rendering.
///
/// [`Collection`]'s equality zips two entry lists sorted by this order, which pairs the
/// entries up when values equal under [`PartialEq`] compare `Equal` here. A record or
/// collection that holds commit times breaks that: it orders by its rendering, which shows
/// raw times, while equality compares their ranks. The zip then pairs mismatched entries and
/// reports a disagreement, never a false agreement.
fn total_cmp(a: &Value, b: &Value) -> Ordering {
    fn rank(v: &Value) -> u8 {
        match v {
            Value::Unit => 0,
            Value::CommitTime(_) => 7,
            Value::Bool(_) => 1,
            Value::Int(_) => 2,
            Value::Str(_) => 3,
            Value::Record(_) => 4,
            Value::Variant { .. } => 5,
            Value::Collection(_) => 6,
        }
    }
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Str(x), Value::Str(y)) => x.cmp(y),
        (Value::Bool(x), Value::Bool(y)) => x.cmp(y),
        (Value::Unit, Value::Unit) => Ordering::Equal,
        (Value::CommitTime(x), Value::CommitTime(y)) => x.cmp(y),
        (
            Value::Variant {
                tag: x,
                payload: px,
            },
            Value::Variant {
                tag: y,
                payload: py,
            },
        ) => x.cmp(y).then_with(|| total_cmp(px, py)),
        // Records and collections order by rendering: a stable tie-break, never a claim
        // about their contents.
        (x, y) if rank(x) == rank(y) => x.to_string().cmp(&y.to_string()),
        (x, y) => rank(x).cmp(&rank(y)),
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::Str(s) => write!(f, "{s:?}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Unit => write!(f, "()"),
            Value::CommitTime(t) => write!(f, "t{t}"),
            Value::Record(fields) => {
                let mut sorted = fields.clone();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                let body: Vec<String> = sorted.iter().map(|(n, v)| format!("{n}: {v}")).collect();
                write!(f, "({})", body.join(", "))
            }
            Value::Variant { tag, payload } => write!(f, "`{tag}({payload})"),
            Value::Collection(c) => {
                let dense = c
                    .sorted()
                    .iter()
                    .enumerate()
                    .all(|(i, (k, _))| matches!(k, Value::Int(n) if *n == i as i64));
                let body: Vec<String> = c
                    .sorted()
                    .iter()
                    .map(|(k, v)| {
                        if dense {
                            format!("{v}")
                        } else {
                            format!("{k} -> {v}")
                        }
                    })
                    .collect();
                write!(f, "[{}]", body.join(", "))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(key: Value, v: i64) -> (Value, Value) {
        (key, Value::Int(v))
    }

    fn site(tag: &str, t: i64) -> Value {
        Value::Variant {
            tag: tag.to_string(),
            payload: Box::new(Value::CommitTime(t)),
        }
    }

    /// Only the order of commit times is compared, per site.
    #[test]
    fn commit_times_compare_by_their_order_within_each_site() {
        let a = Collection::from_entries(vec![
            at(site("0", 1), 10),
            at(site("0", 2), 30),
            at(site("1", 1), 5),
        ]);
        let b = Collection::from_entries(vec![
            at(site("0", 3), 10),
            at(site("0", 7), 30),
            at(site("1", 4), 5),
        ]);
        assert_eq!(a, b);
        let swapped = Collection::from_entries(vec![
            at(site("0", 3), 30),
            at(site("0", 7), 10),
            at(site("1", 4), 5),
        ]);
        assert_ne!(a, swapped);
    }
}

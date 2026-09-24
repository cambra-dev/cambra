//! The value domain: what a CHL program means, with none of the apparatus that makes it
//! computable incrementally.
//!
//! A [`Collection`] is a key-to-value map, because that is what a CHL collection is — the
//! keys carry information (a filter keeps the positions its survivors had, a group-by is
//! keyed by the group key), so dropping them would make two different answers compare equal.
//! Order, by contrast, carries nothing: [`PartialEq`] compares entries as a multiset.

use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Str(String),
    Bool(bool),
    Unit,
    Record(Vec<(String, Value)>),
    Variant { tag: String, payload: Box<Value> },
    Collection(Collection),
}

/// A key-to-value map. Keys are unique; order is not part of the value.
#[derive(Clone, Debug, Default)]
pub struct Collection {
    entries: Vec<(Value, Value)>,
}

impl Collection {
    pub fn new() -> Self {
        Self::default()
    }

    /// Build from entries in any order. A repeated key is a caller error, not a merge.
    pub fn from_entries(entries: Vec<(Value, Value)>) -> Self {
        Self { entries }
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

    pub fn push(&mut self, key: Value, value: Value) {
        self.entries.push((key, value));
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
    /// key is.
    fn eq(&self, other: &Self) -> bool {
        self.entries.len() == other.entries.len()
            && self
                .sorted()
                .iter()
                .zip(other.sorted())
                .all(|(a, b)| a.0 == b.0 && a.1 == b.1)
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Unit, Value::Unit) => true,
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
/// Values of different shapes never compare equal, so ordering them by shape first is
/// enough; nothing reads the order itself.
fn total_cmp(a: &Value, b: &Value) -> Ordering {
    fn rank(v: &Value) -> u8 {
        match v {
            Value::Unit => 0,
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
        (Value::Variant { tag: x, .. }, Value::Variant { tag: y, .. }) => x.cmp(y),
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
            Value::Record(fields) => {
                let mut sorted = fields.clone();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                let body: Vec<String> = sorted.iter().map(|(n, v)| format!("{n}: {v}")).collect();
                write!(f, "{{{}}}", body.join(", "))
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

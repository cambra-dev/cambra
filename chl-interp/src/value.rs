//! The values a program's meaning is stated in.
//!
//! A [`Collection`] is a key-to-value map, and [`PartialEq`] compares its entries as a
//! multiset: its keys are part of its value (a filter keeps its survivors' positions, a
//! group-by is keyed by the group key) and its order is not.

use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Str(String),
    Bool(bool),
    Unit,
    Record(Vec<(String, Value)>),
    Variant {
        tag: String,
        payload: Box<Value>,
    },
    /// A value of a nominal type: the type a `type` declaration names, the constructor that
    /// built it, and the constructor's argument (`docs/chl-spec.md`, "Declaring a nominal
    /// type"). The type is part of the value, so two declarations' constructors of one name
    /// build different values, and a variant's tag never matches a constructor.
    Nominal {
        ty: String,
        ctor: String,
        payload: Box<Value>,
    },
    Collection(Collection),
    /// A value that depends on a channel whose contents are not complete yet, on a pass of
    /// evaluation before the one [`crate::run`] answers from (see [`crate::eval`]). It
    /// absorbs: every value computed from it is pending, so no other value holds one.
    Pending,
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
    /// key is.
    fn eq(&self, other: &Self) -> bool {
        self.entries.len() == other.entries.len()
            && self
                .sorted()
                .iter()
                .zip(other.sorted())
                .all(|(x, y)| x.0 == y.0 && x.1 == y.1)
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
            (
                Value::Nominal {
                    ty: n1,
                    ctor: c1,
                    payload: p1,
                },
                Value::Nominal {
                    ty: n2,
                    ctor: c2,
                    payload: p2,
                },
            ) => n1 == n2 && c1 == c2 && p1 == p2,
            (Value::Collection(a), Value::Collection(b)) => a == b,
            _ => false,
        }
    }
}

/// A total order over values, used only to canonicalize for comparison and rendering.
///
/// [`Collection`]'s equality zips two entry lists sorted by this order, which pairs the
/// entries up when values equal under [`PartialEq`] compare `Equal` here.
fn total_cmp(a: &Value, b: &Value) -> Ordering {
    fn rank(v: &Value) -> u8 {
        match v {
            Value::Unit => 0,
            Value::Bool(_) => 1,
            Value::Int(_) => 2,
            Value::Str(_) => 3,
            Value::Record(_) => 4,
            Value::Variant { .. } => 5,
            Value::Nominal { .. } => 8,
            Value::Collection(_) => 6,
            Value::Pending => 7,
        }
    }
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Str(x), Value::Str(y)) => x.cmp(y),
        (Value::Bool(x), Value::Bool(y)) => x.cmp(y),
        (Value::Unit, Value::Unit) => Ordering::Equal,
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
        (
            Value::Nominal {
                ty: tx,
                ctor: x,
                payload: px,
            },
            Value::Nominal {
                ty: ty_,
                ctor: y,
                payload: py,
            },
        ) => tx
            .cmp(ty_)
            .then_with(|| x.cmp(y))
            .then_with(|| total_cmp(px, py)),
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
            Value::Pending => write!(f, "?"),
            Value::Record(fields) => {
                let mut sorted = fields.clone();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                let body: Vec<String> = sorted.iter().map(|(n, v)| format!("{n}: {v}")).collect();
                write!(f, "({})", body.join(", "))
            }
            Value::Variant { tag, payload } => write!(f, "`{tag}({payload})"),
            Value::Nominal { ty, ctor, payload } => write!(f, "{ty}::{ctor}({payload})"),
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

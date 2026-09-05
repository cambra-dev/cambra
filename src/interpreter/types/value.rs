//! Scalar values produced during interpretation: [`Value`] and the
//! [`FunctionDef`] descriptor for built-in computable functions.

use std::{cmp::Ordering, collections::HashMap, hash::Hash};

use intervalsets::Side;
use intervalsets::numeric::Domain;
use smol_str::SmolStr;

use crate::ccl::FieldKey;
use crate::interpreter::{
    BinOpKind, UnaryOpKind, apply_binop_column, apply_unaryop_column, tuple_field,
};
use crate::pretty_graph::fmt_binop;
use crate::util::fmt_record;

use super::{ColumnValue, FuncBinding, bindings_are_list};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionDef {
    BinOp(BinOpKind),
    /// Unary arithmetic or boolean operation applied element-wise to a single column.
    UnaryOp(UnaryOpKind),
    RecordField(String),
    /// `insert(m, k, v)` — the collection with one key's value replaced, inserting the key
    /// where it was absent. Applied to a `Records` column of the tupled argument
    /// ([`crate::ccl::Builtin::Insert`]), pointwise: one map in, one map out.
    Insert,
}

impl FunctionDef {
    pub fn apply(&self, input: ColumnValue) -> ColumnValue {
        match (self, input) {
            (FunctionDef::BinOp(op), ColumnValue::Records(mut fields)) => apply_binop_column(
                *op,
                fields.remove(&tuple_field(0)).expect("Not a tuple"),
                &fields[&tuple_field(1)],
            ),
            (FunctionDef::UnaryOp(op), cv) => apply_unaryop_column(*op, cv),
            (FunctionDef::RecordField(f), ColumnValue::Records(mut fields)) => fields
                .remove(f)
                .unwrap_or_else(|| panic!("Missing field {f}")),
            (FunctionDef::Insert, ColumnValue::Records(mut fields)) => {
                let maps = fields
                    .remove(&tuple_field(0))
                    .expect("insert: no collection");
                let keys = fields.remove(&tuple_field(1)).expect("insert: no key");
                let values = fields.remove(&tuple_field(2)).expect("insert: no value");
                ColumnValue::Variants(
                    (0..maps.len())
                        .map(|i| {
                            insert_binding(maps.index_at(i), keys.index_at(i), values.index_at(i))
                        })
                        .collect(),
                )
            }
            _ => panic!("Invalid function application"),
        }
    }
}

/// `m` with `key` bound to `value` — replacing an existing binding, appending a new one.
///
/// A map value is a [`Value::Function`] binding list, so a key is present at most once and
/// replacement is positional. A non-function `m` is a shape error the type system rules out.
fn insert_binding(m: Value, key: Value, value: Value) -> Value {
    let Value::Function(mut bindings) = m else {
        panic!("insert: the collection operand is not a function value, got {m:?}");
    };
    match bindings.iter_mut().find(|b| b.input == key) {
        Some(b) => b.output = value,
        None => bindings.push(FuncBinding {
            input: key,
            output: value,
        }),
    }
    Value::Function(bindings)
}

impl std::fmt::Display for FunctionDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionDef::UnaryOp(op) => write!(f, "UnaryOp({op:?})"),
            FunctionDef::BinOp(op) => write!(f, "BinOp({})", fmt_binop(op)),
            FunctionDef::RecordField(field) => write!(f, ".{field}"),
            FunctionDef::Insert => write!(f, "insert"),
        }
    }
}

/// Values in CCL
#[derive(Clone, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    UInt(usize),
    String(SmolStr),
    Bool(bool),
    Unit,
    /// A function value (collection of bindings)
    Function(Vec<FuncBinding>),
    /// A record value
    Record(HashMap<String, Value>),
    ComputableFunction(FunctionDef),
    /// A tagged union value: `tag` names which arm, `inner` is the payload.
    ///
    /// The tag is a [`FieldKey`], not a position, so a union value is
    /// **self-describing**: its meaning does not depend on a static type that is
    /// not attached to it. A positional tag makes equality, hashing and any
    /// serialization of a union value only meaningful within one static type,
    /// because the same position denotes different arms in a type and its
    /// width-supertype.
    Union {
        tag: FieldKey,
        inner: Box<Value>,
    },
}

impl Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Value::Int(i) => i.hash(state),
            Value::UInt(i) => i.hash(state),
            Value::String(s) => s.hash(state),
            Value::Bool(b) => b.hash(state),
            Value::Unit => {}
            Value::Function(bindings) => bindings.hash(state),
            Value::Record(fields) => {
                fields.len().hash(state);
                let mut entries: Vec<_> = fields.iter().collect();
                entries.sort_by_key(|(k, _)| *k);
                for (k, v) in entries {
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::ComputableFunction(f) => f.hash(state),
            Value::Union { tag, inner } => {
                tag.hash(state);
                inner.hash(state);
            }
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            Value::Int(i) => {
                if let Value::Int(o) = other {
                    i.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::UInt(i) => {
                if let Value::UInt(o) = other {
                    i.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::String(s) => {
                if let Value::String(o) = other {
                    s.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::Bool(b) => {
                if let Value::Bool(o) = other {
                    b.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::Unit => {
                if let Value::Unit = other {
                    Some(Ordering::Equal)
                } else {
                    None
                }
            }
            // Order records lexicographically if they have the same schema.
            Value::Record(fields) => {
                if let Value::Record(o_fields) = other {
                    if fields.keys().collect::<std::collections::HashSet<_>>()
                        != o_fields.keys().collect::<std::collections::HashSet<_>>()
                    {
                        return None; // Records with different keys are not comparable
                    }
                    let mut entries: Vec<_> = fields.iter().collect();
                    let mut o_entries: Vec<_> = o_fields.iter().collect();
                    entries.sort_by_key(|(k, _)| *k);
                    o_entries.sort_by_key(|(k, _)| *k);
                    entries.partial_cmp(&o_entries)
                } else {
                    None
                }
            }
            Value::Union { tag, inner } => {
                if let Value::Union {
                    tag: o_tag,
                    inner: o_inner,
                } = other
                {
                    tag.partial_cmp(o_tag).and_then(|o| {
                        if o.is_eq() {
                            inner.partial_cmp(o_inner)
                        } else {
                            Some(o)
                        }
                    })
                } else {
                    None
                }
            }
            _ => todo!("Ordering not implemented yet: {self:?}"),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::UInt(i) => write!(f, "u{i}"),
            Value::String(s) => write!(f, "\"{s}\""),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Unit => write!(f, "()"),
            Value::Function(bindings) => {
                // If inputs are exactly u0..uN, omit them for readability.
                let is_list = bindings_are_list(bindings);
                let binding_strs: Vec<String> = bindings
                    .iter()
                    .map(|b| {
                        if is_list {
                            format!("{}", b.output)
                        } else {
                            format!("{} -> {}", b.input, b.output)
                        }
                    })
                    .collect();
                write!(f, "Function [ {} ]", binding_strs.join(", "))
            }
            Value::Record(fields) => fmt_record(f, fields),
            Value::ComputableFunction(fun) => write!(f, "{fun}"),
            // A variant value is what a constructor produced, so it renders as
            // that constructor: `` `tag(payload) ``. The nullary one shows its
            // payload too (`` `abort(()) ``, `Unit`'s own rendering) — a value
            // always has one, unlike an arm's *type*, where storing nothing is
            // the whole content and the arm is written bare.
            Value::Union { tag, inner } => write!(f, "`{tag}({inner})"),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Domain for Value {
    /// Finds the next smaller or larger element, or None if no such element exists
    /// (like <0 for usize, or anything for strings and floats).
    fn try_adjacent(&self, side: Side) -> Option<Self> {
        match (self, side) {
            (Value::Bool(false), Side::Left) => None,
            (Value::Bool(true), Side::Left) => Some(Value::from(false)),
            (Value::Bool(false), Side::Right) => Some(Value::from(true)),
            (Value::Bool(true), Side::Right) => None,
            (Value::Int(i), Side::Left) => i.checked_sub(1).map(Value::from),
            (Value::Int(i), Side::Right) => i.checked_add(1).map(Value::from),
            (Value::UInt(i), Side::Left) => i.checked_sub(1).map(Value::from),
            (Value::UInt(i), Side::Right) => i.checked_add(1).map(Value::from),
            _ => None,
        }
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        Value::Int(v)
    }
}

impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Value::UInt(v)
    }
}

impl From<SmolStr> for Value {
    fn from(v: SmolStr) -> Self {
        Value::String(v)
    }
}

impl From<bool> for Value {
    fn from(v: bool) -> Self {
        Value::Bool(v)
    }
}

impl Value {
    pub fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            _ => panic!("Not bool: {self:?}"),
        }
    }

    pub fn as_int(&self) -> i64 {
        match self {
            Value::Int(i) => *i,
            _ => panic!("Not int: {self:?}"),
        }
    }

    pub fn as_uint(&self) -> usize {
        match self {
            Value::UInt(i) => *i,
            _ => panic!("Not uint: {self:?}"),
        }
    }

    pub fn as_string(&self) -> &SmolStr {
        match self {
            Value::String(s) => s,
            _ => panic!("Not string: {self:?}"),
        }
    }

    pub fn as_function(&self) -> &Vec<FuncBinding> {
        match self {
            Value::Function(v) => v,
            _ => panic!("Not function: {self:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    // --- Display tests ---

    #[test]
    fn test_value_display_primitives() {
        assert_eq!(Value::Int(42).to_string(), "42");
        assert_eq!(Value::Int(-7).to_string(), "-7");
        assert_eq!(Value::UInt(3).to_string(), "u3");
        assert_eq!(Value::String("hello".into()).to_string(), "\"hello\"");
        assert_eq!(Value::Bool(true).to_string(), "true");
        assert_eq!(Value::Bool(false).to_string(), "false");
        assert_eq!(Value::Unit.to_string(), "()");
    }

    /// A variant value renders as the constructor that produced it, so a value
    /// read out of a tile and the term that built it read the same. The nullary
    /// constructor still shows its payload — a *value* always has one.
    #[test]
    fn test_value_display_union_is_the_constructor() {
        assert_eq!(
            Value::Union {
                tag: FieldKey::Name("commit".into()),
                inner: Box::new(Value::Int(7)),
            }
            .to_string(),
            "`commit(7)"
        );
        assert_eq!(
            Value::Union {
                tag: FieldKey::Name("abort".into()),
                inner: Box::new(Value::Unit),
            }
            .to_string(),
            "`abort(())"
        );
    }

    #[test]
    fn test_value_display_function_positional() {
        // Inputs are u0, u1, u2 — should be omitted.
        let f = Value::Function(vec![
            FuncBinding {
                input: Value::UInt(0),
                output: Value::String("a".into()),
            },
            FuncBinding {
                input: Value::UInt(1),
                output: Value::String("b".into()),
            },
        ]);
        assert_eq!(f.to_string(), r#"Function [ "a", "b" ]"#);
    }

    #[test]
    fn test_value_display_function_non_positional() {
        // Inputs are not u0..uN — should be shown explicitly.
        let f = Value::Function(vec![
            FuncBinding {
                input: Value::String("x".into()),
                output: Value::Int(1),
            },
            FuncBinding {
                input: Value::String("y".into()),
                output: Value::Int(2),
            },
        ]);
        assert_eq!(f.to_string(), r#"Function [ "x" -> 1, "y" -> 2 ]"#);
    }

    #[test]
    fn test_value_display_function_gap_in_indices() {
        // u0, u2 — not contiguous, so inputs should be shown.
        let f = Value::Function(vec![
            FuncBinding {
                input: Value::UInt(0),
                output: Value::Int(10),
            },
            FuncBinding {
                input: Value::UInt(2),
                output: Value::Int(20),
            },
        ]);
        assert_eq!(f.to_string(), "Function [ u0 -> 10, u2 -> 20 ]");
    }

    #[test]
    fn test_value_display_record() {
        let mut fields = HashMap::new();
        fields.insert("x".to_string(), Value::Int(1));
        let r = Value::Record(fields);
        assert_eq!(r.to_string(), "{x: 1}");
    }
}

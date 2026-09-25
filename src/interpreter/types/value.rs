//! Scalar values produced during interpretation: [`Value`] and the
//! [`FunctionDef`] descriptor for built-in computable functions.

use std::{cmp::Ordering, collections::HashMap, hash::Hash};

use intervalsets::Side;
use intervalsets::numeric::Domain;
use smol_str::SmolStr;

use crate::ccl::FieldKey;
use crate::interpreter::{
    BinOpKind, Extent, Tile, UnaryOpKind, apply_binop_column, apply_unaryop_column, tuple_field,
};
use crate::pretty_graph::fmt_binop;
use crate::util::fmt_record;

use super::{ColumnValue, FuncBinding, bindings_are_list};
use crate::interpreter::tile_operators::{materialize_collections, open_collections};

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

    /// Apply this function to an argument **tile**, for an argument carrying a collection as
    /// a level — which a column has nowhere to put, so [`Self::apply`] cannot be handed one.
    /// `argument_extent` is the argument's extent, which types the written values.
    ///
    /// Only [`Self::Insert`] has a level-shaped argument: a keyed write's collection operand
    /// reaches it opened when the store read that produced it was. The rest read columns,
    /// and a level arriving at one is a defect rather than a case to cover.
    pub fn apply_tile(&self, input: Tile, argument_extent: &Extent) -> Tile {
        let FunctionDef::Insert = self else {
            panic!("{self} takes a column argument; a level reaching it is a shape error")
        };
        let Tile::Record(mut fields) = input else {
            panic!("insert takes the tupled `(collection, key, value)`, got {input:?}")
        };
        let Some(Extent::Function {
            codomain: value_extent,
            ..
        }) = argument_extent
            .record_fields()
            .and_then(|f| f.get(&tuple_field(0)))
        else {
            panic!("insert's argument is `(collection, key, value)`, got {argument_extent}")
        };
        let collection = fields
            .remove(&tuple_field(0))
            .expect("insert: no collection");
        let Tile::DataFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
            ..
        } = &collection
        else {
            panic!("FunctionDef::apply_tile is for a collection operand that is a level")
        };
        // The key and value are one value per row, which a product spreads over a record of
        // columns. The key is read as one column, and the value is reopened into the shape
        // the collection's values take, at whatever depth that is.
        let new_keys =
            materialize_collections(fields.remove(&tuple_field(1)).expect("insert: no key"));
        let new_values = open_collections(
            &materialize_collections(fields.remove(&tuple_field(2)).expect("insert: no value")),
            value_extent,
        );
        let rows = collection.rows();
        assert_eq!(
            new_keys.len(),
            rows,
            "insert writes one key in each row of the collection it is handed"
        );
        // Rebuild each row's group with its key written: replacing the binding where the row
        // already holds that key, appending it where it does not. A removed key is dropped
        // rather than carried, since the group a write lands in is the live one. Every entry
        // is gathered from the collection's entries followed by the written ones, so entry
        // `i < written` is the collection's and `written + r` is row `r`'s write.
        let written = domain.len();
        let mut starts = Vec::with_capacity(rows);
        let mut key_entries = Vec::with_capacity(written + rows);
        let mut value_entries = Vec::with_capacity(written + rows);
        for (r, (from, to)) in collection.row_runs().enumerate() {
            starts.push(key_entries.len());
            let key = new_keys.index_at(r);
            let mut hit = false;
            for i in (from..to).filter(|i| !deleted.contains(*i)) {
                let is_key = domain.index_at(i) == key;
                hit |= is_key;
                key_entries.push(i);
                value_entries.push(if is_key { written + r } else { i });
            }
            if !hit {
                key_entries.push(written + r);
                value_entries.push(written + r);
            }
        }
        let mut keys = domain.clone();
        keys.append(new_keys);
        let mut values = (**codomain).clone();
        values.merge_rows(new_values);
        Tile::grouped(
            ColumnValue::UInts(starts),
            keys.select_indices(key_entries.iter().copied(), key_entries.len()),
            Box::new(values.select_rows(&value_entries)),
            domain_predicate.clone(),
            bit_set::BitSet::new(),
        )
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
    use crate::interpreter::BaseType;
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

    // --- insert over a level ---

    /// The extent of `insert`'s `(collection, key, value)` argument over `Map(String, value)`.
    fn insert_argument(value: Extent) -> Extent {
        Extent::Record(HashMap::from([
            (
                tuple_field(0),
                Extent::Function {
                    domain: Box::new(Extent::Base(BaseType::String)),
                    codomain: Box::new(value.clone()),
                },
            ),
            (tuple_field(1), Extent::Base(BaseType::String)),
            (tuple_field(2), value),
        ]))
    }

    /// A list level of `Int`s: one row per group in `groups`.
    fn int_lists(groups: &[&[i64]]) -> Tile {
        let mut starts = Vec::new();
        let mut positions = Vec::new();
        let mut elements = Vec::new();
        for group in groups {
            starts.push(positions.len());
            positions.extend(0..group.len());
            elements.extend(group.iter().copied());
        }
        Tile::grouped(
            ColumnValue::UInts(starts),
            ColumnValue::UInts(positions),
            Box::new(Tile::Scalar(ColumnValue::Ints(elements))),
            crate::interpreter::Predicate::True,
            bit_set::BitSet::new(),
        )
    }

    /// `insert` over a collection whose values are themselves a level, `Map(String,
    /// List(Int))`: the written list replaces the row's list at a held key and is appended at
    /// a new one, and the lists below stay a level rather than a column of maps.
    #[test]
    fn apply_tile_writes_a_collection_valued_key() {
        // Row 0 is `{a: [1, 2]}`, row 1 is `{a: [3]}`.
        let level = Tile::grouped(
            ColumnValue::from_uints(vec![0, 1]),
            ColumnValue::Strings(vec!["a".into(), "a".into()]),
            Box::new(int_lists(&[&[1, 2], &[3]])),
            crate::interpreter::Predicate::True,
            bit_set::BitSet::new(),
        );
        let argument = Tile::Record(HashMap::from([
            (tuple_field(0), level),
            // Row 0 writes `a := [7]`, which it holds; row 1 writes `b := [8, 9]`, which it
            // does not.
            (
                tuple_field(1),
                Tile::Scalar(ColumnValue::Strings(vec!["a".into(), "b".into()])),
            ),
            (tuple_field(2), int_lists(&[&[7], &[8, 9]])),
        ]));
        let list = Extent::Function {
            domain: Box::new(Extent::Base(BaseType::UInt)),
            codomain: Box::new(Extent::Base(BaseType::Int)),
        };
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            ..
        } = FunctionDef::Insert.apply_tile(argument, &insert_argument(list))
        else {
            panic!("insert over a level yields a level")
        };
        assert_eq!(row_starts, ColumnValue::from_uints(vec![0, 1]));
        assert_eq!(
            domain,
            ColumnValue::Strings(vec!["a".into(), "a".into(), "b".into()])
        );
        assert_eq!(*codomain, int_lists(&[&[7], &[3], &[8, 9]]));
    }

    /// `insert(m, k, v)` over a collection carried as a **level**: each row's group gets
    /// `k` written, replacing the binding the row already holds and appending it where the
    /// row lacks one. The two rows differ in both, which is what pins the per-row fold.
    #[test]
    fn apply_tile_writes_its_key_in_every_row() {
        let level = Tile::grouped(
            ColumnValue::from_uints(vec![0, 2]),
            ColumnValue::Strings(vec!["a".into(), "b".into(), "a".into()]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            crate::interpreter::Predicate::True,
            bit_set::BitSet::new(),
        );
        let argument = Tile::Record(HashMap::from([
            (tuple_field(0), level),
            // Row 0 writes `b`, which it holds; row 1 writes `c`, which it does not.
            (
                tuple_field(1),
                Tile::Scalar(ColumnValue::Strings(vec!["b".into(), "c".into()])),
            ),
            (
                tuple_field(2),
                Tile::Scalar(ColumnValue::Ints(vec![20, 30])),
            ),
        ]));
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            ..
        } = FunctionDef::Insert.apply_tile(argument, &insert_argument(Extent::Base(BaseType::Int)))
        else {
            panic!("insert over a level yields a level")
        };
        assert_eq!(row_starts, ColumnValue::from_uints(vec![0, 2]));
        assert_eq!(
            domain,
            ColumnValue::Strings(vec!["a".into(), "b".into(), "a".into(), "c".into()])
        );
        assert_eq!(
            *codomain,
            Tile::Scalar(ColumnValue::Ints(vec![1, 20, 3, 30]))
        );
    }
}

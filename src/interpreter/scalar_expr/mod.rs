//! Recognize element-wise chains and evaluate them as [`FunctionDef::Scalar`](super::FunctionDef).
//!
//! A [`ScalarProgram`] is a straight-line sequence of instructions. [`fuse_prefix`] builds one from
//! a chain, and [`ScalarProgram::eval`] applies it to a column. A conditional in a program is a
//! `Case` instruction applying a [`CaseFn`].
//!
//! The program format and evaluation rules are in `src/interpreter/design-operators.md`, "Scalar
//! programs". Conversion eligibility is in `src/ccl/design/optimization.md`, "Element-wise chains".

mod case;
mod eval;
mod parse;
mod split;
#[cfg(test)]
mod tests;

pub use parse::fuse_prefix;

use smol_str::SmolStr;

use crate::ccl::FieldKey;

use super::{BaseType, BinOpKind as InterpreterBinOp, Extent, UnaryOpKind, Value};
use case::{CaseFn, CaseGate, PAYLOAD, Shape};

/// The index of an instruction, which is also the slot it writes.
type Slot = u32;

/// One instruction of a [`ScalarProgram`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Instr {
    /// The column at `path` inside the map's input value; an empty path is the value itself. In a
    /// conditional's arm the input is its captures, so the column may be anything a capture holds.
    /// A column other than of `Int`, `UInt`, `String` or `Bool` has no view, so no operation reads
    /// one ([`ScalarProgram::operands_have_views`]), and a constructor copies its rows.
    Input {
        path: Vec<SmolStr>,
    },
    /// One value of a base type at every row. A `Unit` constant has no view, so no operation
    /// reads one ([`ScalarProgram::operands_have_views`]).
    Const(Value),
    Bin(InterpreterBinOp, Slot, Slot),
    Un(UnaryOpKind, Slot),
    /// A column of records, one field per slot named, sorted by field name. A tuple's fields are
    /// `_0`, `_1`, …, which sort as strings: `_10` before `_2`.
    ///
    /// A constructor: no operation reads it, and it is the last instruction or a field or payload
    /// of a later constructor ([`ScalarProgram::constructors_build_only_the_result`]).
    Record(Vec<(SmolStr, Slot)>),
    /// A union column whose every row carries `tag`, with the payload in `payload`. The column
    /// holds only that arm, since an absent arm reads as an empty one
    /// ([`ColumnValue::Union`](super::ColumnValue::Union)).
    ///
    /// A constructor, as [`Instr::Record`] is.
    Wrap {
        tag: FieldKey,
        payload: Slot,
    },
    /// A conditional ([`CaseFn`]) applied to the record of `captures`, one field per slot named,
    /// which its arms read. A `Case` that `constructs` yields a record, a union or `Unit` and is a
    /// constructor, as [`Instr::Record`] is; one that does not yields a column with a view and
    /// writes a scratch column. A capture is read as a `Record`'s field is. `shape` is the empty
    /// column of its result's type, which evaluating the arms on no rows would build at a cost
    /// that doubles with each conditional nested in an arm.
    Case {
        case: Box<CaseFn>,
        captures: Vec<(SmolStr, Slot)>,
        constructs: bool,
        shape: Shape,
    },
}

impl Instr {
    /// Whether this instruction builds part of the result: a [`Instr::Record`], a [`Instr::Wrap`],
    /// or a [`Instr::Case`] that constructs.
    fn is_constructor(&self) -> bool {
        matches!(
            self,
            Instr::Record(_)
                | Instr::Wrap { .. }
                | Instr::Case {
                    constructs: true,
                    ..
                }
        )
    }
}

/// A straight-line program whose operands refer to earlier instruction slots.
///
/// The last instruction produces the result. Structural equality compares instruction sequences;
/// it does not establish equivalence between different expressions for the same function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScalarProgram {
    instrs: Vec<Instr>,
}

impl ScalarProgram {
    /// The input fields this program reads, other than [`PAYLOAD`]: the first segment of each
    /// input path, once each.
    pub(crate) fn input_fields(&self) -> Vec<SmolStr> {
        let mut fields: Vec<SmolStr> = Vec::new();
        for instr in &self.instrs {
            if let Instr::Input { path } = instr
                && let Some(first) = path.first()
                && first != PAYLOAD
                && !fields.contains(first)
            {
                fields.push(first.clone());
            }
        }
        fields
    }

    /// Check that constructors are used only to build the result, never as operation operands:
    /// each is the last instruction or a field, payload or capture of a later constructor or
    /// `Case`. The last instruction must be an operation or a constructor, not a borrowed input or
    /// constant. The programs of a `Case`'s arms are checked the same way, except that an arm's
    /// body may answer with an input or a constant.
    fn constructors_build_only_the_result(&self) -> bool {
        let last = self.instrs.len() - 1;
        !matches!(self.instrs[last], Instr::Input { .. } | Instr::Const(_))
            && self.constructors_are_placed()
    }

    /// [`ScalarProgram::constructors_build_only_the_result`] without the condition on the last
    /// instruction, for this program and the programs of its `Case`s.
    fn constructors_are_placed(&self) -> bool {
        let is_constructor = |slot: &Slot| self.instrs[*slot as usize].is_constructor();
        let last = self.instrs.len() - 1;
        let arms_are_placed = self.instrs.iter().all(|instr| match instr {
            Instr::Case { case, .. } => case.arms.iter().all(|arm| {
                arm.body.constructors_are_placed()
                    && match &arm.gate {
                        CaseGate::Holds { program, .. } => program.constructors_are_placed(),
                        CaseGate::Rest | CaseGate::Tag { .. } => true,
                    }
            }),
            _ => true,
        });
        let builds = |later: &Instr, slot: usize| match later {
            Instr::Record(fields)
            | Instr::Case {
                captures: fields, ..
            } => fields.iter().any(|(_, field)| *field as usize == slot),
            Instr::Wrap { payload, .. } => *payload as usize == slot,
            _ => false,
        };
        arms_are_placed
            && self
                .instrs
                .iter()
                .enumerate()
                .all(|(slot, instr)| match instr {
                    Instr::Bin(_, a, b) => !is_constructor(a) && !is_constructor(b),
                    Instr::Un(_, a) => !is_constructor(a),
                    instr if instr.is_constructor() => {
                        slot == last
                            || self.instrs[slot + 1..]
                                .iter()
                                .any(|later| builds(later, slot))
                    }
                    _ => true,
                })
    }

    /// Check that every operand of an operation has a view, for a program applied to values of
    /// `input`. An operand has a view when it is an operation, or an input or constant whose
    /// extent has one ([`has_view`]). A constructor, a `Unit` constant, and a `Unit` or union input
    /// have none.
    fn operands_have_views(&self, input: &Extent) -> bool {
        let has_a_view = |slot: &Slot| match &self.instrs[*slot as usize] {
            Instr::Input { path } => path
                .iter()
                .try_fold(input, |extent, name| extent.record_fields()?.get(name))
                .is_some_and(has_view),
            Instr::Const(value) => value_extent(value).as_ref().is_some_and(has_view),
            Instr::Bin(..)
            | Instr::Un(..)
            | Instr::Case {
                constructs: false, ..
            } => true,
            Instr::Record(_) | Instr::Wrap { .. } | Instr::Case { .. } => false,
        };
        self.instrs.iter().all(|instr| match instr {
            Instr::Bin(_, a, b) => has_a_view(a) && has_a_view(b),
            Instr::Un(_, a) => has_a_view(a),
            _ => true,
        })
    }
}

impl std::fmt::Display for Instr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instr::Input { path } if path.is_empty() => write!(f, "_"),
            Instr::Input { path } => write!(f, "_.{}", path.join(".")),
            Instr::Const(value) => write!(f, "{value}"),
            Instr::Un(op, a) => write!(f, "{op:?}(s{a})"),
            Instr::Bin(op, a, b) => {
                write!(f, "{}(s{a}, s{b})", crate::pretty_graph::fmt_binop(op))
            }
            Instr::Record(fields) => {
                write!(f, "(")?;
                for (i, (name, field)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: s{field}")?;
                }
                write!(f, ")")
            }
            Instr::Wrap { tag, payload } => write!(f, "`{tag}(s{payload})"),
            Instr::Case { case, captures, .. } => {
                write!(f, "case(")?;
                for (i, (name, capture)) in captures.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: s{capture}")?;
                }
                write!(f, ") {{ ")?;
                for arm in &case.arms {
                    match &arm.gate {
                        CaseGate::Holds { program, .. } => write!(f, "[{program}] -> ")?,
                        CaseGate::Rest => write!(f, "else -> ")?,
                        CaseGate::Tag { scrutinee, tag, .. } => {
                            write!(f, "{scrutinee} is `{tag} -> ")?
                        }
                    }
                    write!(f, "[{}]; ", arm.body)?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl std::fmt::Display for ScalarProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (slot, instr) in self.instrs.iter().enumerate() {
            write!(f, "s{slot} = {instr}; ")?;
        }
        write!(f, "=> s{}", self.instrs.len() - 1)
    }
}

/// A fused chain: the program, the extents it is applied between, and how many of the
/// chain's elements it replaces.
pub struct Fused {
    pub program: ScalarProgram,
    pub domain: Extent,
    pub codomain: Extent,
    pub consumed: usize,
}

/// The extent of a closed value, read from the value: a base value or a record of them. A variant
/// names only its own arm, so it has no extent here.
fn value_extent(value: &Value) -> Option<Extent> {
    Some(match value {
        Value::Unit => Extent::Base(BaseType::Unit),
        Value::Int(_) => Extent::Base(BaseType::Int),
        Value::UInt(_) => Extent::Base(BaseType::UInt),
        Value::String(_) => Extent::Base(BaseType::String),
        Value::Bool(_) => Extent::Base(BaseType::Bool),
        Value::Record(fields) => Extent::Record(
            fields
                .iter()
                .map(|(name, v)| Some((name.clone(), value_extent(v)?)))
                .collect::<Option<_>>()?,
        ),
        _ => return None,
    })
}

/// Whether a column of `extent` has a [`ColumnView`](super::ColumnView): a base type other than
/// `Unit`, whose column stores no values.
fn has_view(extent: &Extent) -> bool {
    matches!(extent, Extent::Base(base) if *base != BaseType::Unit)
}
